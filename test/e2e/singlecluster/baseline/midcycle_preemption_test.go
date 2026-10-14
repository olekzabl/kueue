/*
Copyright The Kubernetes Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

package baseline

import (
	"github.com/onsi/ginkgo/v2"
	"github.com/onsi/gomega"
	corev1 "k8s.io/api/core/v1"
	apimeta "k8s.io/apimachinery/pkg/api/meta"
	"k8s.io/apimachinery/pkg/api/resource"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/types"
	"sigs.k8s.io/controller-runtime/pkg/client"

	kueue "sigs.k8s.io/kueue/apis/kueue/v1beta2"
	workloadjob "sigs.k8s.io/kueue/pkg/controller/jobs/job"
	"sigs.k8s.io/kueue/pkg/resources"
	utilpod "sigs.k8s.io/kueue/pkg/util/pod"
	utiltesting "sigs.k8s.io/kueue/pkg/util/testing"
	utiltestingapi "sigs.k8s.io/kueue/pkg/util/testing/v1beta2"
	testingjob "sigs.k8s.io/kueue/pkg/util/testingjobs/job"
	"sigs.k8s.io/kueue/pkg/workload"
	workloadevict "sigs.k8s.io/kueue/pkg/workload/evict"
	"sigs.k8s.io/kueue/test/util/behavioral"
	"sigs.k8s.io/kueue/test/util/behavioral/e2e"
)

var _ = ginkgo.Describe("Mid-cycle Preemption Overlap Race", ginkgo.Label("area:singlecluster", "feature:tas", "feature:preemption", "feature:midcycle"), func() {
	var (
		ns               *corev1.Namespace
		topology         *kueue.Topology
		rf               *kueue.ResourceFlavor
		cohortName       string
		cq0, cq1         *kueue.ClusterQueue
		cq2, cq3         *kueue.ClusterQueue
		lq0, lq1         *kueue.LocalQueue
		lq2, lq3         *kueue.LocalQueue
		lowPriorityClass *kueue.WorkloadPriorityClass
		p1PriorityClass  *kueue.WorkloadPriorityClass
		p2PriorityClass  *kueue.WorkloadPriorityClass
		p3PriorityClass  *kueue.WorkloadPriorityClass

		job0CPU, job1CPU resource.Quantity
		job2CPU, job3CPU resource.Quantity
	)

	ginkgo.BeforeEach(func() {
		ns = behavioral.CreateNamespaceFromPrefixWithLog(ctx, k8sClient, "e2e-race-")

		lowPriorityClass = utiltestingapi.MakeWorkloadPriorityClass("low-" + ns.Name).PriorityValue(10).Obj()
		behavioral.MustCreate(ctx, k8sClient, lowPriorityClass)
		// Distinct priorities (p1 > p2 > p3 > low) guarantee makeClassicalIterator
		// processes the three heads in the exact order wl1 -> wl2 -> wl3.
		p1PriorityClass = utiltestingapi.MakeWorkloadPriorityClass("p1-" + ns.Name).PriorityValue(103).Obj()
		behavioral.MustCreate(ctx, k8sClient, p1PriorityClass)
		p2PriorityClass = utiltestingapi.MakeWorkloadPriorityClass("p2-" + ns.Name).PriorityValue(102).Obj()
		behavioral.MustCreate(ctx, k8sClient, p2PriorityClass)
		p3PriorityClass = utiltestingapi.MakeWorkloadPriorityClass("p3-" + ns.Name).PriorityValue(101).Obj()
		behavioral.MustCreate(ctx, k8sClient, p3PriorityClass)

		// 1. Live discovery of kind-worker free TAS capacity (Allocatable minus non-TAS pods on kind-worker).
		var workerNode corev1.Node
		gomega.Expect(k8sClient.Get(ctx, types.NamespacedName{Name: "kind-worker"}, &workerNode)).To(gomega.Succeed())
		allocatableMilli := workerNode.Status.Allocatable.Cpu().MilliValue()

		var podList corev1.PodList
		gomega.Expect(k8sClient.List(ctx, &podList)).To(gomega.Succeed())
		var nonTASMilli int64
		for i := range podList.Items {
			pod := &podList.Items[i]
			if pod.Spec.NodeName != "kind-worker" || utilpod.IsTerminated(pod) {
				continue
			}
			reqs := resources.NewRequestsFromPodSpec(&pod.Spec)
			v, _ := reqs.ResourceValue(corev1.ResourceCPU).Int64()
			nonTASMilli += v
		}

		freeMilli := allocatableMilli - nonTASMilli
		unitMilli := freeMilli / 10

		// Size job0 so that job0 + job3 == freeMilli (exact 100% of TAS freeCapacity on kind-worker):
		// - In nominate():
		//   - job0 + job1 = freeMilli - 2*unitMilli < freeMilli (fits as Fit)
		//   - job0 + job2 = freeMilli - 1*unitMilli < freeMilli (fits as Fit)
		//   - job0 + job3 = freeMilli <= freeMilli              (fits as Fit)
		// - In processEntry() after job1 is admitted:
		//   - job0 + job1 + job2 = freeMilli + 1*unitMilli > freeMilli (fails TAS with FitsCheckNoTAS!)
		//   - job0 + job1 + job3 = freeMilli + 2*unitMilli > freeMilli (cannot fit until job0 is evicted!)
		job1CPU = *resource.NewMilliQuantity(2*unitMilli, resource.DecimalSI)
		job2CPU = *resource.NewMilliQuantity(3*unitMilli, resource.DecimalSI)
		job3CPU = *resource.NewMilliQuantity(4*unitMilli, resource.DecimalSI)
		job0CPU = *resource.NewMilliQuantity(freeMilli-4*unitMilli, resource.DecimalSI)

		// Cohort quota must be >= job0 + job1 + job3 (~12 units) so that in processEntry(),
		// cq2.Fits() passes the Quota check and fails specifically on TAS (FitsCheckNoTAS),
		// triggering needsTASRecompute. cq0 has 0 nominal quota so wl0 borrows all its CPU
		// and can be reclaimed by cq2 via ReclaimWithinCohort.
		cq0NominalCPU := "0"
		cq1NominalCPU := job1CPU.String()
		cq2NominalCPU := job2CPU.String()
		cq3NominalCPU := resource.NewMilliQuantity(10*unitMilli, resource.DecimalSI).String()

		topology = utiltestingapi.MakeDefaultOneLevelTopology("hostname-" + ns.Name)
		behavioral.MustCreate(ctx, k8sClient, topology)

		// Pin ResourceFlavor strictly to kind-worker so that topology evaluation
		// operates on this exact single node (as in the bug scenario).
		rf = utiltestingapi.MakeResourceFlavor("rf-" + ns.Name).
			NodeLabel(corev1.LabelHostname, "kind-worker").
			TopologyName(topology.Name).
			Obj()
		behavioral.MustCreate(ctx, k8sClient, rf)

		cohortName = "cohort-" + ns.Name
		nsSelector := &metav1.LabelSelector{
			MatchLabels: map[string]string{"admission": "enabled"},
		}

		// cq0: hosts initial victim wl0 (~60% of node free capacity). Low priority, borrows from cohort.
		cq0 = utiltestingapi.MakeClusterQueue("cq0-" + ns.Name).
			Cohort(kueue.CohortReference(cohortName)).
			ResourceGroup(*utiltestingapi.MakeFlavorQuotas(rf.Name).
				Resource(corev1.ResourceCPU, cq0NominalCPU).
				Resource(corev1.ResourceMemory, "100Gi").
				Obj()).
			Obj()
		behavioral.CreateClusterQueuesAndWaitForActive(ctx, k8sClient, cq0)
		lq0 = utiltestingapi.MakeLocalQueue("lq0", ns.Name).ClusterQueue(cq0.Name).Obj()
		behavioral.CreateLocalQueuesAndWaitForActive(ctx, k8sClient, lq0)

		// cq1: nominal 20%. Hosts wl1 (20%). Gated by NamespaceSelector until all 3 jobs are queued.
		cq1 = utiltestingapi.MakeClusterQueue("cq1-" + ns.Name).
			Cohort(kueue.CohortReference(cohortName)).
			NamespaceSelector(nsSelector).
			ResourceGroup(*utiltestingapi.MakeFlavorQuotas(rf.Name).
				Resource(corev1.ResourceCPU, cq1NominalCPU).
				Resource(corev1.ResourceMemory, "100Gi").
				Obj()).
			Obj()
		behavioral.CreateClusterQueuesAndWaitForActive(ctx, k8sClient, cq1)
		lq1 = utiltestingapi.MakeLocalQueue("lq1", ns.Name).ClusterQueue(cq1.Name).Obj()
		behavioral.CreateLocalQueuesAndWaitForActive(ctx, k8sClient, lq1)

		// cq2: nominal 30% with preemption enabled. Hosts wl2 (30%).
		cq2 = utiltestingapi.MakeClusterQueue("cq2-" + ns.Name).
			Cohort(kueue.CohortReference(cohortName)).
			NamespaceSelector(nsSelector).
			ResourceGroup(*utiltestingapi.MakeFlavorQuotas(rf.Name).
				Resource(corev1.ResourceCPU, cq2NominalCPU).
				Resource(corev1.ResourceMemory, "100Gi").
				Obj()).
			Preemption(kueue.ClusterQueuePreemption{
				ReclaimWithinCohort: kueue.PreemptionPolicyAny,
				WithinClusterQueue:  kueue.PreemptionPolicyLowerPriority,
				BorrowWithinCohort: &kueue.BorrowWithinCohort{
					Policy: kueue.BorrowWithinCohortPolicyLowerPriority,
				},
			}).
			Obj()
		behavioral.CreateClusterQueuesAndWaitForActive(ctx, k8sClient, cq2)
		lq2 = utiltestingapi.MakeLocalQueue("lq2", ns.Name).ClusterQueue(cq2.Name).Obj()
		behavioral.CreateLocalQueuesAndWaitForActive(ctx, k8sClient, lq2)

		// cq3: nominal 100% (so cohort quota is 150% and never bottlenecks TAS). Hosts wl3 (40%).
		cq3 = utiltestingapi.MakeClusterQueue("cq3-" + ns.Name).
			Cohort(kueue.CohortReference(cohortName)).
			NamespaceSelector(nsSelector).
			ResourceGroup(*utiltestingapi.MakeFlavorQuotas(rf.Name).
				Resource(corev1.ResourceCPU, cq3NominalCPU).
				Resource(corev1.ResourceMemory, "100Gi").
				Obj()).
			Preemption(kueue.ClusterQueuePreemption{
				ReclaimWithinCohort: kueue.PreemptionPolicyAny,
				WithinClusterQueue:  kueue.PreemptionPolicyLowerPriority,
				BorrowWithinCohort: &kueue.BorrowWithinCohort{
					Policy: kueue.BorrowWithinCohortPolicyLowerPriority,
				},
			}).
			Obj()
		behavioral.CreateClusterQueuesAndWaitForActive(ctx, k8sClient, cq3)
		lq3 = utiltestingapi.MakeLocalQueue("lq3", ns.Name).ClusterQueue(cq3.Name).Obj()
		behavioral.CreateLocalQueuesAndWaitForActive(ctx, k8sClient, lq3)
	})

	ginkgo.AfterEach(func() {
		gomega.Expect(behavioral.DeleteAllJobsInNamespace(ctx, k8sClient, ns)).Should(gomega.Succeed())
		gomega.Expect(client.IgnoreNotFound(k8sClient.DeleteAllOf(ctx, &corev1.Pod{}, client.InNamespace(ns.Name), client.GracePeriodSeconds(0)))).Should(gomega.Succeed())
		gomega.Expect(behavioral.DeleteWorkloadsInNamespace(ctx, k8sClient, ns)).Should(gomega.Succeed())
		behavioral.ExpectObjectToBeDeleted(ctx, k8sClient, lq0, true)
		behavioral.ExpectObjectToBeDeleted(ctx, k8sClient, lq1, true)
		behavioral.ExpectObjectToBeDeleted(ctx, k8sClient, lq2, true)
		behavioral.ExpectObjectToBeDeleted(ctx, k8sClient, lq3, true)
		behavioral.ExpectObjectToBeDeleted(ctx, k8sClient, cq0, true)
		behavioral.ExpectObjectToBeDeleted(ctx, k8sClient, cq1, true)
		behavioral.ExpectObjectToBeDeleted(ctx, k8sClient, cq2, true)
		behavioral.ExpectObjectToBeDeleted(ctx, k8sClient, cq3, true)
		behavioral.ExpectObjectToBeDeleted(ctx, k8sClient, rf, true)
		behavioral.ExpectObjectToBeDeleted(ctx, k8sClient, topology, true)
		behavioral.ExpectObjectToBeDeleted(ctx, k8sClient, lowPriorityClass, true)
		behavioral.ExpectObjectToBeDeleted(ctx, k8sClient, p1PriorityClass, true)
		behavioral.ExpectObjectToBeDeleted(ctx, k8sClient, p2PriorityClass, true)
		behavioral.ExpectObjectToBeDeleted(ctx, k8sClient, p3PriorityClass, true)
		gomega.Expect(behavioral.DeleteNamespace(ctx, k8sClient, ns)).To(gomega.Succeed())
		behavioral.ExpectAllPodsInNamespaceDeleted(ctx, k8sClient, ns)
	})

	ginkgo.It("demonstrates false Fit admission when wl3 nominated as Fit relies on mid-cycle victim eviction", func() {
		ginkgo.By("Starting job0 in cq0 to consume 60% of kind-worker capacity (low priority)")
		// Use a PreStop SleepAction(60) with TerminationGracePeriod(60) so that when
		// job0 is preempted and suspended, its pod remains Running (Terminating) on
		// kind-worker for 60s instead of exiting immediately on SIGTERM. This keeps
		// job0's CPU occupied on the node while we assert that job3's pod is Unschedulable.
		job0 := testingjob.MakeJob("job0", ns.Name).
			Queue(kueue.LocalQueueName(lq0.Name)).
			Image(e2e.GetAgnHostImage(), e2e.BehaviorWaitForDeletion).
			RequestAndLimit(corev1.ResourceCPU, job0CPU.String()).
			RequestAndLimit(corev1.ResourceMemory, "200Mi").
			PodAnnotation(kueue.PodSetRequiredTopologyAnnotation, corev1.LabelHostname).
			WorkloadPriorityClass(lowPriorityClass.Name).
			TerminationGracePeriod(60).
			Obj()
		job0.Spec.Template.Spec.Containers[0].Lifecycle = &corev1.Lifecycle{
			PreStop: &corev1.LifecycleHandler{
				Sleep: &corev1.SleepAction{
					Seconds: 60,
				},
			},
		}
		behavioral.MustCreate(ctx, k8sClient, job0)

		wl0Key := types.NamespacedName{Name: workloadjob.GetWorkloadNameForJob(job0.Name, job0.UID), Namespace: ns.Name}
		ginkgo.By("Awaiting admission and running pod of job0", func() {
			wl0 := &kueue.Workload{}
			gomega.Eventually(func(g gomega.Gomega) {
				g.Expect(k8sClient.Get(ctx, wl0Key, wl0)).To(gomega.Succeed())
				g.Expect(workload.IsAdmitted(wl0)).To(gomega.BeTrue())
			}, behavioral.MediumTimeout, behavioral.Interval).Should(gomega.Succeed())
			behavioral.ExpectJobUnsuspended(ctx, k8sClient, client.ObjectKeyFromObject(job0))
			behavioral.ExpectPodsReadyCondition(ctx, k8sClient, wl0Key)
		})

		ginkgo.By("Creating job1 (20%, p1=103), job2 (30%, p2=102), and job3 (40%, p3=101) while ns does not match cq1..cq3 NamespaceSelector")
		job1 := testingjob.MakeJob("job1", ns.Name).
			Queue(kueue.LocalQueueName(lq1.Name)).
			Image(e2e.GetAgnHostImage(), e2e.BehaviorWaitForDeletion).
			RequestAndLimit(corev1.ResourceCPU, job1CPU.String()).
			RequestAndLimit(corev1.ResourceMemory, "200Mi").
			PodAnnotation(kueue.PodSetRequiredTopologyAnnotation, corev1.LabelHostname).
			WorkloadPriorityClass(p1PriorityClass.Name).
			Obj()
		behavioral.MustCreate(ctx, k8sClient, job1)

		job2 := testingjob.MakeJob("job2", ns.Name).
			Queue(kueue.LocalQueueName(lq2.Name)).
			Image(e2e.GetAgnHostImage(), e2e.BehaviorWaitForDeletion).
			RequestAndLimit(corev1.ResourceCPU, job2CPU.String()).
			RequestAndLimit(corev1.ResourceMemory, "200Mi").
			PodAnnotation(kueue.PodSetRequiredTopologyAnnotation, corev1.LabelHostname).
			WorkloadPriorityClass(p2PriorityClass.Name).
			Obj()
		behavioral.MustCreate(ctx, k8sClient, job2)

		job3 := testingjob.MakeJob("job3", ns.Name).
			Queue(kueue.LocalQueueName(lq3.Name)).
			Image(e2e.GetAgnHostImage(), e2e.BehaviorWaitForDeletion).
			RequestAndLimit(corev1.ResourceCPU, job3CPU.String()).
			RequestAndLimit(corev1.ResourceMemory, "200Mi").
			PodAnnotation(kueue.PodSetRequiredTopologyAnnotation, corev1.LabelHostname).
			WorkloadPriorityClass(p3PriorityClass.Name).
			Obj()
		behavioral.MustCreate(ctx, k8sClient, job3)

		wl1Key := types.NamespacedName{Name: workloadjob.GetWorkloadNameForJob(job1.Name, job1.UID), Namespace: ns.Name}
		wl2Key := types.NamespacedName{Name: workloadjob.GetWorkloadNameForJob(job2.Name, job2.UID), Namespace: ns.Name}
		wl3Key := types.NamespacedName{Name: workloadjob.GetWorkloadNameForJob(job3.Name, job3.UID), Namespace: ns.Name}

		ginkgo.By("Waiting for wl1, wl2, wl3 to be parked as inadmissible in cq1, cq2, cq3", func() {
			behavioral.ExpectWorkloadsToBeInadmissibleByKeys(ctx, k8sClient, wl1Key, wl2Key, wl3Key)
		})

		ginkgo.By("Labeling the namespace so requeueWorkloadsCohort atomically activates wl1, wl2, wl3 in the same scheduling cycle", func() {
			gomega.Eventually(func(g gomega.Gomega) {
				g.Expect(k8sClient.Get(ctx, client.ObjectKeyFromObject(ns), ns)).To(gomega.Succeed())
				if ns.Labels == nil {
					ns.Labels = make(map[string]string)
				}
				ns.Labels["admission"] = "enabled"
				g.Expect(k8sClient.Update(ctx, ns)).To(gomega.Succeed())
			}, behavioral.Timeout, behavioral.Interval).Should(gomega.Succeed())
		})

		// --- DEMONSTRATION OF THE BUG ---
		// In reality, job3 only fits on kind-worker because job0 is being evicted (60% + 20% + 40% = 120% > 100%).
		// Therefore, job3 SHOULD also wait for job0's eviction (WaitingForPreemptedWorkloads).
		//
		// However, Kueue's current implementation admits job3 immediately as Fit:
		// because job3 nominated as Fit in isolation (60% + 40% <= 100%), it had no preemption targets,
		// so needsOverlapRecompute is false, and fits() subtracts preemptedWorkloads (wl0) unconditionally.
		//
		// First, verify the workload states produced by the scheduling cycle before job0's
		// Job.Stop() finishes clearing wl0's QuotaReservation:
		// - wl1 is admitted as Fit
		// - wl0 is Preempted/Evicted while still holding its QuotaReservation
		// - wl2 is waiting for wl0's eviction (WaitingForPreemptedWorkloads)
		// - wl3 is prematurely admitted as Fit while wl0 still holds its QuotaReservation
		wl0 := &kueue.Workload{}
		wl1 := &kueue.Workload{}
		wl2 := &kueue.Workload{}
		wl3 := &kueue.Workload{}
		ginkgo.By("Verifying the scheduling cycle admits wl1 and (erroneously) wl3 as Fit while wl0 is evicting and wl2 waits for preemption", func() {
			gomega.Eventually(func(g gomega.Gomega) {
				g.Expect(k8sClient.Get(ctx, wl1Key, wl1)).To(gomega.Succeed())
				g.Expect(workload.IsAdmitted(wl1)).To(gomega.BeTrue())

				g.Expect(k8sClient.Get(ctx, wl0Key, wl0)).To(gomega.Succeed())
				g.Expect(workloadevict.IsEvicted(wl0)).To(gomega.BeTrue())
				g.Expect(wl0.Status.Conditions).Should(utiltesting.HaveConditionStatusTrue(kueue.WorkloadPreempted))
				g.Expect(workload.HasQuotaReservation(wl0)).To(gomega.BeTrue())

				g.Expect(k8sClient.Get(ctx, wl2Key, wl2)).To(gomega.Succeed())
				cond := apimeta.FindStatusCondition(wl2.Status.Conditions, kueue.WorkloadQuotaReserved)
				g.Expect(cond).NotTo(gomega.BeNil())
				g.Expect(cond.Status).To(gomega.Equal(metav1.ConditionFalse))
				g.Expect(cond.Reason).To(gomega.Equal(kueue.WorkloadQuotaReservedReasonWaitingForPreemptedWorkloads))

				g.Expect(k8sClient.Get(ctx, wl3Key, wl3)).To(gomega.Succeed())
				// BUG: wl3 is admitted immediately rather than waiting for preempted workloads!
				g.Expect(workload.IsAdmitted(wl3)).To(gomega.BeTrue())
			}, behavioral.MediumTimeout, behavioral.ShortInterval).Should(gomega.Succeed())
		})

		ginkgo.By("Verifying job1's pod runs on kind-worker while job3's pod is Unschedulable because job0's pod is still terminating", func() {
			behavioral.ExpectPodsReadyCondition(ctx, k8sClient, wl1Key)

			// Because wl3 was admitted, job3 is unsuspended immediately while job0's pod is still terminating.
			behavioral.ExpectJobUnsuspended(ctx, k8sClient, client.ObjectKeyFromObject(job3))

			// Verify job3's pod cannot be scheduled by kube-scheduler onto kind-worker right away
			// because job0's terminating pod (~60%) + job1's running pod (20%) leave only 20% free CPU.
			gomega.Eventually(func(g gomega.Gomega) {
				var pods corev1.PodList
				g.Expect(k8sClient.List(ctx, &pods, client.InNamespace(ns.Name), client.MatchingLabels{"job-name": job3.Name})).To(gomega.Succeed())
				g.Expect(pods.Items).To(gomega.HaveLen(1))
				pod := &pods.Items[0]
				g.Expect(pod.Spec.SchedulingGates).To(gomega.BeEmpty())
				var scheduledCond *corev1.PodCondition
				for i := range pod.Status.Conditions {
					if pod.Status.Conditions[i].Type == corev1.PodScheduled {
						scheduledCond = &pod.Status.Conditions[i]
						break
					}
				}
				g.Expect(scheduledCond).NotTo(gomega.BeNil())
				g.Expect(scheduledCond.Status).To(gomega.Equal(corev1.ConditionFalse))
				g.Expect(scheduledCond.Reason).To(gomega.Equal(corev1.PodReasonUnschedulable))
			}, behavioral.MediumTimeout, behavioral.Interval).Should(gomega.Succeed())
		})

		ginkgo.By("Cleaning up: force-deleting job0's terminating pod so eviction completes and job2 and job3 pods can run", func() {
			gomega.Expect(k8sClient.DeleteAllOf(ctx, &corev1.Pod{}, client.InNamespace(ns.Name), client.MatchingLabels{"job-name": job0.Name}, client.GracePeriodSeconds(0))).To(gomega.Succeed())
			gomega.Eventually(func(g gomega.Gomega) {
				g.Expect(k8sClient.Get(ctx, wl2Key, wl2)).To(gomega.Succeed())
				g.Expect(workload.IsAdmitted(wl2)).To(gomega.BeTrue())
			}, behavioral.MediumTimeout, behavioral.Interval).Should(gomega.Succeed())
			behavioral.ExpectPodsReadyCondition(ctx, k8sClient, wl2Key)
			behavioral.ExpectPodsReadyCondition(ctx, k8sClient, wl3Key)
		})
	})
})
