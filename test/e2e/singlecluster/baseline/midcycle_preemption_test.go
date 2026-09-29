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
	"sync"

	"github.com/onsi/ginkgo/v2"
	"github.com/onsi/gomega"
	corev1 "k8s.io/api/core/v1"
	apimeta "k8s.io/apimachinery/pkg/api/meta"
	"k8s.io/apimachinery/pkg/api/resource"
	"k8s.io/apimachinery/pkg/types"
	"sigs.k8s.io/controller-runtime/pkg/client"

	kueue "sigs.k8s.io/kueue/apis/kueue/v1beta2"
	workloadjob "sigs.k8s.io/kueue/pkg/controller/jobs/job"
	utiltesting "sigs.k8s.io/kueue/pkg/util/testing"
	utiltestingapi "sigs.k8s.io/kueue/pkg/util/testing/v1beta2"
	testingjob "sigs.k8s.io/kueue/pkg/util/testingjobs/job"
	"sigs.k8s.io/kueue/pkg/workload"
	workloadevict "sigs.k8s.io/kueue/pkg/workload/evict"
	"sigs.k8s.io/kueue/test/util"
)

var _ = ginkgo.Describe("Mid-cycle Preemption Overlap Race", ginkgo.Label("area:singlecluster", "feature:tas", "feature:preemption", "feature:midcycle"), func() {
	var (
		ns                *corev1.Namespace
		topology          *kueue.Topology
		rf                *kueue.ResourceFlavor
		cohortName        string
		cq0, cq1          *kueue.ClusterQueue
		cq2, cq3          *kueue.ClusterQueue
		lq0, lq1          *kueue.LocalQueue
		lq2, lq3          *kueue.LocalQueue
		lowPriorityClass  *kueue.WorkloadPriorityClass
		highPriorityClass *kueue.WorkloadPriorityClass

		job0CPU, job1CPU resource.Quantity
		job2CPU, job3CPU resource.Quantity
	)

	ginkgo.BeforeEach(func() {
		ns = util.CreateNamespaceFromPrefixWithLog(ctx, k8sClient, "e2e-race-")

		lowPriorityClass = utiltestingapi.MakeWorkloadPriorityClass("low-" + ns.Name).PriorityValue(10).Obj()
		util.MustCreate(ctx, k8sClient, lowPriorityClass)
		highPriorityClass = utiltestingapi.MakeWorkloadPriorityClass("high-" + ns.Name).PriorityValue(100).Obj()
		util.MustCreate(ctx, k8sClient, highPriorityClass)

		// 1. Live discovery of kind-worker capacity
		var workerNode corev1.Node
		gomega.Expect(k8sClient.Get(ctx, types.NamespacedName{Name: "kind-worker"}, &workerNode)).To(gomega.Succeed())
		allocatableMilli := workerNode.Status.Allocatable.Cpu().MilliValue()

		// Use 80% of node allocatable capacity to avoid system daemon contention, divided into 10 shares
		nodeCapacityMilli := (allocatableMilli * 8) / 10
		unitMilli := nodeCapacityMilli / 10

		job0CPU = *resource.NewMilliQuantity(6*unitMilli, resource.DecimalSI) // 60% of node
		job1CPU = *resource.NewMilliQuantity(2*unitMilli, resource.DecimalSI) // 20% of node
		job2CPU = *resource.NewMilliQuantity(3*unitMilli, resource.DecimalSI) // 30% of node
		job3CPU = *resource.NewMilliQuantity(4*unitMilli, resource.DecimalSI) // 40% of node

		cq0NominalCPU := "0"
		cq1NominalCPU := resource.NewMilliQuantity(2*unitMilli, resource.DecimalSI).String()
		cq2NominalCPU := resource.NewMilliQuantity(3*unitMilli, resource.DecimalSI).String()
		cq3NominalCPU := resource.NewMilliQuantity(5*unitMilli, resource.DecimalSI).String()

		topology = utiltestingapi.MakeDefaultOneLevelTopology("hostname-" + ns.Name)
		util.MustCreate(ctx, k8sClient, topology)

		// Pin ResourceFlavor strictly to kind-worker so that topology evaluation
		// operates on this exact single node (as in the bug scenario).
		rf = utiltestingapi.MakeResourceFlavor("rf-" + ns.Name).
			NodeLabel(corev1.LabelHostname, "kind-worker").
			TopologyName(topology.Name).
			Obj()
		util.MustCreate(ctx, k8sClient, rf)

		// Flat cohort whose total capacity is strictly the sum of leaf CQ nominal quotas:
		// cq0 (6) + cq1 (2) + cq2 (3) + cq3 (4) = 15 units of quota, but kind-worker has only 10 units!
		cohortName = "cohort-" + ns.Name

		// cq0: hosts initial victim wl0 (60% of node capacity). Low priority.
		cq0 = utiltestingapi.MakeClusterQueue("cq0-" + ns.Name).
			Cohort(kueue.CohortReference(cohortName)).
			ResourceGroup(*utiltestingapi.MakeFlavorQuotas(rf.Name).
				Resource(corev1.ResourceCPU, cq0NominalCPU).
				Resource(corev1.ResourceMemory, "100Gi").
				Obj()).
			Obj()
		util.CreateClusterQueuesAndWaitForActive(ctx, k8sClient, cq0)
		lq0 = utiltestingapi.MakeLocalQueue("lq0", ns.Name).ClusterQueue(cq0.Name).Obj()
		util.CreateLocalQueuesAndWaitForActive(ctx, k8sClient, lq0)

		// cq1: nominal 20%. Hosts wl1 (20%).
		cq1 = utiltestingapi.MakeClusterQueue("cq1-" + ns.Name).
			Cohort(kueue.CohortReference(cohortName)).
			ResourceGroup(*utiltestingapi.MakeFlavorQuotas(rf.Name).
				Resource(corev1.ResourceCPU, cq1NominalCPU).
				Resource(corev1.ResourceMemory, "100Gi").
				Obj()).
			Obj()
		util.CreateClusterQueuesAndWaitForActive(ctx, k8sClient, cq1)

		// cq2: nominal 30% with preemption enabled. Hosts wl2 (30%).
		cq2 = utiltestingapi.MakeClusterQueue("cq2-" + ns.Name).
			Cohort(kueue.CohortReference(cohortName)).
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
		util.CreateClusterQueuesAndWaitForActive(ctx, k8sClient, cq2)

		// cq3: nominal 40%. Hosts wl3 (40%).
		cq3 = utiltestingapi.MakeClusterQueue("cq3-" + ns.Name).
			Cohort(kueue.CohortReference(cohortName)).
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
		util.CreateClusterQueuesAndWaitForActive(ctx, k8sClient, cq3)

		// Create lq1, lq2, lq3 on Hold so all 3 workloads can be queued as heads simultaneously.
		lq1 = utiltestingapi.MakeLocalQueue("lq1", ns.Name).ClusterQueue(cq1.Name).StopPolicy(kueue.Hold).Obj()
		util.MustCreate(ctx, k8sClient, lq1)
		lq2 = utiltestingapi.MakeLocalQueue("lq2", ns.Name).ClusterQueue(cq2.Name).StopPolicy(kueue.Hold).Obj()
		util.MustCreate(ctx, k8sClient, lq2)
		lq3 = utiltestingapi.MakeLocalQueue("lq3", ns.Name).ClusterQueue(cq3.Name).StopPolicy(kueue.Hold).Obj()
		util.MustCreate(ctx, k8sClient, lq3)
	})

	ginkgo.AfterEach(func() {
		gomega.Expect(util.DeleteAllJobsInNamespace(ctx, k8sClient, ns)).Should(gomega.Succeed())
		gomega.Expect(util.DeleteWorkloadsInNamespace(ctx, k8sClient, ns)).Should(gomega.Succeed())
		util.ExpectObjectToBeDeleted(ctx, k8sClient, lq0, true)
		util.ExpectObjectToBeDeleted(ctx, k8sClient, lq1, true)
		util.ExpectObjectToBeDeleted(ctx, k8sClient, lq2, true)
		util.ExpectObjectToBeDeleted(ctx, k8sClient, lq3, true)
		util.ExpectObjectToBeDeleted(ctx, k8sClient, cq0, true)
		util.ExpectObjectToBeDeleted(ctx, k8sClient, cq1, true)
		util.ExpectObjectToBeDeleted(ctx, k8sClient, cq2, true)
		util.ExpectObjectToBeDeleted(ctx, k8sClient, cq3, true)
		util.ExpectObjectToBeDeleted(ctx, k8sClient, rf, true)
		util.ExpectObjectToBeDeleted(ctx, k8sClient, topology, true)
		util.ExpectObjectToBeDeleted(ctx, k8sClient, lowPriorityClass, true)
		util.ExpectObjectToBeDeleted(ctx, k8sClient, highPriorityClass, true)
	})

	ginkgo.It("demonstrates false Fit admission when wl3 nominated as Fit relies on mid-cycle victim eviction", func() {
		ginkgo.By("Starting job0 in cq0 to consume 60% of kind-worker capacity (low priority)")
		job0 := testingjob.MakeJob("job0", ns.Name).
			Queue(kueue.LocalQueueName(lq0.Name)).
			Image(util.GetAgnHostImage(), util.BehaviorWaitForDeletion).
			RequestAndLimit(corev1.ResourceCPU, job0CPU.String()).
			RequestAndLimit(corev1.ResourceMemory, "10Mi").
			PodAnnotation(kueue.PodSetRequiredTopologyAnnotation, corev1.LabelHostname).
			WorkloadPriorityClass(lowPriorityClass.Name).
			TerminationGracePeriod(60).
			Obj()
		util.MustCreate(ctx, k8sClient, job0)

		wl0Key := types.NamespacedName{Name: workloadjob.GetWorkloadNameForJob(job0.Name, job0.UID), Namespace: ns.Name}
		ginkgo.By("Awaiting admission of job0", func() {
			wl0 := &kueue.Workload{}
			gomega.Eventually(func(g gomega.Gomega) {
				g.Expect(k8sClient.Get(ctx, wl0Key, wl0)).To(gomega.Succeed())
				g.Expect(wl0.Status.Admission).NotTo(gomega.BeNil())
			}, util.MediumTimeout, util.Interval).Should(gomega.Succeed())
		})
		util.ExpectJobUnsuspended(ctx, k8sClient, client.ObjectKeyFromObject(job0))

		ginkgo.By("Creating job1 (20%), job2 (30%), and job3 (40%) with high priority while their queues are on Hold")
		job1 := testingjob.MakeJob("job1", ns.Name).
			Queue(kueue.LocalQueueName(lq1.Name)).
			Image(util.GetAgnHostImage(), util.BehaviorWaitForDeletion).
			RequestAndLimit(corev1.ResourceCPU, job1CPU.String()).
			RequestAndLimit(corev1.ResourceMemory, "10Mi").
			PodAnnotation(kueue.PodSetRequiredTopologyAnnotation, corev1.LabelHostname).
			WorkloadPriorityClass(highPriorityClass.Name).
			Obj()
		util.MustCreate(ctx, k8sClient, job1)

		job2 := testingjob.MakeJob("job2", ns.Name).
			Queue(kueue.LocalQueueName(lq2.Name)).
			Image(util.GetAgnHostImage(), util.BehaviorWaitForDeletion).
			RequestAndLimit(corev1.ResourceCPU, job2CPU.String()).
			RequestAndLimit(corev1.ResourceMemory, "10Mi").
			PodAnnotation(kueue.PodSetRequiredTopologyAnnotation, corev1.LabelHostname).
			WorkloadPriorityClass(highPriorityClass.Name).
			Obj()
		util.MustCreate(ctx, k8sClient, job2)

		job3 := testingjob.MakeJob("job3", ns.Name).
			Queue(kueue.LocalQueueName(lq3.Name)).
			Image(util.GetAgnHostImage(), util.BehaviorWaitForDeletion).
			RequestAndLimit(corev1.ResourceCPU, job3CPU.String()).
			RequestAndLimit(corev1.ResourceMemory, "10Mi").
			PodAnnotation(kueue.PodSetRequiredTopologyAnnotation, corev1.LabelHostname).
			WorkloadPriorityClass(highPriorityClass.Name).
			Obj()
		util.MustCreate(ctx, k8sClient, job3)

		wl1Key := types.NamespacedName{Name: workloadjob.GetWorkloadNameForJob(job1.Name, job1.UID), Namespace: ns.Name}
		wl2Key := types.NamespacedName{Name: workloadjob.GetWorkloadNameForJob(job2.Name, job2.UID), Namespace: ns.Name}
		wl3Key := types.NamespacedName{Name: workloadjob.GetWorkloadNameForJob(job3.Name, job3.UID), Namespace: ns.Name}

		ginkgo.By("Unholding lq1, lq2, lq3 concurrently so all three are evaluated in the same cycle")
		var wg sync.WaitGroup
		for _, q := range []*kueue.LocalQueue{lq1, lq2, lq3} {
			wg.Add(1)
			go func(lq *kueue.LocalQueue) {
				defer wg.Done()
				util.UnholdLocalQueue(ctx, k8sClient, lq)
			}(q)
		}
		wg.Wait()

		ginkgo.By("Verifying job1 is admitted as Fit without preemption")
		wl1 := &kueue.Workload{}
		gomega.Eventually(func(g gomega.Gomega) {
			g.Expect(k8sClient.Get(ctx, wl1Key, wl1)).To(gomega.Succeed())
			g.Expect(wl1.Status.Admission).NotTo(gomega.BeNil())
		}, util.MediumTimeout, util.Interval).Should(gomega.Succeed())

		ginkgo.By("Verifying job2 triggers preemption of job0 to fit on kind-worker")
		wl0 := &kueue.Workload{}
		gomega.Eventually(func(g gomega.Gomega) {
			g.Expect(k8sClient.Get(ctx, wl0Key, wl0)).To(gomega.Succeed())
			g.Expect(workloadevict.IsEvicted(wl0)).To(gomega.BeTrue())
			g.Expect(wl0.Status.Conditions).Should(utiltesting.HaveConditionStatusTrue(kueue.WorkloadPreempted))
		}, util.MediumTimeout, util.Interval).Should(gomega.Succeed())

		wl2 := &kueue.Workload{}
		gomega.Eventually(func(g gomega.Gomega) {
			g.Expect(k8sClient.Get(ctx, wl2Key, wl2)).To(gomega.Succeed())
			cond := apimeta.FindStatusCondition(wl2.Status.Conditions, string(kueue.WorkloadQuotaReserved))
			g.Expect(cond).NotTo(gomega.BeNil())
			g.Expect(cond.Reason).To(gomega.BeElementOf(
				kueue.WorkloadQuotaReservedReasonWaitingForPreemptedWorkloads,
				kueue.WorkloadQuotaReserved,
			))
		}, util.MediumTimeout, util.Interval).Should(gomega.Succeed())

		// --- DEMONSTRATION OF THE BUG ---
		// In reality, job3 only fits on the node and in the cohort because job0 is being evicted.
		// Therefore, job3 SHOULD also wait for job0's eviction (WaitingForPreemptedWorkloads).
		//
		// However, Kueue's current implementation admits job3 immediately as Fit:
		// because job3 nominated as Fit in isolation (60% + 40% <= 100%), it had no preemption targets,
		// so needsOverlapRecompute is false and DeferredFit never triggers.
		//
		// The test asserts this actual (mis)behavior: job3 is admitted immediately, and its Job is un-suspended.
		ginkgo.By("Demonstrating the bug: job3 is admitted immediately as Fit instead of waiting for job0 eviction", func() {
			wl3 := &kueue.Workload{}
			gomega.Eventually(func(g gomega.Gomega) {
				g.Expect(k8sClient.Get(ctx, wl3Key, wl3)).To(gomega.Succeed())
				// BUG: wl3 is admitted immediately rather than waiting for preempted workloads!
				g.Expect(workload.IsAdmitted(wl3)).To(gomega.BeTrue())
			}, util.MediumTimeout, util.Interval).Should(gomega.Succeed())

			// Because wl3 was admitted, job3 is unsuspended immediately while job0's pods are still terminating.
			util.ExpectJobUnsuspended(ctx, k8sClient, client.ObjectKeyFromObject(job3))
		})

		ginkgo.By("Cleaning up: finishing eviction for job0 so the remaining jobs can complete", func() {
			util.FinishEvictionForWorkloads(ctx, k8sClient, wl0)
			gomega.Eventually(func(g gomega.Gomega) {
				g.Expect(k8sClient.Get(ctx, wl2Key, wl2)).To(gomega.Succeed())
				g.Expect(wl2.Status.Admission).NotTo(gomega.BeNil())
			}, util.MediumTimeout, util.Interval).Should(gomega.Succeed())
		})
	})
})
