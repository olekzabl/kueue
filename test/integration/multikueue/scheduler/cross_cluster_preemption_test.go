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

// Integration tests for cross-cluster preemption (MultiKueueCrossClusterPreemption
// feature gate + MultiKueueDispatcherModeCrossClusterPreemption dispatcher).
//
// Reuses the per-suite test cluster fixtures from suite_test.go
// (managerTestCluster, worker1TestCluster, worker2TestCluster).
//
// The topology mirrors the POC `_local/poc-multikueue-cross-preemption`:
// two tenants share a cohort across one manager and two workers. Tenant A
// is the "owner" (per-worker nominal quota; ReclaimWithinCohort=Never).
// Tenant B is the "borrower" (per-worker nominal=0; admits via cohort
// borrow; ReclaimWithinCohort=LowerPriority so it can be reclaimed). The
// dispatcher's same-CQ skip is intentional: cross-cluster preemption is
// for cross-tenant reclaim, not within-tenant. A single-CQ setup would
// not exercise the feature at all.
//
// Run only this file's tests:
//
//	make test-multikueue-integration GINKGO_ARGS="--focus 'cross-cluster preemption'"
package scheduler

import (
	"context"
	"strings"
	"time"

	"github.com/onsi/ginkgo/v2"
	"github.com/onsi/gomega"
	corev1 "k8s.io/api/core/v1"
	"k8s.io/apimachinery/pkg/api/resource"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/types"
	"k8s.io/utils/ptr"
	"sigs.k8s.io/controller-runtime/pkg/client"
	"sigs.k8s.io/controller-runtime/pkg/manager"

	config "sigs.k8s.io/kueue/apis/config/v1beta2"
	kueue "sigs.k8s.io/kueue/apis/kueue/v1beta2"
	workloadjob "sigs.k8s.io/kueue/pkg/controller/jobs/job"
	"sigs.k8s.io/kueue/pkg/features"
	"sigs.k8s.io/kueue/pkg/util/admissioncheck"
	utiltestingapi "sigs.k8s.io/kueue/pkg/util/testing/v1beta2"
	testingjob "sigs.k8s.io/kueue/pkg/util/testingjobs/job"
	"sigs.k8s.io/kueue/pkg/workload"
	"sigs.k8s.io/kueue/test/util"
)

var _ = ginkgo.Describe("MultiKueue cross-cluster preemption",
	ginkgo.Label("area:multikueue", "feature:multikueue", "feature:cross-cluster-preemption"),
	ginkgo.Ordered, ginkgo.ContinueOnFailure, func() {
		var (
			managerNs *corev1.Namespace
			worker1Ns *corev1.Namespace
			worker2Ns *corev1.Namespace

			managerSecret1, managerSecret2 *corev1.Secret
			workerCluster1, workerCluster2 *kueue.MultiKueueCluster

			managerCfg *kueue.MultiKueueConfig
			multiAC    *kueue.AdmissionCheck

			managerLowWPC, managerHighWPC *kueue.WorkloadPriorityClass

			managerFlavor *kueue.ResourceFlavor
			worker1Flavor *kueue.ResourceFlavor
			worker2Flavor *kueue.ResourceFlavor

			// Two tenants per cluster: A is the "owner" (per-worker nominal
			// quota; never a preemption victim source); B is the "borrower"
			// (per-worker nominal=0; admits via cohort borrow; can be reclaimed).
			managerTenantACq, worker1TenantACq, worker2TenantACq *kueue.ClusterQueue
			managerTenantBCq, worker1TenantBCq, worker2TenantBCq *kueue.ClusterQueue
			managerTenantALq, worker1TenantALq, worker2TenantALq *kueue.LocalQueue
			managerTenantBLq, worker1TenantBLq, worker2TenantBLq *kueue.LocalQueue
		)

		ginkgo.BeforeAll(func() {
			managerTestCluster.fwk.StartManager(managerTestCluster.ctx, managerTestCluster.cfg, func(ctx context.Context, mgr manager.Manager) {
				managerAndMultiKueueSetup(ctx, mgr, 2*time.Second, defaultEnabledIntegrations,
					config.MultiKueueDispatcherModeAllAtOnce)
			})
		})
		ginkgo.AfterAll(func() {
			managerTestCluster.fwk.StopManager(managerTestCluster.ctx)
		})

		ginkgo.BeforeEach(func() {
			features.SetFeatureGateDuringTest(ginkgo.GinkgoTB(), features.MultiKueueCrossClusterPreemption, true)
			features.SetFeatureGateDuringTest(ginkgo.GinkgoTB(), features.MultiKueueOrchestratedPreemption, true)

			managerNs = util.CreateNamespaceFromPrefixWithLog(managerTestCluster.ctx, managerTestCluster.client, "ccp-")
			worker1Ns = util.CreateNamespaceWithLog(worker1TestCluster.ctx, worker1TestCluster.client, managerNs.Name)
			worker2Ns = util.CreateNamespaceWithLog(worker2TestCluster.ctx, worker2TestCluster.client, managerNs.Name)

			w1Kubeconfig, err := worker1TestCluster.kubeConfigBytes()
			gomega.Expect(err).NotTo(gomega.HaveOccurred())
			w2Kubeconfig, err := worker2TestCluster.kubeConfigBytes()
			gomega.Expect(err).NotTo(gomega.HaveOccurred())

			managerSecret1 = &corev1.Secret{
				ObjectMeta: metav1.ObjectMeta{Name: "ccp-multikueue1", Namespace: managersConfigNamespace.Name},
				Data:       map[string][]byte{kueue.MultiKueueConfigSecretKey: w1Kubeconfig},
			}
			util.MustCreate(managerTestCluster.ctx, managerTestCluster.client, managerSecret1)
			managerSecret2 = &corev1.Secret{
				ObjectMeta: metav1.ObjectMeta{Name: "ccp-multikueue2", Namespace: managersConfigNamespace.Name},
				Data:       map[string][]byte{kueue.MultiKueueConfigSecretKey: w2Kubeconfig},
			}
			util.MustCreate(managerTestCluster.ctx, managerTestCluster.client, managerSecret2)

			workerCluster1 = utiltestingapi.MakeMultiKueueCluster("worker1").KubeConfig(kueue.SecretLocationType, managerSecret1.Name).Obj()
			util.MustCreate(managerTestCluster.ctx, managerTestCluster.client, workerCluster1)
			workerCluster2 = utiltestingapi.MakeMultiKueueCluster("worker2").KubeConfig(kueue.SecretLocationType, managerSecret2.Name).Obj()
			util.MustCreate(managerTestCluster.ctx, managerTestCluster.client, workerCluster2)

			managerCfg = utiltestingapi.MakeMultiKueueConfig("ccp-cfg").Clusters(workerCluster1.Name, workerCluster2.Name).Obj()
			util.MustCreate(managerTestCluster.ctx, managerTestCluster.client, managerCfg)
			multiAC = utiltestingapi.MakeAdmissionCheck("ccp-ac").
				ControllerName(kueue.MultiKueueControllerName).
				Parameters(kueue.GroupVersion.Group, "MultiKueueConfig", managerCfg.Name).
				Obj()
			util.CreateAdmissionChecksAndWaitForActive(managerTestCluster.ctx, managerTestCluster.client, multiAC)

			managerHighWPC = utiltestingapi.MakeWorkloadPriorityClass("ccp-high").PriorityValue(300).Obj()
			util.MustCreate(managerTestCluster.ctx, managerTestCluster.client, managerHighWPC)
			managerLowWPC = utiltestingapi.MakeWorkloadPriorityClass("ccp-low").PriorityValue(100).Obj()
			util.MustCreate(managerTestCluster.ctx, managerTestCluster.client, managerLowWPC)

			managerFlavor = utiltestingapi.MakeResourceFlavor("ccp-fl").Obj()
			util.MustCreate(managerTestCluster.ctx, managerTestCluster.client, managerFlavor)

			// Cohort name is the identifier; cross-cluster cohort is just a
			// shared `spec.cohortName` string across CQs (no separate CR).
			const cohortName = "ccp-cohort"

			// --- Manager-side CQs ---
			// Both tenant CQs on the manager have plenty of nominal so manager-
			// side admission is never the constraint. The actual quota
			// constraint that drives cross-cluster preemption is on workers.
			managerTenantACq = utiltestingapi.MakeClusterQueue("ccp-tenant-a-cq").
				Cohort(kueue.CohortReference(cohortName)).
				AdmissionChecks(kueue.AdmissionCheckReference(multiAC.Name)).
				ResourceGroup(*utiltestingapi.MakeFlavorQuotas(managerFlavor.Name).
					Resource(corev1.ResourceCPU, "10").
					Resource(corev1.ResourceMemory, "10G").
					Obj()).
				Obj()
			util.CreateClusterQueuesAndWaitForActive(managerTestCluster.ctx, managerTestCluster.client, managerTenantACq)
			managerTenantALq = utiltestingapi.MakeLocalQueue("ccp-tenant-a-lq", managerNs.Name).ClusterQueue(managerTenantACq.Name).Obj()
			util.CreateLocalQueuesAndWaitForActive(managerTestCluster.ctx, managerTestCluster.client, managerTenantALq)

			managerTenantBCq = utiltestingapi.MakeClusterQueue("ccp-tenant-b-cq").
				Cohort(kueue.CohortReference(cohortName)).
				AdmissionChecks(kueue.AdmissionCheckReference(multiAC.Name)).
				ResourceGroup(*utiltestingapi.MakeFlavorQuotas(managerFlavor.Name).
					Resource(corev1.ResourceCPU, "10").
					Resource(corev1.ResourceMemory, "10G").
					Obj()).
				Obj()
			util.CreateClusterQueuesAndWaitForActive(managerTestCluster.ctx, managerTestCluster.client, managerTenantBCq)
			managerTenantBLq = utiltestingapi.MakeLocalQueue("ccp-tenant-b-lq", managerNs.Name).ClusterQueue(managerTenantBCq.Name).Obj()
			util.CreateLocalQueuesAndWaitForActive(managerTestCluster.ctx, managerTestCluster.client, managerTenantBLq)

			// --- Worker-side CQs ---
			// Per-worker capacity math (mirrors POC):
			//   cohort:        tenant-a-cq(nom=1) + tenant-b-cq(nom=0) = 1 CPU
			//   tenant A:      owner; ReclaimWithinCohort=LowerPriority
			//   tenant B:      borrower; ReclaimWithinCohort=Never
			worker1Flavor = utiltestingapi.MakeResourceFlavor("ccp-fl").Obj()
			util.MustCreate(worker1TestCluster.ctx, worker1TestCluster.client, worker1Flavor)
			worker1TenantACq = utiltestingapi.MakeClusterQueue("ccp-tenant-a-cq").
				Cohort(kueue.CohortReference(cohortName)).
				ResourceGroup(*utiltestingapi.MakeFlavorQuotas(worker1Flavor.Name).
					Resource(corev1.ResourceCPU, "1").
					Resource(corev1.ResourceMemory, "1G").
					Obj()).
				Preemption(kueue.ClusterQueuePreemption{
					ReclaimWithinCohort: kueue.PreemptionPolicyLowerPriority,
				}).
				Obj()
			util.CreateClusterQueuesAndWaitForActive(worker1TestCluster.ctx, worker1TestCluster.client, worker1TenantACq)
			worker1TenantALq = utiltestingapi.MakeLocalQueue("ccp-tenant-a-lq", worker1Ns.Name).ClusterQueue(worker1TenantACq.Name).Obj()
			util.CreateLocalQueuesAndWaitForActive(worker1TestCluster.ctx, worker1TestCluster.client, worker1TenantALq)

			worker1TenantBCq = utiltestingapi.MakeClusterQueue("ccp-tenant-b-cq").
				Cohort(kueue.CohortReference(cohortName)).
				ResourceGroup(*utiltestingapi.MakeFlavorQuotas(worker1Flavor.Name).
					Resource(corev1.ResourceCPU, "0").
					Resource(corev1.ResourceMemory, "0").
					Obj()).
				Preemption(kueue.ClusterQueuePreemption{
					ReclaimWithinCohort: kueue.PreemptionPolicyNever,
				}).
				Obj()
			util.CreateClusterQueuesAndWaitForActive(worker1TestCluster.ctx, worker1TestCluster.client, worker1TenantBCq)
			worker1TenantBLq = utiltestingapi.MakeLocalQueue("ccp-tenant-b-lq", worker1Ns.Name).ClusterQueue(worker1TenantBCq.Name).Obj()
			util.CreateLocalQueuesAndWaitForActive(worker1TestCluster.ctx, worker1TestCluster.client, worker1TenantBLq)

			worker2Flavor = utiltestingapi.MakeResourceFlavor("ccp-fl").Obj()
			util.MustCreate(worker2TestCluster.ctx, worker2TestCluster.client, worker2Flavor)
			worker2TenantACq = utiltestingapi.MakeClusterQueue("ccp-tenant-a-cq").
				Cohort(kueue.CohortReference(cohortName)).
				ResourceGroup(*utiltestingapi.MakeFlavorQuotas(worker2Flavor.Name).
					Resource(corev1.ResourceCPU, "1").
					Resource(corev1.ResourceMemory, "1G").
					Obj()).
				Preemption(kueue.ClusterQueuePreemption{
					ReclaimWithinCohort: kueue.PreemptionPolicyLowerPriority,
				}).
				Obj()
			util.CreateClusterQueuesAndWaitForActive(worker2TestCluster.ctx, worker2TestCluster.client, worker2TenantACq)
			worker2TenantALq = utiltestingapi.MakeLocalQueue("ccp-tenant-a-lq", worker2Ns.Name).ClusterQueue(worker2TenantACq.Name).Obj()
			util.CreateLocalQueuesAndWaitForActive(worker2TestCluster.ctx, worker2TestCluster.client, worker2TenantALq)

			worker2TenantBCq = utiltestingapi.MakeClusterQueue("ccp-tenant-b-cq").
				Cohort(kueue.CohortReference(cohortName)).
				ResourceGroup(*utiltestingapi.MakeFlavorQuotas(worker2Flavor.Name).
					Resource(corev1.ResourceCPU, "0").
					Resource(corev1.ResourceMemory, "0").
					Obj()).
				Preemption(kueue.ClusterQueuePreemption{
					ReclaimWithinCohort: kueue.PreemptionPolicyNever,
				}).
				Obj()
			util.CreateClusterQueuesAndWaitForActive(worker2TestCluster.ctx, worker2TestCluster.client, worker2TenantBCq)
			worker2TenantBLq = utiltestingapi.MakeLocalQueue("ccp-tenant-b-lq", worker2Ns.Name).ClusterQueue(worker2TenantBCq.Name).Obj()
			util.CreateLocalQueuesAndWaitForActive(worker2TestCluster.ctx, worker2TestCluster.client, worker2TenantBLq)
		})

		ginkgo.AfterEach(func() {
			gomega.Expect(util.DeleteNamespace(managerTestCluster.ctx, managerTestCluster.client, managerNs)).To(gomega.Succeed())
			gomega.Expect(util.DeleteNamespace(worker1TestCluster.ctx, worker1TestCluster.client, worker1Ns)).To(gomega.Succeed())
			gomega.Expect(util.DeleteNamespace(worker2TestCluster.ctx, worker2TestCluster.client, worker2Ns)).To(gomega.Succeed())
			util.ExpectObjectToBeDeleted(managerTestCluster.ctx, managerTestCluster.client, managerTenantACq, true)
			util.ExpectObjectToBeDeleted(managerTestCluster.ctx, managerTestCluster.client, managerTenantBCq, true)
			util.ExpectObjectToBeDeleted(worker1TestCluster.ctx, worker1TestCluster.client, worker1TenantACq, true)
			util.ExpectObjectToBeDeleted(worker1TestCluster.ctx, worker1TestCluster.client, worker1TenantBCq, true)
			util.ExpectObjectToBeDeleted(worker2TestCluster.ctx, worker2TestCluster.client, worker2TenantACq, true)
			util.ExpectObjectToBeDeleted(worker2TestCluster.ctx, worker2TestCluster.client, worker2TenantBCq, true)
			util.ExpectObjectToBeDeleted(managerTestCluster.ctx, managerTestCluster.client, managerFlavor, true)
			util.ExpectObjectToBeDeleted(worker1TestCluster.ctx, worker1TestCluster.client, worker1Flavor, true)
			util.ExpectObjectToBeDeleted(worker2TestCluster.ctx, worker2TestCluster.client, worker2Flavor, true)
			util.ExpectObjectToBeDeleted(managerTestCluster.ctx, managerTestCluster.client, managerLowWPC, true)
			util.ExpectObjectToBeDeleted(managerTestCluster.ctx, managerTestCluster.client, managerHighWPC, true)
			util.ExpectObjectToBeDeleted(managerTestCluster.ctx, managerTestCluster.client, multiAC, true)
			util.ExpectObjectToBeDeleted(managerTestCluster.ctx, managerTestCluster.client, managerCfg, true)
			util.ExpectObjectToBeDeleted(managerTestCluster.ctx, managerTestCluster.client, workerCluster1, true)
			util.ExpectObjectToBeDeleted(managerTestCluster.ctx, managerTestCluster.client, workerCluster2, true)
			util.ExpectObjectToBeDeleted(managerTestCluster.ctx, managerTestCluster.client, managerSecret1, true)
			util.ExpectObjectToBeDeleted(managerTestCluster.ctx, managerTestCluster.client, managerSecret2, true)
		})

		// fillBothWorkersWithTenantB submits two tenant-B jobs that admit, one
		// per worker, exhausting cohort capacity on both workers. Returns the
		// two workload keys (on the manager) so individual scenarios can
		// observe which one is evicted later.
		fillBothWorkersWithTenantB := func(priorityClassName string) (types.NamespacedName, types.NamespacedName) {
			ginkgo.GinkgoHelper()
			b1Job := testingjob.MakeJob("tenant-b-1", managerNs.Name).
				WorkloadPriorityClass(priorityClassName).
				Queue(kueue.LocalQueueName(managerTenantBLq.Name)).
				RequestAndLimit(corev1.ResourceCPU, "1").
				RequestAndLimit(corev1.ResourceMemory, "1G").
				Obj()
			util.MustCreate(managerTestCluster.ctx, managerTestCluster.client, b1Job)
			b1Key := types.NamespacedName{Name: workloadjob.GetWorkloadNameForJob(b1Job.Name, b1Job.UID), Namespace: managerNs.Name}

			gomega.Eventually(func(g gomega.Gomega) {
				wl := &kueue.Workload{}
				g.Expect(managerTestCluster.client.Get(managerTestCluster.ctx, b1Key, wl)).To(gomega.Succeed())
				g.Expect(workload.IsAdmitted(wl)).To(gomega.BeTrue())
			}, util.Timeout, util.Interval).Should(gomega.Succeed())

			b2Job := testingjob.MakeJob("tenant-b-2", managerNs.Name).
				WorkloadPriorityClass(priorityClassName).
				Queue(kueue.LocalQueueName(managerTenantBLq.Name)).
				RequestAndLimit(corev1.ResourceCPU, "1").
				RequestAndLimit(corev1.ResourceMemory, "1G").
				Obj()
			util.MustCreate(managerTestCluster.ctx, managerTestCluster.client, b2Job)
			b2Key := types.NamespacedName{Name: workloadjob.GetWorkloadNameForJob(b2Job.Name, b2Job.UID), Namespace: managerNs.Name}

			gomega.Eventually(func(g gomega.Gomega) {
				wl := &kueue.Workload{}
				g.Expect(managerTestCluster.client.Get(managerTestCluster.ctx, b2Key, wl)).To(gomega.Succeed())
				g.Expect(workload.IsAdmitted(wl)).To(gomega.BeTrue())
			}, util.Timeout, util.Interval).Should(gomega.Succeed())

			// Wait until BOTH worker-side tenant-b-cq's reflect borrowing in
			// their Status.FlavorsUsage. Worker admission of the remote
			// workload completes (which is what manager-side IsAdmitted
			// observes via the multikueue check) *before* the worker's CQ
			// status-update reconciler propagates the usage. If we hand off
			// to the caller before both worker CQ statuses are settled,
			// tenant A's dispatcher reconcile may run before it can see
			// either CQ as a borrower, fall back to all-at-once, and set
			// tenant A's NominatedClusterNames. That terminal state is
			// never re-evaluated (the dispatcher watches Workloads, not
			// CQs), so the preemption opportunity is permanently missed.
			workerClients := []struct {
				name   string
				ctx    context.Context
				client client.Client
			}{
				{"worker1", worker1TestCluster.ctx, worker1TestCluster.client},
				{"worker2", worker2TestCluster.ctx, worker2TestCluster.client},
			}
			gomega.Eventually(func(g gomega.Gomega) {
				for _, w := range workerClients {
					cq := &kueue.ClusterQueue{}
					g.Expect(w.client.Get(w.ctx, types.NamespacedName{Name: "ccp-tenant-b-cq"}, cq)).To(gomega.Succeed())
					var cpuUsed bool
					for _, fu := range cq.Status.FlavorsUsage {
						for _, ru := range fu.Resources {
							if ru.Name == corev1.ResourceCPU && !ru.Total.IsZero() {
								cpuUsed = true
							}
						}
					}
					g.Expect(cpuUsed).To(gomega.BeTrue(),
						"%s tenant-b-cq Status.FlavorsUsage does not yet show CPU usage", w.name)
				}
			}, util.Timeout, util.Interval).Should(gomega.Succeed())

			return b1Key, b2Key
		}

		// Scenario 1: Happy path — tenant B fills both workers via cohort
		// borrow; tenant A's higher-priority workload reclaims its quota by
		// evicting one of B's borrowing workloads. This is the ownership-
		// reclaim flow the dispatcher exists to enable.
		//
		// Assertion strategy: we check the WorkloadEvicted condition's
		// Message rather than its Status. The dispatcher patches the victim
		// with Status=True, but the manager scheduler immediately re-admits
		// the evicted workload (its CQ has plenty of cohort capacity in this
		// envtest topology), which calls SetQuotaReservation and resets
		// WorkloadEvicted to Status=False with `Message="Previously: <prev>"`.
		// The Message — "evicted by cross-cluster preemption for ..." — is
		// preserved across the reset and is the durable signal that our
		// dispatcher fired. (In a real cluster the re-admit-on-the-other-
		// worker scenario takes longer, so the True window is wider; envtest
		// is just very fast.)
		ginkgo.It("should evict a borrowing tenant-B workload", func() {
			b1Key, b2Key := fillBothWorkersWithTenantB(managerLowWPC.Name)

			aJob := testingjob.MakeJob("tenant-a-1", managerNs.Name).
				WorkloadPriorityClass(managerHighWPC.Name).
				Queue(kueue.LocalQueueName(managerTenantALq.Name)).
				RequestAndLimit(corev1.ResourceCPU, "1").
				RequestAndLimit(corev1.ResourceMemory, "1G").
				Obj()
			util.MustCreate(managerTestCluster.ctx, managerTestCluster.client, aJob)

			ginkgo.By("one of the borrowing tenant-B workloads is evicted while the other remains admitted", func() {
				gomega.Eventually(func(g gomega.Gomega) {
					evictedOnManager := 0
					admittedOnManager := 0
					evictedOnWorkers := 0
					admittedOnWorkers := 0
					for _, key := range []types.NamespacedName{b1Key, b2Key} {
						wl := &kueue.Workload{}
						g.Expect(managerTestCluster.client.Get(managerTestCluster.ctx, key, wl)).To(gomega.Succeed())
						
						acState := admissioncheck.FindAdmissionCheck(wl.Status.AdmissionChecks, "ccp-ac")
						if acState != nil {
							if acState.State == kueue.CheckStateReady {
								admittedOnManager++
							} else if acState.State == kueue.CheckStateRetry && strings.Contains(acState.Message, "Workload evicted on worker cluster") {
								evictedOnManager++
							} else if acState.State == kueue.CheckStatePending && strings.Contains(acState.Message, "Previously: Retry") {
								evictedOnManager++
							}
						}

						for _, worker := range []cluster{worker1TestCluster, worker2TestCluster} {
							remoteWl := &kueue.Workload{}
							g.Expect(client.IgnoreNotFound(worker.client.Get(worker.ctx, key, remoteWl))).To(gomega.Succeed())
							if workload.IsAdmitted(remoteWl) {
								admittedOnWorkers++
							} else if workload.IsEvicted(remoteWl) {
								evictedOnWorkers++
							}
						}
					}
					g.Expect(evictedOnManager).To(gomega.Equal(1), "expected exactly one tenant-B workload to be evicted on the manager")
					g.Expect(admittedOnManager).To(gomega.Equal(1), "expected exactly one tenant-B workload to remain admitted on the manager")
					g.Expect(evictedOnWorkers).To(gomega.Equal(1), "expected exactly one tenant-B workload to be evicted on the workers")
					g.Expect(admittedOnWorkers).To(gomega.Equal(1), "expected exactly one tenant-B workload to remain admitted on the workers")
				}, util.MediumTimeout, util.Interval).Should(gomega.Succeed())
			})
		})

		// Scenario 2: B fills both workers at HIGH priority. Tenant A's
		// low-priority workload cannot reclaim — tenant-b-cq's
		// ReclaimWithinCohort=LowerPriority blocks eviction since
		// incoming.priority is not strictly greater than victim.priority.
		ginkgo.It("should NOT preempt when reclaiming tenant-A workload has lower priority than the borrowing victim", func() {
			b1Key, b2Key := fillBothWorkersWithTenantB(managerHighWPC.Name)

			aJob := testingjob.MakeJob("tenant-a-1", managerNs.Name).
				WorkloadPriorityClass(managerLowWPC.Name).
				Queue(kueue.LocalQueueName(managerTenantALq.Name)).
				RequestAndLimit(corev1.ResourceCPU, "1").
				RequestAndLimit(corev1.ResourceMemory, "1G").
				Obj()
			util.MustCreate(managerTestCluster.ctx, managerTestCluster.client, aJob)

			ginkgo.By("neither tenant-B workload is evicted", func() {
				gomega.Consistently(func(g gomega.Gomega) {
					for _, key := range []types.NamespacedName{b1Key, b2Key} {
						wl := &kueue.Workload{}
						g.Expect(managerTestCluster.client.Get(managerTestCluster.ctx, key, wl)).To(gomega.Succeed())
						g.Expect(workload.IsEvicted(wl)).To(gomega.BeFalse(),
							"tenant-B %s was evicted; cross-cluster preemption should require strictly higher incoming priority",
							key.Name)
					}
				}, 5*time.Second, 500*time.Millisecond).Should(gomega.Succeed())
			})
		})


		// Scenario 5: BorrowWithinCohort.MaxPriorityThreshold on the
		// incoming workload's CQ caps which victims may be evicted via
		// borrow-driven preemption. Standard LowerPriority alone would
		// permit eviction (incoming 300 > victim 100), but the threshold
		// (50) is a victim-side cap — the victim's priority must be ≤
		// threshold to be eligible. B's priority (100) is above the
		// threshold, so the dispatcher must skip the candidate.
		ginkgo.When("BorrowWithinCohort.MaxPriorityThreshold protects the victim", func() {
			ginkgo.BeforeEach(func() {
				// Lower manager-A nominal to 1 CPU/1G so submitting a
				// second 1-CPU tenant-A job puts A above its manager-side
				// nominal — i.e. the dispatcher classifies A's second
				// job as a borrow-preemption attempt, gating victim
				// eligibility on canBorrowAgainstVictim.
				cq := &kueue.ClusterQueue{}
				gomega.Expect(managerTestCluster.client.Get(
					managerTestCluster.ctx,
					types.NamespacedName{Name: managerTenantACq.Name},
					cq,
				)).To(gomega.Succeed())
				cq.Spec.ResourceGroups[0].Flavors[0].Resources[0].NominalQuota = resource.MustParse("1")
				cq.Spec.ResourceGroups[0].Flavors[0].Resources[1].NominalQuota = resource.MustParse("1G")
				cq.Spec.Preemption = &kueue.ClusterQueuePreemption{
					ReclaimWithinCohort: kueue.PreemptionPolicyLowerPriority,
					BorrowWithinCohort: &kueue.BorrowWithinCohort{
						Policy:               kueue.BorrowWithinCohortPolicyLowerPriority,
						MaxPriorityThreshold: ptr.To(int32(50)),
					},
				}
				gomega.Expect(managerTestCluster.client.Update(managerTestCluster.ctx, cq)).To(gomega.Succeed())
			})

			ginkgo.It("should NOT borrow-preempt a tenant-B victim whose priority exceeds the threshold", func() {
				// Step 1: tenant-A's first workload occupies one worker's
				// per-tenant nominal (1 CPU per worker is A's only
				// physical capacity).
				a1Job := testingjob.MakeJob("tenant-a-1", managerNs.Name).
					WorkloadPriorityClass(managerHighWPC.Name).
					Queue(kueue.LocalQueueName(managerTenantALq.Name)).
					RequestAndLimit(corev1.ResourceCPU, "1").
					RequestAndLimit(corev1.ResourceMemory, "1G").
					Obj()
				util.MustCreate(managerTestCluster.ctx, managerTestCluster.client, a1Job)
				a1Key := types.NamespacedName{Name: workloadjob.GetWorkloadNameForJob(a1Job.Name, a1Job.UID), Namespace: managerNs.Name}
				gomega.Eventually(func(g gomega.Gomega) {
					wl := &kueue.Workload{}
					g.Expect(managerTestCluster.client.Get(managerTestCluster.ctx, a1Key, wl)).To(gomega.Succeed())
					g.Expect(workload.IsAdmitted(wl)).To(gomega.BeTrue())
				}, util.Timeout, util.Interval).Should(gomega.Succeed())

				// Step 2: tenant-B borrows the remaining cohort slot on
				// the other worker at priority 100 — the candidate the
				// threshold must protect.
				b1Job := testingjob.MakeJob("tenant-b-1", managerNs.Name).
					WorkloadPriorityClass(managerLowWPC.Name).
					Queue(kueue.LocalQueueName(managerTenantBLq.Name)).
					RequestAndLimit(corev1.ResourceCPU, "1").
					RequestAndLimit(corev1.ResourceMemory, "1G").
					Obj()
				util.MustCreate(managerTestCluster.ctx, managerTestCluster.client, b1Job)
				b1Key := types.NamespacedName{Name: workloadjob.GetWorkloadNameForJob(b1Job.Name, b1Job.UID), Namespace: managerNs.Name}
				gomega.Eventually(func(g gomega.Gomega) {
					wl := &kueue.Workload{}
					g.Expect(managerTestCluster.client.Get(managerTestCluster.ctx, b1Key, wl)).To(gomega.Succeed())
					g.Expect(workload.IsAdmitted(wl)).To(gomega.BeTrue())
				}, util.Timeout, util.Interval).Should(gomega.Succeed())

				// Wait for some worker tenant-b-cq to reflect borrowing
				// before A's second submission so the dispatcher sees B
				// as a candidate. Same propagation race
				// fillBothWorkersWithTenantB guards against.
				gomega.Eventually(func(g gomega.Gomega) {
					seen := false
					for _, w := range []struct {
						ctx    context.Context
						client client.Client
					}{
						{worker1TestCluster.ctx, worker1TestCluster.client},
						{worker2TestCluster.ctx, worker2TestCluster.client},
					} {
						cq := &kueue.ClusterQueue{}
						g.Expect(w.client.Get(w.ctx, types.NamespacedName{Name: "ccp-tenant-b-cq"}, cq)).To(gomega.Succeed())
						for _, fu := range cq.Status.FlavorsUsage {
							for _, ru := range fu.Resources {
								if ru.Name == corev1.ResourceCPU && !ru.Total.IsZero() {
									seen = true
								}
							}
						}
					}
					g.Expect(seen).To(gomega.BeTrue(),
						"no worker tenant-b-cq Status.FlavorsUsage reflects borrowing yet")
				}, util.Timeout, util.Interval).Should(gomega.Succeed())

				// Step 3: tenant-A's second workload pushes A above its
				// manager nominal (1 CPU). Dispatcher fires with
				// preemptorWouldBorrow=true and gates eviction on
				// canBorrowAgainstVictim, which the threshold blocks.
				a2Job := testingjob.MakeJob("tenant-a-2", managerNs.Name).
					WorkloadPriorityClass(managerHighWPC.Name).
					Queue(kueue.LocalQueueName(managerTenantALq.Name)).
					RequestAndLimit(corev1.ResourceCPU, "1").
					RequestAndLimit(corev1.ResourceMemory, "1G").
					Obj()
				util.MustCreate(managerTestCluster.ctx, managerTestCluster.client, a2Job)

				ginkgo.By("tenant-B workload is NOT evicted (its priority 100 exceeds the threshold 50)", func() {
					gomega.Consistently(func(g gomega.Gomega) {
						wl := &kueue.Workload{}
						g.Expect(managerTestCluster.client.Get(managerTestCluster.ctx, b1Key, wl)).To(gomega.Succeed())
						g.Expect(workload.IsEvicted(wl)).To(gomega.BeFalse(),
							"tenant-B workload was evicted despite its priority (100) being above MaxPriorityThreshold (50)")
					}, 5*time.Second, 500*time.Millisecond).Should(gomega.Succeed())
				})
			})
		})
	})
