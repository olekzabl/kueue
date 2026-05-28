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

package workloaddispatcher

import (
	"context"
	"sort"
	"sync"
	"testing"
	"time"

	"github.com/google/go-cmp/cmp"
	"github.com/google/go-cmp/cmp/cmpopts"
	corev1 "k8s.io/api/core/v1"
	"k8s.io/apimachinery/pkg/api/resource"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/types"
	testingclock "k8s.io/utils/clock/testing"
	ctrl "sigs.k8s.io/controller-runtime"
	"sigs.k8s.io/controller-runtime/pkg/client"
	"sigs.k8s.io/controller-runtime/pkg/client/fake"

	kueue "sigs.k8s.io/kueue/apis/kueue/v1beta2"
	"sigs.k8s.io/kueue/pkg/controller/constants"
	"sigs.k8s.io/kueue/pkg/util/admissioncheck"
	utiltestingapi "sigs.k8s.io/kueue/pkg/util/testing/v1beta2"
)

// fakeRemoteView is an in-memory RemoteView. Membership is configured
// explicitly per (cluster, ClusterQueue), with the ClusterQueue's preemption
// policy carried so the dispatcher's policy gating is exercised. Workloads
// admitted on each (cluster, ClusterQueue) are configured separately.
type fakeRemoteView struct {
	mu sync.Mutex

	// memberCQs[clusterName] = list of ClusterQueues on that worker.
	memberCQs map[string][]kueue.ClusterQueue

	// admittedWLs[clusterName + "/" + clusterQueue] = workloads.
	admittedWLs map[string][]kueue.Workload
}

func newFakeRemoteView() *fakeRemoteView {
	return &fakeRemoteView{
		memberCQs:   map[string][]kueue.ClusterQueue{},
		admittedWLs: map[string][]kueue.Workload{},
	}
}

// addMemberCQ registers a worker ClusterQueue with the given cohort name +
// reclaim policy. Defaults the CQ's ResourceGroups + Status.FlavorsUsage to
// "borrowing" (usage above nominal) so tests focused on priority/policy
// don't have to spell out quota state. Use addMemberCQWithQuota when a test
// needs explicit usage vs. nominal.
func (f *fakeRemoteView) addMemberCQ(clusterName, cqName, cohortName string, reclaim kueue.PreemptionPolicy) {
	f.addMemberCQWithQuota(clusterName, cqName, cohortName, reclaim, 1, 10)
}

// addMemberCQWithQuota registers a worker ClusterQueue with the given cohort
// name, reclaim policy, and a single (default-flavor, cpu) quota tuple. Use
// nominalCPU < usageCPU to mark the CQ as a borrower and ≥ to mark it as a
// non-borrower (at-or-below nominal).
func (f *fakeRemoteView) addMemberCQWithQuota(clusterName, cqName, cohortName string, reclaim kueue.PreemptionPolicy, nominalCPU, usageCPU int64) {
	f.mu.Lock()
	defer f.mu.Unlock()
	cq := kueue.ClusterQueue{
		ObjectMeta: metav1.ObjectMeta{Name: cqName},
		Spec: kueue.ClusterQueueSpec{
			CohortName: kueue.CohortReference(cohortName),
			Preemption: &kueue.ClusterQueuePreemption{ReclaimWithinCohort: reclaim},
			ResourceGroups: []kueue.ResourceGroup{{
				CoveredResources: []corev1.ResourceName{corev1.ResourceCPU},
				Flavors: []kueue.FlavorQuotas{{
					Name: "default-flavor",
					Resources: []kueue.ResourceQuota{{
						Name:         corev1.ResourceCPU,
						NominalQuota: *resource.NewQuantity(nominalCPU, resource.DecimalSI),
					}},
				}},
			}},
		},
		Status: kueue.ClusterQueueStatus{
			FlavorsUsage: []kueue.FlavorUsage{{
				Name: "default-flavor",
				Resources: []kueue.ResourceUsage{{
					Name:  corev1.ResourceCPU,
					Total: *resource.NewQuantity(usageCPU, resource.DecimalSI),
				}},
			}},
		},
	}
	f.memberCQs[clusterName] = append(f.memberCQs[clusterName], cq)
}

func (f *fakeRemoteView) addAdmitted(clusterName, clusterQueue string, wls ...kueue.Workload) {
	f.mu.Lock()
	defer f.mu.Unlock()
	key := clusterName + "/" + clusterQueue
	f.admittedWLs[key] = append(f.admittedWLs[key], wls...)
}

func (f *fakeRemoteView) FindCohortMembers(_ context.Context, cohortName string, clusterNames []string) ([]CohortMember, error) {
	f.mu.Lock()
	defer f.mu.Unlock()
	out := make([]CohortMember, 0)
	for _, name := range clusterNames {
		for _, cq := range f.memberCQs[name] {
			if string(cq.Spec.CohortName) == cohortName {
				out = append(out, CohortMember{ClusterName: name, ClusterQueue: cq})
			}
		}
	}
	return out, nil
}

func (f *fakeRemoteView) ListAdmittedWorkloads(_ context.Context, clusterName, clusterQueue string) ([]kueue.Workload, error) {
	f.mu.Lock()
	defer f.mu.Unlock()
	out := make([]kueue.Workload, len(f.admittedWLs[clusterName+"/"+clusterQueue]))
	copy(out, f.admittedWLs[clusterName+"/"+clusterQueue])
	return out, nil
}

// fakeEvictor records every claim-and-evict call.
type fakeEvictor struct {
	mu             sync.Mutex
	calls          []evictCall
	alreadyClaimed map[string]bool
}

type evictCall struct {
	ClusterName     string
	VictimNamespace string
	VictimName      string
	IncomingNS      string
	IncomingName    string
}

func newFakeEvictor() *fakeEvictor {
	return &fakeEvictor{alreadyClaimed: map[string]bool{}}
}

func (e *fakeEvictor) ClaimAndEvict(_ context.Context, clusterName, victimNamespace, victimName, incomingNamespace, incomingName string) error {
	e.mu.Lock()
	defer e.mu.Unlock()
	if e.alreadyClaimed[clusterName+"/"+victimNamespace+"/"+victimName] {
		return ErrVictimAlreadyClaimed
	}
	e.calls = append(e.calls, evictCall{clusterName, victimNamespace, victimName, incomingNamespace, incomingName})
	return nil
}

// makeMultiKueueACState returns a Pending MultiKueue admission check state.
func makeMultiKueueACState(name string) *kueue.AdmissionCheckState {
	return &kueue.AdmissionCheckState{
		Name:  kueue.AdmissionCheckReference(name),
		State: kueue.CheckStatePending,
	}
}

// makeIncoming builds a high-priority workload arriving at the manager.
// The manager-side ClusterQueue is what's named in cqName.
func makeIncoming(name, cqName string, prio int32, acName string) *kueue.Workload {
	now := time.Now()
	w := utiltestingapi.MakeWorkload(name, metav1.NamespaceDefault).
		AdmissionChecks(*makeMultiKueueACState(acName)).
		ReserveQuotaAt(utiltestingapi.MakeAdmission(kueue.ClusterQueueReference(cqName)).Obj(), now).
		Obj()
	w.Spec.Priority = ptrInt32(prio)
	return w
}

// makeAdmittedVictim builds an admitted workload running on a worker, in the given CQ.
func makeAdmittedVictim(name, cqName string, prio int32) kueue.Workload {
	now := time.Now()
	w := utiltestingapi.MakeWorkload(name, metav1.NamespaceDefault).
		Label(kueue.MultiKueueOriginLabel, "multikueue").
		ReserveQuotaAt(utiltestingapi.MakeAdmission(kueue.ClusterQueueReference(cqName)).Obj(), now).
		AdmittedAt(true, now).
		Obj()
	w.Spec.Priority = ptrInt32(prio)
	return *w
}

// addAC registers an AdmissionCheck CR + MultiKueueConfig on the fake client.
func addAC(t *testing.T, builder *fake.ClientBuilder, acName, configName string, clusters ...string) {
	t.Helper()
	builder.WithObjects(
		utiltestingapi.MakeAdmissionCheck(acName).
			ControllerName(kueue.MultiKueueControllerName).
			Parameters(kueue.GroupVersion.Group, "MultiKueueConfig", configName).
			Active(metav1.ConditionTrue).
			Obj(),
		utiltestingapi.MakeMultiKueueConfig(configName).Clusters(clusters...).Obj(),
	)
}

// addManagerCQ registers a manager-side ClusterQueue with the given cohort name.
func addManagerCQ(t *testing.T, builder *fake.ClientBuilder, cqName, cohortName string) {
	t.Helper()
	cq := utiltestingapi.MakeClusterQueue(cqName).Obj()
	cq.Spec.CohortName = kueue.CohortReference(cohortName)
	builder.WithObjects(cq)
}

// addManagerCQWithBorrowState builds the manager-side ClusterQueue with the
// given cohort name + preemption.borrowWithinCohort policy and seeds its
// FlavorsReservation so that the dispatcher's "preemptor would borrow"
// computation reads `reservedCPU` against `nominalCPU`. Used to exercise the
// BorrowWithinCohort gate.
func addManagerCQWithBorrowState(t *testing.T, builder *fake.ClientBuilder, cqName, cohortName string, preemption *kueue.ClusterQueuePreemption, nominalCPU, reservedCPU int64) {
	t.Helper()
	cq := utiltestingapi.MakeClusterQueue(cqName).Obj()
	cq.Spec.CohortName = kueue.CohortReference(cohortName)
	cq.Spec.Preemption = preemption
	cq.Spec.ResourceGroups = []kueue.ResourceGroup{{
		CoveredResources: []corev1.ResourceName{corev1.ResourceCPU},
		Flavors: []kueue.FlavorQuotas{{
			Name: "default-flavor",
			Resources: []kueue.ResourceQuota{{
				Name:         corev1.ResourceCPU,
				NominalQuota: *resource.NewQuantity(nominalCPU, resource.DecimalSI),
			}},
		}},
	}}
	cq.Status.FlavorsReservation = []kueue.FlavorUsage{{
		Name: "default-flavor",
		Resources: []kueue.ResourceUsage{{
			Name:  corev1.ResourceCPU,
			Total: *resource.NewQuantity(reservedCPU, resource.DecimalSI),
		}},
	}}
	builder.WithObjects(cq)
}

func newScheme(t *testing.T) *runtime.Scheme {
	t.Helper()
	s := runtime.NewScheme()
	if err := kueue.AddToScheme(s); err != nil {
		t.Fatal(err)
	}
	return s
}

func runReconcile(t *testing.T, c client.Client, view RemoteView, evictor Evictor, wlKey types.NamespacedName) *kueue.Workload {
	t.Helper()
	helper, err := admissioncheck.NewMultiKueueStoreHelper(c)
	if err != nil {
		t.Fatal(err)
	}
	r := NewCrossClusterPreemptionDispatcherReconciler(c, helper, view, evictor, nil)
	r.clock = testingclock.NewFakeClock(time.Now())
	if _, err := r.Reconcile(context.Background(), ctrl.Request{NamespacedName: wlKey}); err != nil {
		t.Fatalf("reconcile: %v", err)
	}
	got := &kueue.Workload{}
	if err := c.Get(context.Background(), wlKey, got); err != nil {
		t.Fatal(err)
	}
	return got
}

func TestCrossClusterPreemption_FallbackWhenManagerCQHasNoCohort(t *testing.T) {
	const cqName, wlName, acName, cfgName = "gpu-cq", "test-wl", "ac", "cfg"

	wl := makeIncoming(wlName, cqName, 0, acName)
	scheme := newScheme(t)
	builder := fake.NewClientBuilder().WithScheme(scheme).WithStatusSubresource(&kueue.Workload{}).WithObjects(wl)
	addAC(t, builder, acName, cfgName, "worker1", "worker2")
	// Manager CQ exists but has no cohortName → fall back to all-at-once.
	builder.WithObjects(utiltestingapi.MakeClusterQueue(cqName).Obj())
	c := builder.Build()

	view := newFakeRemoteView()
	evictor := newFakeEvictor()

	got := runReconcile(t, c, view, evictor, client.ObjectKeyFromObject(wl))

	wantNominated := []string{"worker1", "worker2"}
	gotNominated := append([]string(nil), got.Status.NominatedClusterNames...)
	sort.Strings(gotNominated)
	if diff := cmp.Diff(wantNominated, gotNominated); diff != "" {
		t.Errorf("NominatedClusterNames diff (-want +got):\n%s", diff)
	}
	if len(evictor.calls) != 0 {
		t.Errorf("no eviction expected when manager CQ has no cohortName; got %d", len(evictor.calls))
	}
}

func TestCrossClusterPreemption_HappyPath(t *testing.T) {
	const cqName, wlName, acName, cfgName = "gpu-cq", "high-pri", "ac", "cfg"
	const cohortName = "shared-gpu"

	wl := makeIncoming(wlName, cqName, 100, acName)
	scheme := newScheme(t)
	builder := fake.NewClientBuilder().WithScheme(scheme).WithStatusSubresource(&kueue.Workload{}).WithObjects(wl)
	addAC(t, builder, acName, cfgName, "worker1", "worker2")
	addManagerCQ(t, builder, cqName, cohortName)
	c := builder.Build()

	view := newFakeRemoteView()
	// Worker CQ on worker1 is in the cohort and allows reclaim.
	view.addMemberCQ("worker1", "worker1-cq", cohortName, kueue.PreemptionPolicyLowerPriority)
	view.addMemberCQ("worker2", "worker2-cq", cohortName, kueue.PreemptionPolicyLowerPriority)
	view.addAdmitted("worker1", "worker1-cq", makeAdmittedVictim("low-pri", "worker1-cq", 10))

	evictor := newFakeEvictor()

	got := runReconcile(t, c, view, evictor, client.ObjectKeyFromObject(wl))

	if len(evictor.calls) != 1 {
		t.Fatalf("want 1 evict call, got %d (%+v)", len(evictor.calls), evictor.calls)
	}
	wantCall := evictCall{ClusterName: "worker1", VictimNamespace: metav1.NamespaceDefault, VictimName: "low-pri", IncomingNS: metav1.NamespaceDefault, IncomingName: wlName}
	if diff := cmp.Diff(wantCall, evictor.calls[0]); diff != "" {
		t.Errorf("evict call diff (-want +got):\n%s", diff)
	}
	if diff := cmp.Diff([]string{"worker1"}, got.Status.NominatedClusterNames, cmpopts.EquateEmpty()); diff != "" {
		t.Errorf("NominatedClusterNames diff (-want +got):\n%s", diff)
	}
}

func TestCrossClusterPreemption_NoVictim_FallsBackToAllAtOnceOverCohort(t *testing.T) {
	const cqName, wlName, acName, cfgName = "gpu-cq", "low-pri-incoming", "ac", "cfg"
	const cohortName = "shared-gpu"

	wl := makeIncoming(wlName, cqName, 5, acName)
	scheme := newScheme(t)
	builder := fake.NewClientBuilder().WithScheme(scheme).WithStatusSubresource(&kueue.Workload{}).WithObjects(wl)
	addAC(t, builder, acName, cfgName, "worker1", "worker2")
	addManagerCQ(t, builder, cqName, cohortName)
	c := builder.Build()

	view := newFakeRemoteView()
	view.addMemberCQ("worker1", "worker1-cq", cohortName, kueue.PreemptionPolicyLowerPriority)
	view.addMemberCQ("worker2", "worker2-cq", cohortName, kueue.PreemptionPolicyLowerPriority)
	// worker1 has a higher-priority workload (50) — not preemptible by us (5 < 50).
	view.addAdmitted("worker1", "worker1-cq", makeAdmittedVictim("running-high", "worker1-cq", 50))

	evictor := newFakeEvictor()

	got := runReconcile(t, c, view, evictor, client.ObjectKeyFromObject(wl))

	if len(evictor.calls) != 0 {
		t.Errorf("expected no evictions; got %+v", evictor.calls)
	}
	wantNominated := []string{"worker1", "worker2"}
	gotNominated := append([]string(nil), got.Status.NominatedClusterNames...)
	sort.Strings(gotNominated)
	if diff := cmp.Diff(wantNominated, gotNominated); diff != "" {
		t.Errorf("NominatedClusterNames diff (-want +got):\n%s", diff)
	}
}

func TestCrossClusterPreemption_PicksLowestPriorityVictim(t *testing.T) {
	const cqName, wlName, acName, cfgName = "gpu-cq", "incoming", "ac", "cfg"
	const cohortName = "shared-gpu"

	wl := makeIncoming(wlName, cqName, 100, acName)
	scheme := newScheme(t)
	builder := fake.NewClientBuilder().WithScheme(scheme).WithStatusSubresource(&kueue.Workload{}).WithObjects(wl)
	addAC(t, builder, acName, cfgName, "worker1", "worker2")
	addManagerCQ(t, builder, cqName, cohortName)
	c := builder.Build()

	view := newFakeRemoteView()
	view.addMemberCQ("worker1", "worker1-cq", cohortName, kueue.PreemptionPolicyLowerPriority)
	view.addMemberCQ("worker2", "worker2-cq", cohortName, kueue.PreemptionPolicyLowerPriority)
	view.addAdmitted("worker1", "worker1-cq", makeAdmittedVictim("mid-pri", "worker1-cq", 50))
	view.addAdmitted("worker2", "worker2-cq", makeAdmittedVictim("low-pri", "worker2-cq", 10))

	evictor := newFakeEvictor()

	_ = runReconcile(t, c, view, evictor, client.ObjectKeyFromObject(wl))

	if len(evictor.calls) != 1 {
		t.Fatalf("want 1 evict, got %d", len(evictor.calls))
	}
	if got := evictor.calls[0].VictimName; got != "low-pri" {
		t.Errorf("expected lowest-priority victim 'low-pri', got %q", got)
	}
	if got := evictor.calls[0].ClusterName; got != "worker2" {
		t.Errorf("expected nomination on worker2, got %q", got)
	}
}

func TestCrossClusterPreemption_AlreadyClaimedRetriesNext(t *testing.T) {
	const cqName, wlName, acName, cfgName = "gpu-cq", "incoming", "ac", "cfg"
	const cohortName = "shared-gpu"

	wl := makeIncoming(wlName, cqName, 100, acName)
	scheme := newScheme(t)
	builder := fake.NewClientBuilder().WithScheme(scheme).WithStatusSubresource(&kueue.Workload{}).WithObjects(wl)
	addAC(t, builder, acName, cfgName, "worker1", "worker2")
	addManagerCQ(t, builder, cqName, cohortName)
	c := builder.Build()

	low := makeAdmittedVictim("low-pri", "worker1-cq", 10)
	low.Annotations = map[string]string{
		constants.MultiKueueCrossClusterPreemptionVictimAnnotation: "other/some-other-wl",
	}
	mid := makeAdmittedVictim("mid-pri", "worker2-cq", 50)

	view := newFakeRemoteView()
	view.addMemberCQ("worker1", "worker1-cq", cohortName, kueue.PreemptionPolicyLowerPriority)
	view.addMemberCQ("worker2", "worker2-cq", cohortName, kueue.PreemptionPolicyLowerPriority)
	view.addAdmitted("worker1", "worker1-cq", low)
	view.addAdmitted("worker2", "worker2-cq", mid)

	evictor := newFakeEvictor()

	_ = runReconcile(t, c, view, evictor, client.ObjectKeyFromObject(wl))

	if len(evictor.calls) != 1 {
		t.Fatalf("want 1 evict (mid), got %d", len(evictor.calls))
	}
	if got := evictor.calls[0].VictimName; got != "mid-pri" {
		t.Errorf("expected to skip already-claimed low-pri and pick mid-pri, got %q", got)
	}
}

// New: per-CQ preemption policy is honored. A CQ with ReclaimWithinCohort=Never
// is excluded from the candidate set, so its low-priority workload is NOT a victim.
func TestCrossClusterPreemption_HonorsReclaimWithinCohortNever(t *testing.T) {
	const cqName, wlName, acName, cfgName = "gpu-cq", "incoming", "ac", "cfg"
	const cohortName = "shared-gpu"

	wl := makeIncoming(wlName, cqName, 100, acName)
	scheme := newScheme(t)
	builder := fake.NewClientBuilder().WithScheme(scheme).WithStatusSubresource(&kueue.Workload{}).WithObjects(wl)
	addAC(t, builder, acName, cfgName, "worker1", "worker2")
	addManagerCQ(t, builder, cqName, cohortName)
	c := builder.Build()

	view := newFakeRemoteView()
	// worker1 CQ has Never policy — its workloads should NOT be victim candidates.
	view.addMemberCQ("worker1", "worker1-cq", cohortName, kueue.PreemptionPolicyNever)
	view.addMemberCQ("worker2", "worker2-cq", cohortName, kueue.PreemptionPolicyLowerPriority)
	// Both workers have a low-pri running workload, but only worker2 should be eligible.
	view.addAdmitted("worker1", "worker1-cq", makeAdmittedVictim("protected", "worker1-cq", 1))
	view.addAdmitted("worker2", "worker2-cq", makeAdmittedVictim("preemptible", "worker2-cq", 10))

	evictor := newFakeEvictor()

	_ = runReconcile(t, c, view, evictor, client.ObjectKeyFromObject(wl))

	if len(evictor.calls) != 1 {
		t.Fatalf("want exactly 1 evict (preemptible from worker2), got %+v", evictor.calls)
	}
	if got := evictor.calls[0].VictimName; got != "preemptible" {
		t.Errorf("expected to skip protected (Never policy) and evict preemptible, got %q", got)
	}
	if got := evictor.calls[0].ClusterName; got != "worker2" {
		t.Errorf("expected eviction on worker2, got %q", got)
	}
}

// New: ReclaimWithinCohort=Any allows preemption even at equal priority.
func TestCrossClusterPreemption_HonorsReclaimWithinCohortAny(t *testing.T) {
	const cqName, wlName, acName, cfgName = "gpu-cq", "incoming", "ac", "cfg"
	const cohortName = "shared-gpu"

	wl := makeIncoming(wlName, cqName, 50, acName)
	scheme := newScheme(t)
	builder := fake.NewClientBuilder().WithScheme(scheme).WithStatusSubresource(&kueue.Workload{}).WithObjects(wl)
	addAC(t, builder, acName, cfgName, "worker1")
	addManagerCQ(t, builder, cqName, cohortName)
	c := builder.Build()

	view := newFakeRemoteView()
	// Any policy: even equal-priority workloads are preemptible.
	view.addMemberCQ("worker1", "worker1-cq", cohortName, kueue.PreemptionPolicyAny)
	view.addAdmitted("worker1", "worker1-cq", makeAdmittedVictim("equal-pri", "worker1-cq", 50))

	evictor := newFakeEvictor()

	_ = runReconcile(t, c, view, evictor, client.ObjectKeyFromObject(wl))

	if len(evictor.calls) != 1 {
		t.Fatalf("want 1 evict (equal-pri allowed by Any), got %d", len(evictor.calls))
	}
	if got := evictor.calls[0].VictimName; got != "equal-pri" {
		t.Errorf("expected to evict equal-priority victim under Any policy, got %q", got)
	}
}

// New: a victim CQ that is at-or-below its nominal quota (not borrowing) is
// NOT eligible for cross-cohort reclaim, even when ReclaimWithinCohort=Any.
// Mirrors single-cluster cqIsBorrowing-gated reclaim semantics.
func TestCrossClusterPreemption_SkipsNonBorrowingCQ(t *testing.T) {
	const cqName, wlName, acName, cfgName = "gpu-cq", "incoming", "ac", "cfg"
	const cohortName = "shared-gpu"

	wl := makeIncoming(wlName, cqName, 100, acName)
	scheme := newScheme(t)
	builder := fake.NewClientBuilder().WithScheme(scheme).WithStatusSubresource(&kueue.Workload{}).WithObjects(wl)
	addAC(t, builder, acName, cfgName, "worker1", "worker2")
	addManagerCQ(t, builder, cqName, cohortName)
	c := builder.Build()

	view := newFakeRemoteView()
	// worker1 CQ: at-or-below nominal (usage 5, nominal 5) — NOT borrowing.
	view.addMemberCQWithQuota("worker1", "worker1-cq", cohortName,
		kueue.PreemptionPolicyAny, 5, 5)
	// worker2 CQ: borrowing (usage 10, nominal 1).
	view.addMemberCQWithQuota("worker2", "worker2-cq", cohortName,
		kueue.PreemptionPolicyAny, 1, 10)
	view.addAdmitted("worker1", "worker1-cq", makeAdmittedVictim("owned-by-w1", "worker1-cq", 10))
	view.addAdmitted("worker2", "worker2-cq", makeAdmittedVictim("borrowing-on-w2", "worker2-cq", 10))

	evictor := newFakeEvictor()

	_ = runReconcile(t, c, view, evictor, client.ObjectKeyFromObject(wl))

	if len(evictor.calls) != 1 {
		t.Fatalf("want 1 evict (the borrower), got %d", len(evictor.calls))
	}
	if got := evictor.calls[0].VictimName; got != "borrowing-on-w2" {
		t.Errorf("expected to evict from the borrowing CQ on worker2, got %q", got)
	}
	if got := evictor.calls[0].ClusterName; got != "worker2" {
		t.Errorf("expected eviction on worker2, got %q", got)
	}
}

// New: when admitting the incoming workload would leave the manager-side CQ
// above its nominal quota AND the manager CQ has no BorrowWithinCohort
// policy (Never default), the dispatcher must NOT preempt — that would be
// "preempt while borrowing" which the policy forbids.
func TestCrossClusterPreemption_BorrowWithinCohortNeverBlocksPreemption(t *testing.T) {
	const cqName, wlName, acName, cfgName = "gpu-cq", "incoming", "ac", "cfg"
	const cohortName = "shared-gpu"

	wl := makeIncoming(wlName, cqName, 100, acName)
	scheme := newScheme(t)
	builder := fake.NewClientBuilder().WithScheme(scheme).WithStatusSubresource(&kueue.Workload{}).WithObjects(wl)
	addAC(t, builder, acName, cfgName, "worker1")
	// Manager CQ: Reservation 5 > Nominal 1 → preemptor would borrow.
	// Preemption policy: ReclaimWithinCohort allowed but BorrowWithinCohort=nil (Never).
	addManagerCQWithBorrowState(t, builder, cqName, cohortName, &kueue.ClusterQueuePreemption{
		ReclaimWithinCohort: kueue.PreemptionPolicyLowerPriority,
	}, 1, 5)
	c := builder.Build()

	view := newFakeRemoteView()
	view.addMemberCQ("worker1", "worker1-cq", cohortName, kueue.PreemptionPolicyLowerPriority)
	view.addAdmitted("worker1", "worker1-cq", makeAdmittedVictim("low-pri", "worker1-cq", 10))

	evictor := newFakeEvictor()

	_ = runReconcile(t, c, view, evictor, client.ObjectKeyFromObject(wl))

	if len(evictor.calls) != 0 {
		t.Fatalf("expected 0 evicts (BorrowWithinCohort=Never blocks preempt-while-borrowing), got %d", len(evictor.calls))
	}
}

// New: when manager CQ would borrow AND BorrowWithinCohort.Policy=LowerPriority
// AND incoming priority > victim priority, preemption proceeds.
func TestCrossClusterPreemption_BorrowWithinCohortLowerPriorityAllowsBelowVictim(t *testing.T) {
	const cqName, wlName, acName, cfgName = "gpu-cq", "incoming", "ac", "cfg"
	const cohortName = "shared-gpu"

	wl := makeIncoming(wlName, cqName, 100, acName)
	scheme := newScheme(t)
	builder := fake.NewClientBuilder().WithScheme(scheme).WithStatusSubresource(&kueue.Workload{}).WithObjects(wl)
	addAC(t, builder, acName, cfgName, "worker1")
	addManagerCQWithBorrowState(t, builder, cqName, cohortName, &kueue.ClusterQueuePreemption{
		ReclaimWithinCohort: kueue.PreemptionPolicyLowerPriority,
		BorrowWithinCohort: &kueue.BorrowWithinCohort{
			Policy: kueue.BorrowWithinCohortPolicyLowerPriority,
		},
	}, 1, 5)
	c := builder.Build()

	view := newFakeRemoteView()
	view.addMemberCQ("worker1", "worker1-cq", cohortName, kueue.PreemptionPolicyLowerPriority)
	view.addAdmitted("worker1", "worker1-cq", makeAdmittedVictim("low-pri", "worker1-cq", 10))

	evictor := newFakeEvictor()

	_ = runReconcile(t, c, view, evictor, client.ObjectKeyFromObject(wl))

	if len(evictor.calls) != 1 {
		t.Fatalf("want 1 evict (BorrowWithinCohort=LowerPriority lets us borrow against lower-pri victim), got %d", len(evictor.calls))
	}
	if got := evictor.calls[0].VictimName; got != "low-pri" {
		t.Errorf("expected to evict low-pri victim, got %q", got)
	}
}

// New: cross-cluster preemption is for cross-CQ reclaim within a cohort.
// The incoming workload's own ClusterQueue must not be considered as a
// victim source (within-CQ preemption is the worker's local
// `WithinClusterQueue` policy concern, not this dispatcher's).
func TestCrossClusterPreemption_SkipsIncomingWorkloadOwnCQ(t *testing.T) {
	const cqName, wlName, acName, cfgName = "shared-cq", "incoming", "ac", "cfg"
	const cohortName = "shared-cohort"

	wl := makeIncoming(wlName, cqName, 100, acName)
	scheme := newScheme(t)
	builder := fake.NewClientBuilder().WithScheme(scheme).WithStatusSubresource(&kueue.Workload{}).WithObjects(wl)
	addAC(t, builder, acName, cfgName, "worker1")
	addManagerCQ(t, builder, cqName, cohortName)
	c := builder.Build()

	view := newFakeRemoteView()
	// Worker has the SAME-named CQ as the incoming, with `Any` policy and
	// borrowing state. Without the same-CQ skip, the dispatcher would
	// happily evict same-CQ workloads.
	view.addMemberCQ("worker1", cqName, cohortName, kueue.PreemptionPolicyAny)
	view.addAdmitted("worker1", cqName, makeAdmittedVictim("same-cq-sibling", cqName, 50))

	evictor := newFakeEvictor()
	_ = runReconcile(t, c, view, evictor, client.ObjectKeyFromObject(wl))

	if len(evictor.calls) != 0 {
		t.Fatalf("expected 0 evicts (incoming's own CQ must not be a victim source), got %d", len(evictor.calls))
	}
}

// New: when no preemption candidate is found and multiple cohort-member
// CQs share a worker cluster (e.g. per-tenant CQs in the same cohort),
// the all-at-once fallback must NOT write duplicate cluster names to
// NominatedClusterNames.
func TestCrossClusterPreemption_FallbackDedupsClusterNames(t *testing.T) {
	const cqName, wlName, acName, cfgName = "manager-cq", "incoming", "ac", "cfg"
	const cohortName = "shared-cohort"

	wl := makeIncoming(wlName, cqName, 100, acName)
	scheme := newScheme(t)
	builder := fake.NewClientBuilder().WithScheme(scheme).WithStatusSubresource(&kueue.Workload{}).WithObjects(wl)
	addAC(t, builder, acName, cfgName, "worker1", "worker2")
	addManagerCQ(t, builder, cqName, cohortName)
	c := builder.Build()

	view := newFakeRemoteView()
	// Each worker has TWO cohort-member CQs (e.g. per-tenant CQs sharing a
	// cohort). None are borrowing → no candidates → fall back to
	// all-at-once nomination over cohort cluster set.
	view.addMemberCQWithQuota("worker1", "tenant-a-cq", cohortName,
		kueue.PreemptionPolicyAny, 5, 0) // not borrowing
	view.addMemberCQWithQuota("worker1", "tenant-b-cq", cohortName,
		kueue.PreemptionPolicyAny, 5, 0) // not borrowing
	view.addMemberCQWithQuota("worker2", "tenant-a-cq", cohortName,
		kueue.PreemptionPolicyAny, 5, 0) // not borrowing
	view.addMemberCQWithQuota("worker2", "tenant-b-cq", cohortName,
		kueue.PreemptionPolicyAny, 5, 0) // not borrowing

	evictor := newFakeEvictor()
	got := runReconcile(t, c, view, evictor, client.ObjectKeyFromObject(wl))

	if len(evictor.calls) != 0 {
		t.Fatalf("expected no evicts (no borrowers), got %d", len(evictor.calls))
	}
	want := []string{"worker1", "worker2"}
	sort.Strings(got.Status.NominatedClusterNames)
	if !cmp.Equal(got.Status.NominatedClusterNames, want, cmpopts.EquateEmpty()) {
		t.Errorf("expected NominatedClusterNames=%v (deduped), got %v",
			want, got.Status.NominatedClusterNames)
	}
}

func ptrInt32(v int32) *int32 { return &v }
