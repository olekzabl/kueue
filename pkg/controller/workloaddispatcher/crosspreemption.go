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

// Package workloaddispatcher (crosspreemption.go) implements the
// cross-cluster-preemption MultiKueue dispatcher.
//
// Activation:
//   - Set Configuration.MultiKueue.DispatcherName to
//     `kueue.x-k8s.io/multikueue-dispatcher-cross-cluster-preemption`.
//   - Enable the `MultiKueueCrossClusterPreemption` feature gate.
//   - Set `spec.cohortName` on the manager-side ClusterQueue and on the
//     desired worker ClusterQueues — this defines cohort membership the
//     same way as single-cluster Cohort does.
//
// Algorithm (per Workload reconcile):
//  1. Gate: only act if MultiKueue admission check is Pending and workload
//     has quota reserved on the manager.
//  2. Look up the workload's manager-side ClusterQueue and read its
//     spec.cohortName + full Spec.Preemption + Status.FlavorsReservation.
//     If cohortName is empty, fall back to nominating all configured
//     remote clusters (preserves all-at-once behavior for non-cohort CQs).
//  3. Discover cohort members across configured worker clusters via
//     RemoteView.FindCohortMembers (groups worker CQs by spec.cohortName).
//  4. Same-CQ skip: exclude cohort members whose CQ name equals the
//     incoming workload's home CQ name. Cross-cluster preemption is for
//     cross-CQ reclaim within a cohort; within-CQ preemption is the
//     worker's local `WithinClusterQueue` policy concern.
//  5. For each remaining member, exclude CQs that opt out via
//     `Spec.Preemption.ReclaimWithinCohort=Never` AND CQs that are not
//     currently borrowing cohort capacity (cqIsBorrowing); only borrowers
//     are eligible victim sources. Then list admitted workloads on the
//     remaining CQs and apply the policy gate
//     (ReclaimWithinCohort=LowerPriority requires victim.priority <
//     incoming.priority; ReclaimWithinCohort=Any allows any priority).
//  6. If admitting the incoming workload would leave the manager-side CQ
//     above its nominal quota, gate by `Spec.Preemption.BorrowWithinCohort`
//     on the manager CQ — only proceed when policy=LowerPriority and the
//     victim's priority is strictly below the incoming priority and at or
//     below `MaxPriorityThreshold` (when set).
//  7. Filter out victims already claimed by another incoming workload.
//  8. Across members, pick the lowest-priority victim (creation-time tiebreak).
//  9. ClaimAndEvict the victim. On ErrVictimAlreadyClaimed, retry with
//     the next candidate.
// 10. Set Status.NominatedClusterNames to the freed cluster.
// 11. If no candidate exists, fall back to nominating all cohort members
//     (a worker with free capacity could still admit naturally).
package workloaddispatcher

import (
	"context"
	"fmt"
	"sort"

	apierrors "k8s.io/apimachinery/pkg/api/errors"
	"k8s.io/apimachinery/pkg/types"
	"k8s.io/utils/clock"
	ctrl "sigs.k8s.io/controller-runtime"
	"sigs.k8s.io/controller-runtime/pkg/client"
	"sigs.k8s.io/controller-runtime/pkg/reconcile"

	kueueconfig "sigs.k8s.io/kueue/apis/config/v1beta2"
	kueue "sigs.k8s.io/kueue/apis/kueue/v1beta2"
	"sigs.k8s.io/kueue/pkg/controller/constants"
	"sigs.k8s.io/kueue/pkg/controller/core"
	"sigs.k8s.io/kueue/pkg/util/admissioncheck"
	"sigs.k8s.io/kueue/pkg/util/roletracker"
	"sigs.k8s.io/kueue/pkg/workload"
)

// CrossClusterPreemptionDispatcherControllerName is the controller name
// surfaced in logs and metrics.
const CrossClusterPreemptionDispatcherControllerName = "multikueue_cross_cluster_preemption_dispatcher"

// CrossClusterPreemptionDispatcherReconciler is the controller-runtime
// reconciler for the cross-cluster-preemption dispatcher.
type CrossClusterPreemptionDispatcherReconciler struct {
	client      client.Client
	helper      *admissioncheck.MultiKueueStoreHelper
	view        RemoteView
	evictor     Evictor
	clock       clock.Clock
	roleTracker *roletracker.RoleTracker
}

var _ reconcile.Reconciler = (*CrossClusterPreemptionDispatcherReconciler)(nil)

// NewCrossClusterPreemptionDispatcherReconciler constructs a new dispatcher
// reconciler.
func NewCrossClusterPreemptionDispatcherReconciler(
	c client.Client,
	helper *admissioncheck.MultiKueueStoreHelper,
	view RemoteView,
	evictor Evictor,
	roleTracker *roletracker.RoleTracker,
) *CrossClusterPreemptionDispatcherReconciler {
	return &CrossClusterPreemptionDispatcherReconciler{
		client:      c,
		helper:      helper,
		view:        view,
		evictor:     evictor,
		clock:       realClock,
		roleTracker: roleTracker,
	}
}

// SetupWithManager registers this reconciler with the controller-runtime manager.
func (r *CrossClusterPreemptionDispatcherReconciler) SetupWithManager(mgr ctrl.Manager, cfg *kueueconfig.Configuration) error {
	return ctrl.NewControllerManagedBy(mgr).
		Named(CrossClusterPreemptionDispatcherControllerName).
		For(&kueue.Workload{}).
		WithLogConstructor(roletracker.NewLogConstructor(r.roleTracker, CrossClusterPreemptionDispatcherControllerName)).
		Complete(core.WithLeadingManager(mgr, r, &kueue.Workload{}, cfg))
}

// Reconcile drives cross-cluster-preemption dispatch for a Workload.
func (r *CrossClusterPreemptionDispatcherReconciler) Reconcile(ctx context.Context, req ctrl.Request) (ctrl.Result, error) {
	log := ctrl.LoggerFrom(ctx)
	wl := &kueue.Workload{}
	if err := r.client.Get(ctx, req.NamespacedName, wl); err != nil {
		if apierrors.IsNotFound(err) {
			return reconcile.Result{}, nil
		}
		log.Error(err, "Failed to retrieve Workload")
		return reconcile.Result{}, err
	}

	if !wl.DeletionTimestamp.IsZero() {
		return reconcile.Result{}, nil
	}

	mkAc, err := admissioncheck.GetMultiKueueAdmissionCheck(ctx, r.client, wl)
	if err != nil {
		log.Error(err, "Cannot get MultiKueue AdmissionCheckState")
		return reconcile.Result{}, err
	}
	if mkAc == nil || mkAc.State != kueue.CheckStatePending {
		return reconcile.Result{}, nil
	}
	if wl.Status.ClusterName != nil {
		return reconcile.Result{}, nil
	}
	if workload.IsFinished(wl) || !workload.HasQuotaReservation(wl) {
		return reconcile.Result{}, nil
	}

	// Read the manager-side CQ to discover the cohort name. Mirrors the
	// single-cluster pattern: cohort membership is via CQ.spec.cohortName.
	homeCQName := string(wl.Status.Admission.ClusterQueue)
	if homeCQName == "" {
		log.V(3).Info("workload has no admitted ClusterQueue, skip")
		return reconcile.Result{}, nil
	}

	remoteClusters, err := admissioncheck.GetRemoteClusters(ctx, r.helper, mkAc.Name)
	if err != nil {
		log.Error(err, "Cannot resolve remote clusters for workload")
		return reconcile.Result{}, err
	}
	if remoteClusters.Len() == 0 {
		log.V(3).Info("no remote clusters configured, skip")
		return reconcile.Result{}, nil
	}

	if len(wl.Status.NominatedClusterNames) > 0 {
		// Already nominated by a previous reconcile.
		return reconcile.Result{}, nil
	}

	cohortName, managerCQ, err := r.lookupHomeCQ(ctx, homeCQName)
	if err != nil {
		log.Error(err, "lookup home ClusterQueue", "cq", homeCQName)
		return reconcile.Result{}, err
	}
	if cohortName == "" {
		// Manager CQ has no cohortName — fall back to all-at-once.
		log.V(3).Info("manager ClusterQueue has no cohortName, falling back to all-at-once",
			"cq", homeCQName)
		return r.nominate(ctx, wl, remoteClusters.UnsortedList())
	}

	members, err := r.view.FindCohortMembers(ctx, cohortName, remoteClusters.UnsortedList())
	if err != nil {
		log.Error(err, "discover cohort members", "cohort", cohortName)
		return reconcile.Result{}, err
	}

	if len(members) == 0 {
		// No worker CQ in this cohort yet — fall back to all-at-once.
		log.V(3).Info("no worker ClusterQueue references this cohort, falling back to all-at-once",
			"cohort", cohortName)
		return r.nominate(ctx, wl, remoteClusters.UnsortedList())
	}

	incomingPrio := workloadPriority(wl)
	incomingClaim := fmt.Sprintf("%s/%s", wl.Namespace, wl.Name)
	frResources := frResourcesForWorkload(wl)
	managerBorrowing := preemptorWouldBorrow(managerCQ, frResources)
	managerAllowsBorrow := cqAllowsBorrow(managerCQ)

	type candidate struct {
		clusterName string
		victim      kueue.Workload
	}
	candidates := make([]candidate, 0)
	for _, m := range members {
		// Skip the incoming workload's own ClusterQueue. Cross-cluster
		// preemption is for cross-CQ reclaim within a cohort
		// (ReclaimWithinCohort); within-CQ preemption is a separate concern
		// handled by the worker's local scheduler via the CQ's
		// WithinClusterQueue policy.
		if m.ClusterQueue.Name == homeCQName {
			log.V(4).Info("skipping cohort member; same CQ as incoming workload (within-CQ preemption not in scope)",
				"cluster", m.ClusterName, "cq", m.ClusterQueue.Name)
			continue
		}

		// Honor the worker CQ's preemption policy. ReclaimWithinCohort=Never
		// means this CQ never participates as a victim source.
		if !cqAllowsCrossCohortReclaim(&m.ClusterQueue) {
			log.V(4).Info("skipping cohort member; preemption policy disallows cross-cohort reclaim",
				"cluster", m.ClusterName, "cq", m.ClusterQueue.Name)
			continue
		}

		// Quota-based reclaim parity with single-cluster Kueue: a victim CQ
		// is eligible only if it is currently borrowing cohort capacity for
		// at least one resource the incoming workload requests. CQs at-or-
		// below their nominal quota own that quota and must not be evicted
		// to satisfy a sibling.
		if !cqIsBorrowing(&m.ClusterQueue, frResources) {
			log.V(4).Info("skipping cohort member; CQ is at-or-below nominal (not borrowing)",
				"cluster", m.ClusterName, "cq", m.ClusterQueue.Name)
			continue
		}

		victims, err := r.view.ListAdmittedWorkloads(ctx, m.ClusterName, m.ClusterQueue.Name)
		if err != nil {
			log.Error(err, "list admitted workloads on remote", "cluster", m.ClusterName, "cq", m.ClusterQueue.Name)
			continue
		}
		for _, v := range victims {
			if !canPreempt(&m.ClusterQueue, incomingPrio, &v) {
				continue
			}
			// BorrowWithinCohort gate: if admitting the incoming workload
			// would leave the manager-side CQ above its nominal quota, the
			// preemption is "preempt while borrowing". Single-cluster Kueue
			// rejects this unless BorrowWithinCohort.Policy=LowerPriority
			// (with optional MaxPriorityThreshold). Same gate applied here.
			if managerBorrowing {
				if !managerAllowsBorrow {
					continue
				}
				if !canBorrowAgainstVictim(managerCQ, incomingPrio, workloadPriority(&v)) {
					continue
				}
			}
			if existing, ok := v.Annotations[constants.MultiKueueCrossClusterPreemptionVictimAnnotation]; ok && existing != incomingClaim {
				continue
			}
			candidates = append(candidates, candidate{clusterName: m.ClusterName, victim: v})
		}
	}

	if len(candidates) == 0 {
		log.V(3).Info("no preemption victim found, falling back to all-at-once over cohort",
			"cohort", cohortName, "incomingPriority", incomingPrio)
		// Dedup: a single cluster may host multiple cohort-member CQs
		// (e.g. per-tenant CQs sharing a cohort). The nominated list is
		// at the cluster granularity, so collapse duplicates.
		seen := map[string]struct{}{}
		clusters := make([]string, 0, len(members))
		for _, m := range members {
			if _, ok := seen[m.ClusterName]; ok {
				continue
			}
			seen[m.ClusterName] = struct{}{}
			clusters = append(clusters, m.ClusterName)
		}
		return r.nominate(ctx, wl, clusters)
	}

	sort.SliceStable(candidates, func(i, j int) bool {
		pi, pj := workloadPriority(&candidates[i].victim), workloadPriority(&candidates[j].victim)
		if pi != pj {
			return pi < pj
		}
		ti := candidates[i].victim.CreationTimestamp.Time
		tj := candidates[j].victim.CreationTimestamp.Time
		if !ti.Equal(tj) {
			return ti.Before(tj)
		}
		return candidates[i].victim.Name < candidates[j].victim.Name
	})

	for _, cand := range candidates {
		err := r.evictor.ClaimAndEvict(ctx, cand.clusterName,
			cand.victim.Namespace, cand.victim.Name,
			wl.Namespace, wl.Name)
		if err == nil {
			log.Info("cross-cluster preempted victim",
				"victim", cand.victim.Name, "victimNS", cand.victim.Namespace,
				"victimCluster", cand.clusterName, "victimPriority", workloadPriority(&cand.victim),
				"incoming", req.NamespacedName, "incomingPriority", incomingPrio,
				"cohort", cohortName)
			return r.nominate(ctx, wl, []string{cand.clusterName})
		}
		if err == ErrVictimAlreadyClaimed {
			log.V(3).Info("victim already claimed by another incoming workload, trying next",
				"victim", cand.victim.Name, "victimNS", cand.victim.Namespace)
			continue
		}
		log.Error(err, "evict victim", "victim", cand.victim.Name, "cluster", cand.clusterName)
		return reconcile.Result{}, err
	}

	log.V(3).Info("all preemption candidates already claimed; will retry")
	return reconcile.Result{Requeue: true}, nil
}

// lookupHomeCQ reads the named manager-side ClusterQueue and returns its
// spec.cohortName plus the full CQ for downstream policy/usage inspection.
// Returns ("", nil, nil) if the CQ doesn't exist (workload may have been
// re-admitted on a different CQ between watches).
func (r *CrossClusterPreemptionDispatcherReconciler) lookupHomeCQ(ctx context.Context, name string) (string, *kueue.ClusterQueue, error) {
	cq := &kueue.ClusterQueue{}
	if err := r.client.Get(ctx, types.NamespacedName{Name: name}, cq); err != nil {
		if apierrors.IsNotFound(err) {
			return "", nil, nil
		}
		return "", nil, err
	}
	return string(cq.Spec.CohortName), cq, nil
}

// nominate writes wl.Status.NominatedClusterNames to the given list.
func (r *CrossClusterPreemptionDispatcherReconciler) nominate(ctx context.Context, wl *kueue.Workload, clusters []string) (reconcile.Result, error) {
	sort.Strings(clusters)
	if err := workload.PatchAdmissionStatus(ctx, r.client, wl, r.clock, func(w *kueue.Workload) (bool, error) {
		w.Status.NominatedClusterNames = clusters
		return true, nil
	}); err != nil {
		return reconcile.Result{}, fmt.Errorf("patch nominated clusters: %w", err)
	}
	return reconcile.Result{}, nil
}

// cqAllowsCrossCohortReclaim returns true if the remote ClusterQueue's
// preemption policy permits being a cross-cohort preemption victim source.
// Mirrors the single-cluster ReclaimWithinCohort semantics.
func cqAllowsCrossCohortReclaim(cq *kueue.ClusterQueue) bool {
	if cq == nil || cq.Spec.Preemption == nil {
		return false // default is Never
	}
	policy := cq.Spec.Preemption.ReclaimWithinCohort
	return policy == kueue.PreemptionPolicyLowerPriority || policy == kueue.PreemptionPolicyAny
}

// canPreempt returns true if `victim` is eligible for preemption by an
// incoming workload of priority `incomingPrio`, given the victim's home CQ
// preemption policy.
//
// Mirrors single-cluster cohort preemption semantics:
//   - ReclaimWithinCohort=LowerPriority: victim.priority < incomingPrio
//   - ReclaimWithinCohort=Any: any priority allowed (including equal/higher)
//   - ReclaimWithinCohort=Never: never preempt (filtered earlier in
//     cqAllowsCrossCohortReclaim, but defensive here too)
func canPreempt(victimCQ *kueue.ClusterQueue, incomingPrio int32, victim *kueue.Workload) bool {
	if victimCQ == nil || victimCQ.Spec.Preemption == nil {
		return false
	}
	switch victimCQ.Spec.Preemption.ReclaimWithinCohort {
	case kueue.PreemptionPolicyAny:
		return true
	case kueue.PreemptionPolicyLowerPriority:
		return workloadPriority(victim) < incomingPrio
	default: // Never or unrecognized
		return false
	}
}

// workloadPriority returns the workload's priority, defaulting to 0 if nil.
func workloadPriority(wl *kueue.Workload) int32 {
	if wl == nil || wl.Spec.Priority == nil {
		return 0
	}
	return *wl.Spec.Priority
}
