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

// Package workloaddispatcher (crosspreemption_quota.go) — helpers for
// quota-based victim eligibility and preemptor-side borrow gating.
//
// These helpers mirror the single-cluster Kueue cohort preemption semantics
// where applicable. The semantic mapping is:
//
//   single-cluster                                  cross-cluster
//   ----------------------------------------------  -------------
//   cqIsBorrowing(victimCQ)                         cqIsBorrowing (this file)
//   borrowWithinCohort gate on preemptor CQ         preemptorWouldBorrow + cqAllowsBorrow
//
// The big architectural difference vs single-cluster: there is no shared
// scheduler state across clusters, so we read each remote ClusterQueue's
// `Status.FlavorsUsage` snapshot at reconcile time and trust it — same
// pattern as the existing in-tree scheduler reading the cluster-local
// snapshot but spread across kube-apiservers.
package workloaddispatcher

import (
	corev1 "k8s.io/api/core/v1"
	"k8s.io/apimachinery/pkg/api/resource"

	kueue "sigs.k8s.io/kueue/apis/kueue/v1beta2"
)

// cqIsBorrowing returns true iff for at least one (flavor, resource) tuple,
// the ClusterQueue's reported usage exceeds its nominal quota — i.e. the CQ
// is currently consuming cohort-borrowed capacity.
//
// Mirrors single-cluster cqIsBorrowing
// (pkg/cache/scheduler/clusterqueue_snapshot.go ~L142-148).
//
// `frResources` is the set of (flavor, resource) tuples the incoming
// workload needs preemption for. If empty (e.g. unknown), we report
// borrowing for ANY covered resource.
func cqIsBorrowing(cq *kueue.ClusterQueue, frResources []flavorResource) bool {
	if cq == nil {
		return false
	}
	nominal := nominalQuotaByFlavorResource(cq)
	usage := usageByFlavorResource(cq)
	if len(frResources) == 0 {
		// Conservative fallback: any covered resource.
		for fr, n := range nominal {
			if u, ok := usage[fr]; ok && u.Cmp(n) > 0 {
				return true
			}
		}
		return false
	}
	for _, fr := range frResources {
		n, hasNominal := nominal[fr]
		u, hasUsage := usage[fr]
		if !hasNominal || !hasUsage {
			continue
		}
		if u.Cmp(n) > 0 {
			return true
		}
	}
	return false
}

// preemptorWouldBorrow returns true iff the manager-side ClusterQueue is
// (or would remain) above its nominal quota — i.e. admitting/keeping this
// workload requires borrowing cohort capacity. We use FlavorsReservation
// because the incoming workload has already reserved manager-side quota
// (HasQuotaReservation gate upstream), so the reservation snapshot already
// includes this workload's footprint.
func preemptorWouldBorrow(cq *kueue.ClusterQueue, frResources []flavorResource) bool {
	if cq == nil {
		return false
	}
	nominal := nominalQuotaByFlavorResource(cq)
	reserved := reservationByFlavorResource(cq)
	if len(frResources) == 0 {
		for fr, n := range nominal {
			if r, ok := reserved[fr]; ok && r.Cmp(n) > 0 {
				return true
			}
		}
		return false
	}
	for _, fr := range frResources {
		n, hasNominal := nominal[fr]
		r, hasReserved := reserved[fr]
		if !hasNominal || !hasReserved {
			continue
		}
		if r.Cmp(n) > 0 {
			return true
		}
	}
	return false
}

// cqAllowsBorrow returns true iff the manager-side ClusterQueue's
// `BorrowWithinCohort` policy permits a preempting reconcile to leave the
// preemptor borrowing.
//
// Mirrors single-cluster classifyPreemptionVariant semantics
// (pkg/scheduler/preemption/classical/hierarchical_preemption.go ~L71-77,
// 115-123). Specifically:
//   - If BorrowWithinCohort is nil or Policy=Never → cannot borrow while
//     preempting.
//   - If Policy=LowerPriority and MaxPriorityThreshold is set, the
//     incoming workload's priority must exceed MaxPriorityThreshold OR
//     exceed the candidate priority. Since we apply this per-victim later,
//     we accept if the policy is LowerPriority (the fine-grained per-victim
//     check happens in canBorrowAgainstVictim).
func cqAllowsBorrow(cq *kueue.ClusterQueue) bool {
	if cq == nil || cq.Spec.Preemption == nil {
		return false
	}
	bwc := cq.Spec.Preemption.BorrowWithinCohort
	if bwc == nil {
		return false
	}
	return bwc.Policy == kueue.BorrowWithinCohortPolicyLowerPriority
}

// canBorrowAgainstVictim returns true iff, given the preemptor CQ's
// BorrowWithinCohort policy, the incoming workload may borrow while
// evicting this specific victim.
//
// Matches single-cluster Kueue semantics in
// `pkg/scheduler/preemption/classical/hierarchical_preemption.go`
// (`isAboveBorrowingThreshold` ~L115-123) and the upstream API godoc
// on `BorrowWithinCohort.MaxPriorityThreshold` (see
// `apis/kueue/v1beta2/clusterqueue_types.go`):
//
//	"maxPriorityThreshold allows to restrict the set of workloads which
//	 might be preempted by a borrowing workload, to only workloads with
//	 priority less than or equal to the specified threshold priority."
//
// Two checks must both hold:
//  1. Standard LowerPriority rule — victim must have strictly lower
//     priority than the incoming workload.
//  2. Threshold cap (if set) — victim's priority must be ≤ threshold.
//
// The threshold is a *victim-side cap*, not an incoming-side free pass.
func canBorrowAgainstVictim(preemptorCQ *kueue.ClusterQueue, incomingPrio, victimPrio int32) bool {
	if preemptorCQ == nil || preemptorCQ.Spec.Preemption == nil {
		return false
	}
	bwc := preemptorCQ.Spec.Preemption.BorrowWithinCohort
	if bwc == nil || bwc.Policy != kueue.BorrowWithinCohortPolicyLowerPriority {
		return false
	}
	if victimPrio >= incomingPrio {
		return false
	}
	if bwc.MaxPriorityThreshold != nil && victimPrio > *bwc.MaxPriorityThreshold {
		return false
	}
	return true
}

// flavorResource is the (flavor, resource) tuple keyed in the helpers above.
// Mirrors `cache/scheduler` FlavorResource struct shape, kept private here.
type flavorResource struct {
	Flavor   kueue.ResourceFlavorReference
	Resource corev1.ResourceName
}

// frResourcesForWorkload extracts the (flavor, resource) tuples assigned
// to an incoming workload by the manager-side scheduler. Returns nil if the
// workload has no admission yet.
func frResourcesForWorkload(wl *kueue.Workload) []flavorResource {
	if wl == nil || wl.Status.Admission == nil {
		return nil
	}
	out := make([]flavorResource, 0)
	for _, psa := range wl.Status.Admission.PodSetAssignments {
		for resName, flavor := range psa.Flavors {
			out = append(out, flavorResource{Flavor: flavor, Resource: resName})
		}
	}
	return out
}

func nominalQuotaByFlavorResource(cq *kueue.ClusterQueue) map[flavorResource]resource.Quantity {
	out := map[flavorResource]resource.Quantity{}
	for _, rg := range cq.Spec.ResourceGroups {
		for _, fq := range rg.Flavors {
			for _, r := range fq.Resources {
				out[flavorResource{Flavor: fq.Name, Resource: r.Name}] = r.NominalQuota
			}
		}
	}
	return out
}

func usageByFlavorResource(cq *kueue.ClusterQueue) map[flavorResource]resource.Quantity {
	return flavorUsageMap(cq.Status.FlavorsUsage)
}

func reservationByFlavorResource(cq *kueue.ClusterQueue) map[flavorResource]resource.Quantity {
	return flavorUsageMap(cq.Status.FlavorsReservation)
}

func flavorUsageMap(fus []kueue.FlavorUsage) map[flavorResource]resource.Quantity {
	out := map[flavorResource]resource.Quantity{}
	for _, fu := range fus {
		for _, r := range fu.Resources {
			out[flavorResource{Flavor: fu.Name, Resource: r.Name}] = r.Total
		}
	}
	return out
}
