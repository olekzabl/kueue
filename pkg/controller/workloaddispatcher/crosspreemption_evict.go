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

// Package workloaddispatcher (crosspreemption_evict.go) implements the
// manager-side eviction path of the cross-cluster-preemption dispatcher.
//
// Why manager-side: a worker-side eviction would set Evicted=True on the
// remote Workload, but the worker's own Kueue scheduler immediately
// re-admits the workload because the cohort still has capacity (the
// preemptor's incoming workload hasn't taken its slot yet). Evicting on
// the manager side avoids that race because:
//   1. Manager-side Evicted=True triggers the standard manager workload
//      controller, which suspends the local Job and clears Status.Admission
//      (HasQuotaReservation -> false).
//   2. MultiKueue's wlReconciler observes the no-quota state (section 2,
//      "Delete all remote workloads when the local workload is finished
//      or has no quota reservation") and deletes the remote Workload +
//      remote Job. Cohort capacity on the worker is freed.
//   3. The dispatcher has already written
//      `incoming.Status.NominatedClusterNames = [freedCluster]`, so
//      MultiKueue dispatches the incoming workload to that worker; it
//      admits there using the just-freed cohort capacity.
//   4. The evicted workload re-enters the manager's admission queue and
//      gets re-dispatched to whichever worker has capacity (could be the
//      sibling or stay pending).
//
// The eviction protocol has three steps:
//   1. Optimistically patch a victim-claim annotation
//      (constants.MultiKueueCrossClusterPreemptionVictimAnnotation = <ns>/<name>
//      of the incoming workload) onto the manager-side victim. This patch
//      acts as the single-writer lock — concurrent reconciles for different
//      incoming workloads cannot all evict the same victim. If the
//      annotation already exists with a different value, ClaimAndEvict
//      returns ErrVictimAlreadyClaimed and the caller picks another
//      candidate.
//   2. Patch the manager-side workload's status with the WorkloadEvicted
//      condition (reason WorkloadEvictedByPreemption). Idempotent — if the
//      workload is already evicted we no-op.
//   3. Return success. The caller (the dispatcher reconcile loop) then
//      writes wl.Status.NominatedClusterNames so MultiKueue can dispatch
//      the incoming workload to the freed cluster.
package workloaddispatcher

import (
	"context"
	"errors"
	"fmt"
	"time"

	apimeta "k8s.io/apimachinery/pkg/api/meta"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/types"
	"k8s.io/utils/clock"
	"sigs.k8s.io/controller-runtime/pkg/client"

	kueue "sigs.k8s.io/kueue/apis/kueue/v1beta2"
	"sigs.k8s.io/kueue/pkg/controller/constants"
	"sigs.k8s.io/kueue/pkg/workload"
)

// ErrVictimAlreadyClaimed is returned by Evictor.ClaimAndEvict when the
// victim has already been claimed by a different incoming workload.
var ErrVictimAlreadyClaimed = errors.New("cross-preemption victim already claimed by another incoming workload")

// Evictor performs the claim-and-evict cycle on the manager-side victim
// Workload.
type Evictor interface {
	// ClaimAndEvict atomically claims and evicts the named victim Workload
	// on the MANAGER cluster as a preemption victim of the given incoming
	// workload. The clusterName parameter is informational (recorded in
	// the eviction message) — actual eviction targets the manager-side
	// workload, and MultiKueue's reconciler propagates the cleanup to the
	// remote.
	//
	// Returns ErrVictimAlreadyClaimed if the victim has already been
	// claimed by another incoming workload (e.g. due to concurrent
	// reconciles). Returns nil on successful eviction (or no-op if already
	// evicted).
	//
	// incomingNamespace+incomingName identify the workload that triggered
	// preemption; they're written into the
	// MultiKueueCrossClusterPreemptionVictimAnnotation on the victim.
	ClaimAndEvict(
		ctx context.Context,
		clusterName string,
		victimNamespace, victimName string,
		incomingNamespace, incomingName string,
	) error
}

// defaultEvictor is the production Evictor. It operates on manager-side
// Workloads so MultiKueue's standard "no quota reservation -> delete
// remote" reconcile path handles the worker-side cleanup.
type defaultEvictor struct {
	managerClient client.Client
	clock         clock.Clock
}

// NewDefaultEvictor builds an Evictor that targets manager-side workloads
// via the supplied manager client.
func NewDefaultEvictor(managerClient client.Client, clk clock.Clock) Evictor {
	return &defaultEvictor{managerClient: managerClient, clock: clk}
}

func (e *defaultEvictor) ClaimAndEvict(
	ctx context.Context,
	clusterName string,
	victimNamespace, victimName string,
	incomingNamespace, incomingName string,
) error {
	claimValue := fmt.Sprintf("%s/%s", incomingNamespace, incomingName)

	// Step 1: read the manager-side victim, check existing claim, and
	// write the claim if free.
	var victim kueue.Workload
	if err := e.managerClient.Get(ctx, types.NamespacedName{Namespace: victimNamespace, Name: victimName}, &victim); err != nil {
		return fmt.Errorf("get victim %s/%s on manager: %w", victimNamespace, victimName, err)
	}

	if existing, ok := victim.Annotations[constants.MultiKueueCrossClusterPreemptionVictimAnnotation]; ok {
		if existing != claimValue {
			return ErrVictimAlreadyClaimed
		}
		// Already claimed by us — proceed to (idempotent) evict.
	} else {
		// Patch the annotation. We use optimistic concurrency via the
		// resourceVersion to detect a race.
		patched := victim.DeepCopy()
		if patched.Annotations == nil {
			patched.Annotations = map[string]string{}
		}
		patched.Annotations[constants.MultiKueueCrossClusterPreemptionVictimAnnotation] = claimValue
		if err := e.managerClient.Patch(ctx, patched, client.MergeFromWithOptions(&victim, client.MergeFromWithOptimisticLock{})); err != nil {
			// On a conflict, somebody else patched concurrently — refetch
			// and re-check the annotation. Treat differing claimer as
			// already-claimed.
			if err := e.managerClient.Get(ctx, types.NamespacedName{Namespace: victimNamespace, Name: victimName}, &victim); err == nil {
				if existing, ok := victim.Annotations[constants.MultiKueueCrossClusterPreemptionVictimAnnotation]; ok && existing != claimValue {
					return ErrVictimAlreadyClaimed
				}
			}
			return fmt.Errorf("patch claim annotation on %s/%s: %w", victimNamespace, victimName, err)
		}
		victim = *patched
	}

	// Step 2: evict on the manager-side. Idempotent — if already evicted,
	// SetEvictedCondition returns false and we no-op.
	msg := fmt.Sprintf("evicted by cross-cluster preemption for %s (freed cluster: %s)", claimValue, clusterName)

	// Skip if already evicted.
	if c := apimeta.FindStatusCondition(victim.Status.Conditions, kueue.WorkloadEvicted); c != nil && c.Status == metav1.ConditionTrue {
		return nil
	}

	now := e.clock.Now()
	if err := workload.PatchAdmissionStatus(ctx, e.managerClient, &victim, e.clock, func(w *kueue.Workload) (bool, error) {
		// Set Evicted=True on the manager-side workload. The standard
		// manager workload controller will:
		//   - suspend the local (manager-side) Job
		//   - clear Status.Admission (so HasQuotaReservation -> false)
		//   - reset admission checks
		// MultiKueue's wlReconciler then observes the no-quota state and
		// deletes all remote Workloads + remote Jobs (its section 2). The
		// freed worker cohort capacity is what the incoming workload
		// (already nominated to that cluster) will consume.
		//
		// We intentionally leave Status.ClusterName and
		// Status.NominatedClusterNames alone. Clearing them here races
		// with MultiKueue's wlReconciler — between our manager patch and
		// the manager workload controller's Admission-clear, the
		// wlReconciler can observe Evicted=True + HasQuotaReservation=true
		// and run its "evicted on manager" short-circuit
		// (workload.go:478), but only if NominatedClusterNames still
		// reflects the original dispatch. Otherwise it falls through to
		// syncReservingRemoteState, which tries to set
		// status.ClusterName=<reservingRemote> and is rejected by the
		// validating webhook ("when setting clusterName it must be one of
		// the nominatedClusterNames"). The remote workload then never
		// gets cleaned up, the worker's cohort capacity is never freed,
		// and the incoming workload can't admit on the freed cluster.
		return workload.SetEvictedCondition(w, now, kueue.WorkloadEvictedByPreemption, msg), nil
	}); err != nil {
		return fmt.Errorf("patch evicted status on victim %s/%s: %w", victimNamespace, victimName, err)
	}
	return nil
}

// Compile-time check that the time import is used.
var _ time.Duration
