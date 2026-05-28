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
	"testing"

	"k8s.io/utils/ptr"

	kueue "sigs.k8s.io/kueue/apis/kueue/v1beta2"
)

// TestCanBorrowAgainstVictim pins the upstream semantics for
// `BorrowWithinCohort.MaxPriorityThreshold` to the dispatcher's
// canBorrowAgainstVictim helper. The threshold is a victim-side cap:
// the victim's priority must be ≤ threshold to be eligible for
// borrow-driven preemption, in addition to the standard
// "incoming > victim" rule.
//
// See `apis/kueue/v1beta2/clusterqueue_types.go` API godoc and
// `pkg/scheduler/preemption/classical/hierarchical_preemption.go`
// `isAboveBorrowingThreshold` for the upstream definition.
func TestCanBorrowAgainstVictim(t *testing.T) {
	// Apple Ray's published WorkloadPriorityClass values, used to
	// make each row read as a realistic operator scenario.
	const (
		prodPrio int32 = 0     // normal-priority
		p0Prio   int32 = -100  // highest flex tier
		p1Prio   int32 = -500  // default flex tier
		p2Prio   int32 = -1000 // lowest flex tier
	)

	cqWith := func(policy kueue.BorrowWithinCohortPolicy, threshold *int32) *kueue.ClusterQueue {
		return &kueue.ClusterQueue{
			Spec: kueue.ClusterQueueSpec{
				Preemption: &kueue.ClusterQueuePreemption{
					BorrowWithinCohort: &kueue.BorrowWithinCohort{
						Policy:               policy,
						MaxPriorityThreshold: threshold,
					},
				},
			},
		}
	}

	tests := map[string]struct {
		preemptorCQ  *kueue.ClusterQueue
		incomingPrio int32
		victimPrio   int32
		want         bool
	}{
		"nil CQ → denied": {
			preemptorCQ:  nil,
			incomingPrio: prodPrio,
			victimPrio:   p2Prio,
			want:         false,
		},
		"nil Preemption spec → denied": {
			preemptorCQ:  &kueue.ClusterQueue{},
			incomingPrio: prodPrio,
			victimPrio:   p2Prio,
			want:         false,
		},
		"nil BorrowWithinCohort → denied": {
			preemptorCQ:  &kueue.ClusterQueue{Spec: kueue.ClusterQueueSpec{Preemption: &kueue.ClusterQueuePreemption{}}},
			incomingPrio: prodPrio,
			victimPrio:   p2Prio,
			want:         false,
		},
		"policy=Never → denied even with lower-priority victim": {
			preemptorCQ:  cqWith(kueue.BorrowWithinCohortPolicyNever, nil),
			incomingPrio: prodPrio,
			victimPrio:   p2Prio,
			want:         false,
		},
		"policy=LowerPriority, no threshold, victim strictly lower → allowed": {
			preemptorCQ:  cqWith(kueue.BorrowWithinCohortPolicyLowerPriority, nil),
			incomingPrio: prodPrio,
			victimPrio:   p2Prio,
			want:         true,
		},
		"policy=LowerPriority, no threshold, equal priority → denied": {
			preemptorCQ:  cqWith(kueue.BorrowWithinCohortPolicyLowerPriority, nil),
			incomingPrio: p1Prio,
			victimPrio:   p1Prio,
			want:         false,
		},
		"policy=LowerPriority, no threshold, victim higher → denied": {
			preemptorCQ:  cqWith(kueue.BorrowWithinCohortPolicyLowerPriority, nil),
			incomingPrio: p1Prio,
			victimPrio:   p0Prio,
			want:         false,
		},

		// Threshold = -500 (p1). Apple Ray's typical configuration:
		// borrow-preemption is permitted to evict p1 and p2 victims,
		// but never p0 or production work, regardless of incoming.
		"threshold=p1, prod incoming, p2 victim → allowed (below threshold)": {
			preemptorCQ:  cqWith(kueue.BorrowWithinCohortPolicyLowerPriority, ptr.To(p1Prio)),
			incomingPrio: prodPrio,
			victimPrio:   p2Prio,
			want:         true,
		},
		"threshold=p1, prod incoming, p1 victim → allowed (at threshold boundary)": {
			preemptorCQ:  cqWith(kueue.BorrowWithinCohortPolicyLowerPriority, ptr.To(p1Prio)),
			incomingPrio: prodPrio,
			victimPrio:   p1Prio,
			want:         true,
		},
		"threshold=p1, prod incoming, p0 victim → denied (victim above threshold, protected)": {
			preemptorCQ:  cqWith(kueue.BorrowWithinCohortPolicyLowerPriority, ptr.To(p1Prio)),
			incomingPrio: prodPrio,
			victimPrio:   p0Prio,
			want:         false,
		},
		"threshold=p1, prod incoming, prod victim → denied (no LowerPriority delta)": {
			preemptorCQ:  cqWith(kueue.BorrowWithinCohortPolicyLowerPriority, ptr.To(p1Prio)),
			incomingPrio: prodPrio,
			victimPrio:   prodPrio,
			want:         false,
		},
		"threshold=p1, p0 incoming, p1 victim → allowed (both checks pass)": {
			preemptorCQ:  cqWith(kueue.BorrowWithinCohortPolicyLowerPriority, ptr.To(p1Prio)),
			incomingPrio: p0Prio,
			victimPrio:   p1Prio,
			want:         true,
		},
		"threshold=p1, p2 incoming, p2 victim → denied (no LowerPriority delta)": {
			preemptorCQ:  cqWith(kueue.BorrowWithinCohortPolicyLowerPriority, ptr.To(p1Prio)),
			incomingPrio: p2Prio,
			victimPrio:   p2Prio,
			want:         false,
		},
	}

	for name, tc := range tests {
		t.Run(name, func(t *testing.T) {
			got := canBorrowAgainstVictim(tc.preemptorCQ, tc.incomingPrio, tc.victimPrio)
			if got != tc.want {
				t.Errorf("canBorrowAgainstVictim(incoming=%d, victim=%d) = %v, want %v",
					tc.incomingPrio, tc.victimPrio, got, tc.want)
			}
		})
	}
}
