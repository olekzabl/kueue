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

// Package workloaddispatcher (crosspreemption_remoteview.go) abstracts the
// read-side of the cross-cluster-preemption dispatcher: queries that inspect
// remote worker clusters to discover cohort members and victim candidates.
//
// The implementation is split out so unit tests can plug a fake RemoteView
// without standing up a full envtest cluster.
package workloaddispatcher

import (
	"context"
	"fmt"

	apimeta "k8s.io/apimachinery/pkg/api/meta"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"sigs.k8s.io/controller-runtime/pkg/client"

	kueue "sigs.k8s.io/kueue/apis/kueue/v1beta2"
)

// CohortMember is a (clusterName, ClusterQueue) pair found via cohort discovery
// across worker clusters. The full ClusterQueue object is included so the
// dispatcher can read the CQ's preemption policy
// (Spec.Preemption.ReclaimWithinCohort) without a second round trip.
type CohortMember struct {
	ClusterName  string
	ClusterQueue kueue.ClusterQueue
}

// RemoteView is the contract the dispatcher uses to query remote worker
// cluster state. The default implementation talks to real workers; tests
// use a fake.
type RemoteView interface {
	// FindCohortMembers returns the ClusterQueues across the given configured
	// worker clusters whose Spec.CohortName equals cohortName. This mirrors
	// the single-cluster Cohort pattern: cohort membership is inferred from
	// CQ.spec.cohortName, no separate enumeration required.
	//
	// Returns an empty slice (not an error) if no member is found across
	// any cluster — the cohort is empty / unused.
	FindCohortMembers(ctx context.Context, cohortName string, clusterNames []string) ([]CohortMember, error)

	// ListAdmittedWorkloads returns the Workloads currently admitted on the
	// given (clusterName, clusterQueue) pair, dispatched by this manager
	// (filtered by MultiKueueOriginLabel). The returned slice is owned by
	// the caller (safe to mutate / sort).
	ListAdmittedWorkloads(ctx context.Context, clusterName, clusterQueue string) ([]kueue.Workload, error)
}

// defaultRemoteView is the production RemoteView. It uses a shared
// remoteClientCache to talk to worker clusters.
type defaultRemoteView struct {
	cache  *remoteClientCache
	origin string
}

// NewDefaultRemoteView builds a RemoteView that reads from real worker
// clusters via the MultiKueueCluster CRs on the manager.
func NewDefaultRemoteView(cache *remoteClientCache, origin string) RemoteView {
	return &defaultRemoteView{cache: cache, origin: origin}
}

func (v *defaultRemoteView) FindCohortMembers(ctx context.Context, cohortName string, clusterNames []string) ([]CohortMember, error) {
	if cohortName == "" {
		return nil, nil
	}
	out := make([]CohortMember, 0, len(clusterNames))
	for _, name := range clusterNames {
		rc, err := v.cache.Get(ctx, name)
		if err != nil {
			// Skip unreachable workers; they'll be retried on next reconcile.
			continue
		}
		var list kueue.ClusterQueueList
		if err := rc.List(ctx, &list); err != nil {
			return nil, fmt.Errorf("list ClusterQueues on %q: %w", name, err)
		}
		for i := range list.Items {
			cq := list.Items[i]
			if string(cq.Spec.CohortName) == cohortName {
				out = append(out, CohortMember{ClusterName: name, ClusterQueue: cq})
			}
		}
	}
	return out, nil
}

func (v *defaultRemoteView) ListAdmittedWorkloads(ctx context.Context, clusterName, clusterQueue string) ([]kueue.Workload, error) {
	rc, err := v.cache.Get(ctx, clusterName)
	if err != nil {
		return nil, fmt.Errorf("get remote client for %q: %w", clusterName, err)
	}

	var list kueue.WorkloadList
	if err := rc.List(ctx, &list, client.MatchingLabels{kueue.MultiKueueOriginLabel: v.origin}); err != nil {
		return nil, fmt.Errorf("list workloads on %q: %w", clusterName, err)
	}

	out := make([]kueue.Workload, 0, len(list.Items))
	for i := range list.Items {
		w := &list.Items[i]
		if !workloadAdmitted(w) {
			continue
		}
		if w.Status.Admission == nil || string(w.Status.Admission.ClusterQueue) != clusterQueue {
			continue
		}
		out = append(out, *w)
	}
	return out, nil
}

func workloadAdmitted(wl *kueue.Workload) bool {
	c := apimeta.FindStatusCondition(wl.Status.Conditions, kueue.WorkloadAdmitted)
	if c == nil {
		return false
	}
	return c.Status == metav1.ConditionTrue
}
