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
	"os"

	ctrl "sigs.k8s.io/controller-runtime"

	configapi "sigs.k8s.io/kueue/apis/config/v1beta2"
	kueue "sigs.k8s.io/kueue/apis/kueue/v1beta2"
	"sigs.k8s.io/kueue/pkg/util/admissioncheck"
	"sigs.k8s.io/kueue/pkg/util/roletracker"
)

// SetupControllers registers the configured MultiKueue dispatcher (if any).
// Returns the controller name on error so the caller can include it in
// error messages; returns "", nil if no dispatcher needs to be registered
// (i.e., the cluster is using the default AllAtOnce dispatcher which is
// handled in-line by the MultiKueue admissioncheck).
func SetupControllers(mgr ctrl.Manager, cfg *configapi.Configuration, roleTracker *roletracker.RoleTracker) (string, error) {
	switch *cfg.MultiKueue.DispatcherName {
	case configapi.MultiKueueDispatcherModeIncremental:
		helper, err := admissioncheck.NewMultiKueueStoreHelper(mgr.GetClient())
		if err != nil {
			return "", err
		}
		idRec := NewIncrementalDispatcherReconciler(mgr.GetClient(), helper, roleTracker)
		if err := idRec.SetupWithManager(mgr, cfg); err != nil {
			return "multikueue-incremental-dispatcher", err
		}
		return "", nil

	case configapi.MultiKueueDispatcherModeCrossClusterPreemption:
		helper, err := admissioncheck.NewMultiKueueStoreHelper(mgr.GetClient())
		if err != nil {
			return "", err
		}
		ns := os.Getenv("POD_NAMESPACE")
		if ns == "" {
			ns = "kueue-system"
		}
		origin := configapi.DefaultMultiKueueOrigin
		if cfg.MultiKueue != nil && cfg.MultiKueue.Origin != nil && *cfg.MultiKueue.Origin != "" {
			origin = *cfg.MultiKueue.Origin
		}
		clientCache := newRemoteClientCache(mgr.GetClient(), ns)
		view := NewDefaultRemoteView(clientCache, origin)
		evictor := NewDefaultEvictor(mgr.GetClient(), realClock)
		ccpRec := NewCrossClusterPreemptionDispatcherReconciler(
			mgr.GetClient(), helper, view, evictor, roleTracker)
		if err := ccpRec.SetupWithManager(mgr, cfg); err != nil {
			return "multikueue-cross-cluster-preemption-dispatcher", err
		}
		return "", nil
	}

	return "", nil
}

// Compile-time check that the kueue api type is referenced (for go-vet
// happiness when configapi.MultiKueueOrigin is removed in some future refactor).
var _ = kueue.MultiKueueOriginLabel
