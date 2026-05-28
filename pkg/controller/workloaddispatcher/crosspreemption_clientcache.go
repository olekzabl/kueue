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

// Package workloaddispatcher (crosspreemption_clientcache.go) defines the
// remote-client cache shared between the read-side RemoteView and the
// write-side Evictor of the cross-cluster-preemption dispatcher. Both look
// up MultiKueueCluster CRs on the manager and build a cached
// controller-runtime client to the worker cluster.
package workloaddispatcher

import (
	"context"
	"errors"
	"fmt"
	"os"
	"sync"

	corev1 "k8s.io/api/core/v1"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/types"
	"k8s.io/client-go/kubernetes/scheme"
	"k8s.io/client-go/tools/clientcmd"
	"sigs.k8s.io/controller-runtime/pkg/client"

	kueue "sigs.k8s.io/kueue/apis/kueue/v1beta2"
)

// remoteClientCache loads + caches controller-runtime clients for worker
// clusters referenced by MultiKueueCluster objects on the manager.
//
// Concurrency: the cache is goroutine-safe. The client construction is
// guarded by a single lock — it's a rare path (once per cluster).
//
// Invalidation: callers can call Invalidate(clusterName) when an API call
// suggests stale credentials. The next Get rebuilds the client.
type remoteClientCache struct {
	localClient     client.Client
	configNamespace string
	scheme          *runtime.Scheme

	mu       sync.Mutex
	clientCh map[string]client.Client
}

// newRemoteClientCache constructs a cache. localClient must be the manager's
// API client. configNamespace must be the namespace where MultiKueueCluster
// kubeconfig Secrets live (typically `kueue-system`).
func newRemoteClientCache(localClient client.Client, configNamespace string) *remoteClientCache {
	s := runtime.NewScheme()
	_ = scheme.AddToScheme(s)
	_ = kueue.AddToScheme(s)
	return &remoteClientCache{
		localClient:     localClient,
		configNamespace: configNamespace,
		scheme:          s,
		clientCh:        map[string]client.Client{},
	}
}

// Get returns a cached or newly-built client for the named MultiKueueCluster.
func (c *remoteClientCache) Get(ctx context.Context, clusterName string) (client.Client, error) {
	c.mu.Lock()
	if rc, ok := c.clientCh[clusterName]; ok {
		c.mu.Unlock()
		return rc, nil
	}
	c.mu.Unlock()

	cluster := &kueue.MultiKueueCluster{}
	if err := c.localClient.Get(ctx, types.NamespacedName{Name: clusterName}, cluster); err != nil {
		return nil, fmt.Errorf("get MultiKueueCluster %q: %w", clusterName, err)
	}
	if cluster.Spec.ClusterSource.KubeConfig == nil {
		return nil, fmt.Errorf("MultiKueueCluster %q has no kubeConfig (clusterProfileRef not supported in MVP)", clusterName)
	}

	kubeConfigBytes, err := c.loadKubeConfig(ctx, cluster.Spec.ClusterSource.KubeConfig)
	if err != nil {
		return nil, err
	}
	restCfg, err := clientcmd.RESTConfigFromKubeConfig(kubeConfigBytes)
	if err != nil {
		return nil, fmt.Errorf("parse kubeconfig for %q: %w", clusterName, err)
	}
	rc, err := client.New(restCfg, client.Options{Scheme: c.scheme})
	if err != nil {
		return nil, fmt.Errorf("build remote client for %q: %w", clusterName, err)
	}

	c.mu.Lock()
	c.clientCh[clusterName] = rc
	c.mu.Unlock()
	return rc, nil
}

// Invalidate drops the cached client for the named cluster. The next Get
// will rebuild it.
func (c *remoteClientCache) Invalidate(clusterName string) {
	c.mu.Lock()
	delete(c.clientCh, clusterName)
	c.mu.Unlock()
}

func (c *remoteClientCache) loadKubeConfig(ctx context.Context, ref *kueue.KubeConfig) ([]byte, error) {
	if ref == nil {
		return nil, errors.New("nil kubeConfig reference")
	}
	if ref.LocationType == kueue.SecretLocationType {
		var sec corev1.Secret
		if err := c.localClient.Get(ctx, types.NamespacedName{Namespace: c.configNamespace, Name: ref.Location}, &sec); err != nil {
			return nil, fmt.Errorf("get kubeconfig secret %q: %w", ref.Location, err)
		}
		data, ok := sec.Data[kueue.MultiKueueConfigSecretKey]
		if !ok {
			return nil, fmt.Errorf("secret %q missing %q key", ref.Location, kueue.MultiKueueConfigSecretKey)
		}
		return data, nil
	}
	return os.ReadFile(ref.Location)
}
