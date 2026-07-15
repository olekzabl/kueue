package scheduler

import (
	"context"
	"fmt"
	"math"
	"strconv"
	"strings"
	"testing"
	"time"

	corev1 "k8s.io/api/core/v1"
	"k8s.io/apimachinery/pkg/api/resource"
	"k8s.io/apimachinery/pkg/util/sets"
	"sigs.k8s.io/controller-runtime/pkg/client"
	"sigs.k8s.io/controller-runtime/pkg/client/interceptor"

	kueue "sigs.k8s.io/kueue/apis/kueue/v1beta2"
	qcache "sigs.k8s.io/kueue/pkg/cache/queue"
	schdcache "sigs.k8s.io/kueue/pkg/cache/scheduler"
	preemptexpectations "sigs.k8s.io/kueue/pkg/scheduler/preemption/expectations"
	utiltesting "sigs.k8s.io/kueue/pkg/util/testing"
	utiltestingapi "sigs.k8s.io/kueue/pkg/util/testing/v1beta2"
	testingnode "sigs.k8s.io/kueue/pkg/util/testingjobs/node"
)

func BenchmarkSchedulerTAS(b *testing.B) {
	cases := []struct {
		nodes                        int
		nodeGroups                   int
		requestedPods                int
		requestedNodeFractionPercent int
		numResources                 int
	}{
		{
			nodes:                        1000,
			nodeGroups:                   8,
			requestedPods:                200,
			requestedNodeFractionPercent: 50,
			numResources:                 30,
		},
	}
	for _, tc := range cases {
		b.Run(fmt.Sprintf("nodes=%d/nodeGroups=%d/pods=%d/res=%d", tc.nodes, tc.nodeGroups, tc.requestedPods, tc.numResources), func(b *testing.B) {
			numNodes := tc.nodes
			numNodeGroups := tc.nodeGroups
			numRequestedPods := tc.requestedPods
			requestedNodeFractionPercent := tc.requestedNodeFractionPercent
			numResources := tc.numResources

			now := time.Now()
			branchingFactor := max(int(math.Sqrt(float64(numNodes))), 1)

			nodes := make([]corev1.Node, numNodes)

			type nodeCap struct {
				cpu int64
				ram int64
			}
			caps := make([]nodeCap, numNodes)

			blockId := 0
			nodeId := 0
			for i := 0; i < numNodes; i++ {
				nodeId++
				if nodeId == branchingFactor {
					nodeId = 0
					blockId++
				}
				host := fmt.Sprintf("node-%d-%d", blockId, nodeId)
				gName := fmt.Sprintf("group-%d", blockId%numNodeGroups+1)

				allocatable := corev1.ResourceList{
					corev1.ResourceCPU:    resource.MustParse("10"),
					corev1.ResourceMemory: resource.MustParse("100Gi"),
					corev1.ResourcePods:   resource.MustParse("110"),
				}
				// 0 and 1 are CPU/Memory, additional ones are mocked.
				for r := 2; r < numResources; r++ {
					allocatable[corev1.ResourceName(fmt.Sprintf("example.com/res-%d", r))] = resource.MustParse("10")
				}

				nodes[i] = *testingnode.MakeNode(host).
					Label("cloud.com/topology-block", fmt.Sprintf("b-%d", blockId)).
					Label(corev1.LabelHostname, host).
					Label("tas-node", "true").
					Label("node-group", gName).
					StatusAllocatable(allocatable).
					Ready().
					Obj()
				caps[i] = nodeCap{cpu: 10, ram: 100}
			}

			var workloads []kueue.Workload

			wlIdx := 1
			for {
				cpuReq := int64(wlIdx%10) + 1
				ramReq := int64(wlIdx%100) + 1
				podsCount := (wlIdx*10)%int(math.Sqrt(float64(numNodes))) + 1

				podsPlaced := 0
				assignments := make(map[string]int32)
				capsBackup := make([]nodeCap, numNodes)
				copy(capsBackup, caps)

				for j := 0; j < numNodes && podsPlaced < podsCount; j++ {
					for caps[j].cpu >= cpuReq && caps[j].ram >= ramReq && podsPlaced < podsCount {
						caps[j].cpu -= cpuReq
						caps[j].ram -= ramReq
						podsPlaced++
						assignments[nodes[j].Labels[corev1.LabelHostname]]++
					}
				}

				if podsPlaced < podsCount {
					copy(caps, capsBackup)
					break
				}

				levels := []string{corev1.LabelHostname}
				ta := utiltestingapi.MakeTopologyAssignment(levels)
				for h, count := range assignments {
					ta.Domain(utiltestingapi.MakeTopologyDomainAssignment([]string{h}, count).Obj())
				}

				ps := utiltestingapi.MakePodSet("main", podsCount).
					Request(corev1.ResourceCPU, fmt.Sprintf("%d", cpuReq)).
					Request(corev1.ResourceMemory, fmt.Sprintf("%dGi", ramReq))
				for r := 2; r < numResources; r++ {
					ps.Request(corev1.ResourceName(fmt.Sprintf("example.com/res-%d", r)), fmt.Sprintf("%d", cpuReq))
				}

				psa := utiltestingapi.MakePodSetAssignment("main").
					Assignment(corev1.ResourceCPU, "tas-flavor", fmt.Sprintf("%d", cpuReq)).
					Assignment(corev1.ResourceMemory, "tas-flavor", fmt.Sprintf("%dGi", ramReq)).
					TopologyAssignment(ta.Obj())
				for r := 2; r < numResources; r++ {
					psa.Assignment(corev1.ResourceName(fmt.Sprintf("example.com/res-%d", r)), "tas-flavor", fmt.Sprintf("%d", cpuReq))
				}

				wl := utiltestingapi.MakeWorkload(fmt.Sprintf("wl-%d", wlIdx), "default").
					Queue("tas-main").
					Priority(int32(wlIdx)).
					PodSets(*ps.Obj()).
					ReserveQuotaAt(utiltestingapi.MakeAdmission("tas-main").
						PodSets(psa.Obj()).Obj(), now).
					AdmittedAt(true, now).
					Obj()

				workloads = append(workloads, *wl)
				wlIdx++
			}

			requestedCpu := int64(10 * requestedNodeFractionPercent / 100)
			requestedRam := int64(100 * requestedNodeFractionPercent / 100)

			psReq := utiltestingapi.MakePodSet("main", numRequestedPods).
				Request(corev1.ResourceCPU, fmt.Sprintf("%d", requestedCpu)).
				Request(corev1.ResourceMemory, fmt.Sprintf("%dGi", requestedRam)).
				NodeSelector(map[string]string{"node-group": "group-1"})
			for r := 2; r < numResources; r++ {
				psReq.Request(corev1.ResourceName(fmt.Sprintf("example.com/res-%d", r)), fmt.Sprintf("%d", requestedCpu))
			}

			requestedWl := utiltestingapi.MakeWorkload("requested-wl", "default").
				Queue("tas-main").
				Priority(int32(wlIdx)).
				PodSets(*psReq.Obj()).
				Obj()

			tasTopology := utiltestingapi.MakeTopology("tas-topology").
				Levels("cloud.com/topology-block", corev1.LabelHostname).
				Obj()
			tasFlavor := utiltestingapi.MakeResourceFlavor("tas-flavor").
				NodeLabel("tas-node", "true").
				TopologyName("tas-topology").
				Obj()

			fq := utiltestingapi.MakeFlavorQuotas("tas-flavor").
				Resource(corev1.ResourceCPU, "100000").
				Resource(corev1.ResourceMemory, "1000000Gi")
			for r := 2; r < numResources; r++ {
				fq.Resource(corev1.ResourceName(fmt.Sprintf("example.com/res-%d", r)), "100000")
			}

			cq := utiltestingapi.MakeClusterQueue("tas-main").
				Preemption(kueue.ClusterQueuePreemption{
					WithinClusterQueue: kueue.PreemptionPolicyLowerPriority,
				}).
				ResourceGroup(*fq.Obj()).
				Obj()

			lq := utiltestingapi.MakeLocalQueue("tas-main", "default").
				ClusterQueue("tas-main").
				Obj()

			objs := []client.Object{
				utiltesting.MakeNamespaceWrapper("default").Obj(),
				tasTopology,
			}
			for i := range nodes {
				objs = append(objs, &nodes[i])
			}

			ctx, log := utiltesting.ContextWithLog(b)

			for b.Loop() {
				b.StopTimer()
				cb := utiltesting.NewClientBuilder(kueue.AddToScheme, corev1.AddToScheme).
					WithObjects(objs...).
					WithLists(
						&kueue.WorkloadList{Items: workloads},
						&kueue.LocalQueueList{Items: []kueue.LocalQueue{*lq}},
						&kueue.ClusterQueueList{Items: []kueue.ClusterQueue{*cq}},
					).
					WithStatusSubresource(&kueue.Workload{}).
					WithInterceptorFuncs(interceptor.Funcs{
						SubResourcePatch: func(ctx context.Context, client client.Client, subResourceName string, obj client.Object, patch client.Patch, opts ...client.SubResourcePatchOption) error {
							return nil // discard updates to speed up bench loop
						},
					})
				cl := cb.Build()
				recorder := &utiltesting.EventRecorder{}
				cqCache := schdcache.New(cl)
				expStore := preemptexpectations.New()
				qManager := qcache.NewManagerForUnitTests(cl, cqCache, qcache.WithPreemptionExpectations(expStore))

				cqCache.AddOrUpdateTopology(log, tasTopology)
				cqCache.AddOrUpdateResourceFlavor(log, tasFlavor)
				_ = cqCache.AddClusterQueue(ctx, cq)
				_ = qManager.AddClusterQueue(ctx, cq)
				_ = qManager.AddLocalQueue(ctx, lq)

				for i := range nodes {
					cqCache.TASCache().SyncNode(&nodes[i])
				}
				for i := range workloads {
					// Admitted workloads go to scheduling cache directly
					_ = cqCache.AddOrUpdateWorkload(log, &workloads[i])
				}

				scheduler := New(qManager, cqCache, cl, recorder, WithPreemptionExpectations(expStore))

				qManager.AddOrUpdateWorkload(log, requestedWl)

				b.StartTimer()
				scheduler.schedule(ctx)

				preemptees := sets.New[int]()
				for _, event := range recorder.RecordedEvents {
					if event.Reason == "Preempted" {
						parts := strings.Split(event.Key.String(), "-")
						idx, _ := strconv.Atoi(parts[len(parts)-1])
						preemptees.Insert(idx)
					}
				}
				b.Logf("[BENCH-DEBUG] Preempted workloads: %v", sets.List(preemptees))
			}
		})
	}
}
