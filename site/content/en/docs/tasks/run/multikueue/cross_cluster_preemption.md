---
title: "Cross-Cluster Preemption"
date: 2026-05-15
weight: 12
description: >
  Allow a high-priority workload arriving at the MultiKueue manager to
  preempt a lower-priority workload running on a sibling worker cluster.
  Mirrors the single-cluster Cohort API: cohort membership is declared on
  each ClusterQueue via `spec.cohortName`, and per-ClusterQueue opt-in is
  controlled by `spec.preemption.reclaimWithinCohort`.
---

{{< feature-state state="alpha" for_version="v0.18" >}}

{{% alert title="Note" color="primary" %}}
Cross-cluster preemption is in alpha and disabled by default. Enable it via
the `MultiKueueCrossClusterPreemption` feature gate. Refer to the
[Installation guide](/docs/installation/#change-the-feature-gates-configuration)
for instructions.
{{% /alert %}}

## When to use cross-cluster preemption

By default MultiKueue dispatches workloads to whichever worker cluster
admits first. If no worker has free quota, the workload waits. If a
high-priority workload arrives but every worker is full of low-priority
workloads, the high-priority workload waits for a low-priority workload to
finish naturally — wait time depends on workloads outside the
high-priority workload's quota.

Cross-cluster preemption gives operators a tool to bound that wait. By
placing the manager-side ClusterQueue and the worker-side ClusterQueues
into a shared cohort (using the same `spec.cohortName` field that
single-cluster Kueue Cohorts use), the manager can evict a lower-priority
workload on a sibling worker to make room for the higher-priority workload.

## Single-cluster Cohort parity

The cross-cluster preemption API uses the **standard single-cluster Cohort
API** so users have a single mental model — there is no MultiKueue-specific
cohort CRD:

- **Cohort membership is declared on each `ClusterQueue` via
  `spec.cohortName`** — never enumerated separately.
- **Cohort-level properties live on the standard single-cluster `Cohort`
  CR** (the same one you'd use without MultiKueue). It's optional and only
  needed if you want a cohort-level shared pool, parent cohort, fair
  sharing, etc.
- **Per-ClusterQueue opt-in is via
  `spec.preemption.reclaimWithinCohort`**: `Never` (default) /
  `LowerPriority` / `Any`. Same semantics as single-cluster.

## Setup

### 1. Enable the feature gate

On the manager cluster's kueue controller-manager:

```
--feature-gates=MultiKueueCrossClusterPreemption=true
```

### 2. Configure the dispatcher mode

In the kueue manager's `Configuration`:

```yaml
multiKueue:
  dispatcherName: kueue.x-k8s.io/multikueue-dispatcher-cross-cluster-preemption
```

### 3. Set `cohortName` on the manager-side ClusterQueue

```yaml
apiVersion: kueue.x-k8s.io/v1beta2
kind: ClusterQueue
metadata:
  name: gpu-cq
spec:
  cohortName: gpu-cohort           # joins the cohort
  namespaceSelector: {}
  admissionChecksStrategy:
    admissionChecks:
    - name: multikueue-ac
  resourceGroups:
  - coveredResources: ["cpu", "memory"]
    flavors:
    - name: default-flavor
      resources:
      - name: cpu
        nominalQuota: "100"
      - name: memory
        nominalQuota: 100Gi
```

### 4. Set `cohortName` and opt in on each worker ClusterQueue

On every worker cluster whose ClusterQueue should participate as a
preemption peer:

```yaml
apiVersion: kueue.x-k8s.io/v1beta2
kind: ClusterQueue
metadata:
  name: gpu-cq
spec:
  cohortName: gpu-cohort           # same name as on the manager + sibling workers
  namespaceSelector: {}
  preemption:
    # Opt in as a victim source. Choose one:
    #   Never         — never give up workloads to cohort siblings (default).
    #   LowerPriority — workloads on this CQ may be evicted by an incoming
    #                   workload of strictly higher priority.
    #   Any           — workloads on this CQ may be evicted by any incoming
    #                   cohort workload regardless of priority.
    reclaimWithinCohort: LowerPriority
  resourceGroups:
  - coveredResources: ["cpu", "memory"]
    flavors:
    - name: default-flavor
      resources:
      - name: cpu
        nominalQuota: "8"
      - name: memory
        nominalQuota: 32Gi
```

### 5. (Optional) Create a single-cluster `Cohort` CR for cohort-level config

If you want cohort-level shared quota, fair sharing, or hierarchical
cohorts, create the standard single-cluster `Cohort` CR — same shape as
in any non-MultiKueue Kueue setup, with `metadata.name` matching the
`cohortName` you set on the ClusterQueues:

```yaml
apiVersion: kueue.x-k8s.io/v1beta2
kind: Cohort
metadata:
  name: gpu-cohort                 # matches the cohortName on the ClusterQueues
spec:
  resourceGroups:                  # additional cohort-level shared capacity
  - coveredResources: ["cpu", "memory"]
    flavors:
    - name: default-flavor
      resources:
      - name: cpu
        nominalQuota: "0"
      - name: memory
        nominalQuota: 0
  # parentName, fairSharing, etc. are honored locally by the cluster's scheduler
```

If you don't need any cohort-level config, you can skip this — the cohort
exists implicitly by virtue of ClusterQueues sharing a `cohortName`.

## How it works

When a workload arrives at the manager and reserves quota:

1. The cross-cluster-preemption dispatcher reads the workload's manager
   ClusterQueue and looks up its `spec.cohortName` and full
   `spec.preemption` policy.
2. It discovers cohort members by listing ClusterQueues across the
   configured worker clusters that share the same `cohortName`.
3. For each member ClusterQueue with
   `spec.preemption.reclaimWithinCohort != Never` AND that is *currently
   borrowing* (`status.flavorsUsage > spec.resourceGroups[…].nominalQuota`
   for some resource the incoming workload requests), it lists workloads
   currently admitted there. CQs at-or-below their nominal own that quota
   and are never victim sources — same as single-cluster.
4. It filters candidate victims by the per-ClusterQueue policy:
   - `LowerPriority`: keep workloads whose priority is strictly less than
     the incoming workload's priority.
   - `Any`: keep all admitted workloads on that ClusterQueue.
5. **BorrowWithinCohort gate**: if admitting the incoming workload would
   leave the *manager-side* ClusterQueue above its nominal quota, the
   preemption is "preempt while borrowing". The dispatcher applies the
   manager CQ's `spec.preemption.borrowWithinCohort` policy:
   - `nil` or `Policy=Never`: drop all candidates — no preempt-while-borrow.
   - `Policy=LowerPriority`: keep candidates where the incoming priority
     beats `MaxPriorityThreshold` or beats the candidate's priority.
6. It picks the lowest-priority candidate (ties broken by creation
   timestamp, then name) and claims it via a
   `kueue.x-k8s.io/multikueue-cross-preemption-victim-of=<incoming-namespace>/<incoming-name>`
   annotation as a single-writer lock.
7. It evicts the victim on its worker (with reason
   `WorkloadEvictedByPreemption`) and nominates the freed worker for the
   incoming workload. MultiKueue's normal flow then dispatches the workload
   there.

If no preemptible victim is found, the dispatcher falls back to nominating
all cohort members — equivalent to all-at-once dispatch over the cohort.

## Cohort-level resource math (lendingLimit, borrowingLimit, fairSharing)

These features work via the **standard single-cluster `Cohort` CR** that
you may have created in step 5 above. The cross-cluster dispatcher does not
introduce a separate cross-cluster cohort CRD; the manager (and each
worker) runs the same Kueue scheduler that already handles cohort-level
resource math:

1. Create a single-cluster `Cohort` CR on the manager (and on each worker
   that needs cohort-level config) with `metadata.name` matching the
   `cohortName` on the ClusterQueues.
2. Put `spec.resourceGroups` (cohort-level shared pool),
   `spec.fairSharing`, and `spec.parentName` (hierarchical cohort) on it.
3. Set `BorrowingLimit` / `LendingLimit` on each ClusterQueue per the
   [single-cluster docs](/docs/concepts/cluster_queue/#cohort).

Each cluster's local scheduler computes its admission decisions using
those constraints — the same code path as any single-cluster Kueue
deployment. The cross-cluster preemption dispatcher reads each remote
ClusterQueue's `Status.FlavorsUsage` (which already reflects cohort math)
to drive its borrowing checks and victim selection.

## Per-ClusterQueue policy reference

The values for `ClusterQueue.spec.preemption.reclaimWithinCohort` map
exactly to single-cluster semantics, with both the priority filter and the
quota-borrowing filter applied jointly:

| Value | Cross-cluster effect |
|---|---|
| `Never` (default) | This ClusterQueue is never a victim source. Its workloads cannot be evicted by cross-cluster preemption. |
| `LowerPriority` | Workloads on this ClusterQueue are eligible victims iff (a) the CQ is currently borrowing for the contended resource AND (b) their priority is strictly less than the incoming workload's priority. |
| `Any` | Workloads on this ClusterQueue are eligible victims iff the CQ is currently borrowing for the contended resource (priority ignored). |

`ClusterQueue.spec.preemption.borrowWithinCohort` on the **manager-side**
CQ controls whether the dispatcher may preempt while leaving the manager
CQ above its nominal:

| `borrowWithinCohort.policy` | Effect |
|---|---|
| `nil` / `Never` (default) | If admitting the incoming would leave the manager CQ above its nominal quota, no preemption fires. |
| `LowerPriority` | Allowed iff `incoming.priority > maxPriorityThreshold` OR `incoming.priority > victim.priority`. |

`spec.preemption.withinClusterQueue` is honored locally by each worker's
own Kueue scheduler; cross-cluster preemption does not change its
semantics.

## Limitations (alpha)

There is a clear split between what the dispatcher enforces directly and
what's inherited from each cluster's standard scheduler:

**Enforced by the cross-cluster dispatcher:**
- `ClusterQueue.spec.preemption.reclaimWithinCohort` for victim eligibility.
- `cqIsBorrowing(victimCQ)` quota-based reclaim filter
  (`Status.FlavorsUsage > NominalQuota`).
- `ClusterQueue.spec.preemption.borrowWithinCohort` on the manager-side CQ
  to gate "preempt while borrowing".

**Inherited from each cluster's standard Kueue scheduler (configure via
the standard single-cluster `Cohort` CR + ClusterQueue limits):**
- Cohort-level shared `ResourceGroups`.
- `BorrowingLimit` / `LendingLimit` on each ClusterQueue.
- `FairSharing` (DRS-based weighting).

**Not enforced anywhere in alpha:**
- Hierarchical cohorts (`Cohort.spec.parentName`) — the cross-cluster
  dispatcher considers only flat cohorts; ancestor membership is not
  consulted.
- Multi-victim packing — alpha picks a single lowest-priority victim per
  reconcile.
- Elastic workloads / `MultiKueueMultiWorkloadAdapter`.
- Enabling `MultiKueueCrossClusterPreemption` and
  `MultiKueueOrchestratedPreemption` (KEP-8303) simultaneously is undefined
  in alpha; pick one dispatcher mode at a time.

See [KEP-NNNN](https://github.com/kubernetes-sigs/kueue/blob/main/keps/NNNN-multikueue-cross-cluster-preemption/README.md)
for the full design and graduation criteria.

## Verifying

Submit a low-priority workload that admits on one worker, then submit a
high-priority workload to the same manager queue. The high-priority
workload should:

1. Reserve quota on the manager.
2. Trigger eviction of the low-priority workload on its worker (you'll see
   `WorkloadEvicted=True` with reason `Preempted` on the remote workload).
3. Be nominated for the freed worker and admit there.

Check controller logs for entries from
`multikueue_cross_cluster_preemption_dispatcher` to see victim selection
and eviction events.
