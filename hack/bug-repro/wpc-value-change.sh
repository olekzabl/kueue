#!/bin/bash

REPRO_PREFIX=repro
CPU_QUOTA=\"0.4\"
MEMORY_QUOTA=\"1G\"
PRIO1_VALUE=1000
PRIO2_VALUE=2000
PRIO1_NEW_VALUE=3000
PRIO2_NEW_VALUE=500

show_wl() {
  kubectl get wl -o custom-columns=NAME:.metadata.name,RESERVED_IN:.status.admission.clusterQueue,PRIORITY:.spec.priority
}

hold() {
  for x in $(seq $1); do
    echo -n .
    sleep 1
  done
  echo ""
}

cat <<EOF | kubectl apply -f -
apiVersion: kueue.x-k8s.io/v1beta1
kind: ResourceFlavor
metadata:
  name: $REPRO_PREFIX-rf
---
apiVersion: kueue.x-k8s.io/v1beta1
kind: ClusterQueue
metadata:
  name: $REPRO_PREFIX-cq
spec:
  namespaceSelector: {} # match all.
  resourceGroups:
  - coveredResources: ["cpu", "memory"]
    flavors:
    - name: $REPRO_PREFIX-rf
      resources:
      - name: "cpu"
        nominalQuota: $CPU_QUOTA
      - name: "memory"
        nominalQuota: $MEMORY_QUOTA
  preemption:
    withinClusterQueue: LowerPriority
---
apiVersion: kueue.x-k8s.io/v1beta1
kind: LocalQueue
metadata:
  name: $REPRO_PREFIX-lq
spec:
  clusterQueue: $REPRO_PREFIX-cq
---
apiVersion: kueue.x-k8s.io/v1beta1
kind: WorkloadPriorityClass
metadata:
  name: $REPRO_PREFIX-prio-1
value: $PRIO1_VALUE
description: "Prio $PRIO1_VALUE"
---
apiVersion: kueue.x-k8s.io/v1beta1
kind: WorkloadPriorityClass
metadata:
  name: $REPRO_PREFIX-prio-2
value: $PRIO2_VALUE
description: "Prio $PRIO2_VALUE"
---
apiVersion: batch/v1
kind: Job
metadata:
  name: $REPRO_PREFIX-job-1
  namespace: default
  labels:
    kueue.x-k8s.io/queue-name: $REPRO_PREFIX-lq
    kueue.x-k8s.io/priority-class: $REPRO_PREFIX-prio-1
spec:
  parallelism: 1
  completions: 1
  template:
    spec:
      containers:
      - name: dummy-job
        image: registry.k8s.io/e2e-test-images/agnhost:2.53
        command: [ "/bin/sh" ]
        args: [ "-c", "sleep 60" ]
        resources:
          requests:
            cpu: $CPU_QUOTA
            memory: $MEMORY_QUOTA
      restartPolicy: Never
---
apiVersion: batch/v1
kind: Job
metadata:
  name: $REPRO_PREFIX-job-2
  namespace: default
  labels:
    kueue.x-k8s.io/queue-name: $REPRO_PREFIX-lq
    kueue.x-k8s.io/priority-class: $REPRO_PREFIX-prio-2
spec:
  parallelism: 1
  completions: 1
  template:
    spec:
      containers:
      - name: dummy-job
        image: registry.k8s.io/e2e-test-images/agnhost:2.53
        command: [ "/bin/sh" ]
        args: [ "-c", "sleep 60" ]
        resources:
          requests:
            cpu: $CPU_QUOTA
            memory: $MEMORY_QUOTA
      restartPolicy: Never
EOF

show_wl

echo "--- Patching $REPRO_PREFIX-prio-2 to have value $PRIO2_NEW_VALUE ---"
kubectl patch workloadpriorityclass $REPRO_PREFIX-prio-2 --type merge -p "{\"value\": $PRIO2_NEW_VALUE}"

echo "--- Verifying that patching succeeded ---"
kubectl get workloadpriorityclass $REPRO_PREFIX-prio-2

echo "--- Giving Kueue some seconds to reconcile ---"
hold 5

echo "--- Expect $REPRO_PREFIX-job-2 to have priority $PRIO2_NEW_VALUE, and be preempted ---"
show_wl
echo "--- BUG: Nothing changed ---"

echo "--- Patching $REPRO_PREFIX-prio-1 to have value $PRIO1_NEW_VALUE ---"
kubectl patch workloadpriorityclass $REPRO_PREFIX-prio-1 --type merge -p "{\"value\": $PRIO1_NEW_VALUE}"

echo "--- Verifying that patching succeeded ---"
kubectl get workloadpriorityclass $REPRO_PREFIX-prio-1

echo "--- Giving Kueue some seconds to reconcile ---"
hold 5

echo "--- Expect $REPRO_PREFIX-job-1 to have priority $PRIO1_NEW_VALUE, and to preempt $REPRO_PREFIX-job-2 ---"
show_wl
echo "--- BUG: Nothing changed ---"

echo "--- Cleaning up ---"
kubectl delete \
  job/$REPRO_PREFIX-job-1 \
  job/$REPRO_PREFIX-job-2 \
  workloadpriorityclass/$REPRO_PREFIX-prio-1 \
  workloadpriorityclass/$REPRO_PREFIX-prio-2 \
  lq/$REPRO_PREFIX-lq \
  cq/$REPRO_PREFIX-cq \
  rf/$REPRO_PREFIX-rf
