#!/bin/bash

logs_start() {
  export LOGS_START_TIME=$(date -Iseconds)
  echo "Cutting logs horizon at: $LOGS_START_TIME"
}

logs_start

mkclear() {
  echo "*** Cleaning up clusters ***"
  export kcnt=0
  for cluster in manager worker1 worker2; do
    echo "--- Cleaning up $cluster ---"
      for kind in job wl kwl lq cq rf admissioncheck cohort workloadpriorityclass; do
        kubectl --context kind-$cluster delete --all -A $kind >/dev/null 2>/dev/null
    done
  done
  echo "*** Cleanup done. ***"
}

mkapply() {
  echo "*** Creating Kueue objects ***"
  for cluster in manager worker1 worker2; do
    echo "--- Creating in $cluster ---"
    if [[ "$cluster" == "manager" ]]; then
      labels="all $cluster"
    else
      labels="all all-workers $cluster"
    fi
    for value in $labels; do
      kubectl --context kind-$cluster apply -l test-cluster=$value -f $1
    done
  done
  echo "*** Creating Kueue objects done. ***"
}

declare -i kcnt

ksend() {
  lq=lq1
  ctx=
  prio=
  n=1
  while true; do
    if [[ "$1" == "-l" ]]; then
      lq="$2"
      shift 2
    elif [[ "$1" == "-c" ]]; then
      ctx="--context $2"
      shift 2
    elif [[ "$1" == "-n" ]]; then
      n="$2"
      shift 2
    elif [[ "$1" == "-p" ]]; then
      prio="prio-$2"
      shift 2
    else
      break
    fi
  done
  if [[ "$#" == "0" ]]; then
    echo "Usage: ksend [-c ctx] [-l lq] [-p prio] [-n times] YAML_FILE"
    return 0
  fi
  fn="$1"
  for _ in $(seq $n); do
    export kcnt=$kcnt+1
    cat "$fn" | sed s/\$lq/$lq/g | sed s/\$prio/$prio/g | sed s/\$id/$kcnt/g |
      kubectl $ctx create -f -
  done
}

kcfg() {
  ctx=
  fn=
  gates=
  level=
  while true; do
    if [[ "$1" == "-c" ]]; then
      ctx="--context $2"
      shift 2
    elif [[ "$1" == "-f" ]]; then
      fn="$2"
      shift 2
    elif [[ "$1" == "-l" ]]; then
      level="$2"
      shift 2
    elif [[ "$1" == "-g" ]]; then
      gates="$2"
      shift 2
    else
      break
    fi
  done
  if [[ "$fn" == "" && "$level" == "" && "$gates" == "" ]]; then
    echo "Usage: kcfg [-c ctx] [-f CONFIG_YAML_FILE] [-g FeatGate1=true,FeatGate2=true] [-l LOG_LEVEL]"
    echo "No updates requested. Exiting."
    return 0
  fi
  echo "*** Applying Kueue config changes ***"
  if [[ "$fn" != "" ]]; then
    echo "--- Applying the new Configuration YAML ---"
    kubectl $ctx apply -f "$fn"
  fi
  if [[ "$level" != "" ]]; then
    echo "--- Applying the new log level ---"
    kubectl $ctx apply --server-side --force-conflicts -f <(
      kubectl $ctx get deployment kueue-controller-manager -n kueue-system -o yaml | sed -r "s/--zap-log-level=[0-9]+/--zap-log-level=$level/g")
  fi
  if [[ "$gates" != "" ]]; then
    gates="MultiKueueAllowInsecureKubeconfigs=true,$gates"
    echo "--- Applying the new feature gates (incl. insecure configs) ---"
    kubectl $ctx apply --server-side --force-conflicts -f <(
      kubectl $ctx get deployment kueue-controller-manager -n kueue-system -o yaml | sed -r "s/--feature-gates=.+/--feature-gates=$gates/g")
  fi
  echo "--- Restarting Kueue manager pods ---"
  kubectl $ctx delete pods --all -n kueue-system
  echo "--- Waiting for the new pods to be ready ---"
  kubectl $ctx wait deploy/kueue-controller-manager -n kueue-system --for=condition=available --timeout=5m
  echo "--- Waiting 2s more to prevent webhook races ---"
  sleep 2
  echo "*** Done. ***"
}

print_wl() {
  ctx=
  while true; do
    if [[ "$1" == "-c" ]]; then
      ctx="--context $2"
      shift 2
    else
      break
    fi
  done
  if [[ "$#" == "0" ]]; then
    kubectl $ctx get kwl
  else
    kubectl $ctx get kwl $(kubectl $ctx get kwl --no-headers -o custom-columns=name:.metadata.name | grep "\-$1-") -o yaml
  fi
}

print_logs() {
  ctx=
  while true; do
    if [[ "$1" == "-c" ]]; then
      ctx="--context $2"
      shift 2
    else
      break
    fi
  done
  pod_name="$(kubectl get pods -n kueue-system --no-headers | cut -f1 -d\ )"
  kubectl logs -n kueue-system "$pod_name" --since-time "$LOGS_START_TIME"
}

check_test_targets () {
  grep -E test-cluster:\|\#\#\# *.yaml
}

