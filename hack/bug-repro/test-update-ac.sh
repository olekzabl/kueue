#!/bin/bash

source common-macros.sh

CLUSTERS="kind-manager,kind-worker1,kind-worker2"

mkclear
mkapply setup1.yaml

kubectl config use-context kind-manager

kcfg -f config1.yaml

kubectl apply -f mk-ac-w1-only.yaml

logs_start

echo "*** ADMISSIONCHECK POINTING TO 1-WORKER MKCONFIG ***"

ksend -n 2 -d 120 job1.yaml

sleep 5

print_wl -c $CLUSTERS

echo "*** SWITCHING ADMISSION CHECK TO 2-WORKER MKCONFIG ***"

kubectl apply -f mk-ac-orig.yaml

for i in $(seq 5); do
  sleep 10
  echo "*** After ${i}0 seconds: ***"
  print_wl -c $CLUSTERS
done

echo "*** SUBMITTING A NEW JOB ***"

ksend job1.yaml

sleep 5

print_wl -c $CLUSTERS

