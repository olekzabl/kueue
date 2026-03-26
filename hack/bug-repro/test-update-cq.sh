#!/bin/bash

source common-macros.sh

CLUSTERS="kind-manager,kind-worker1,kind-worker2"

mkclear
mkapply setup1.yaml

kubectl config use-context kind-manager

kcfg -f config1.yaml

kubectl apply -f cq-w1-only.yaml

logs_start

echo "*** CQ POINTING TO 1-WORKER ADMISSIONCHECK ***"

ksend -n 2 -d 120 job1.yaml

sleep 5

print_wl -c $CLUSTERS

echo "*** SWITCHING CQ TO 2-WORKER ADMISSIONCHECK ***"

kubectl apply -f cq-orig.yaml

sleep 10
echo "*** After 10 seconds: ***"
print_wl -c $CLUSTERS

