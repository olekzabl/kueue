#!/bin/bash

source common-macros.sh

CLUSTERS="kind-manager,kind-worker1,kind-worker2"

mkclear
mkapply setup1.yaml

kubectl config use-context kind-manager

kcfg -f config1.yaml

kubectl apply -f mkc-w1-only.yaml

logs_start

echo "*** 1-WORKER MKCONFIG ***"

ksend -n 2 job1.yaml

sleep 5

print_wl -c $CLUSTERS

echo "*** ADDING 2ND WORKER TO MKCONFIG ***"

kubectl apply -f mkc-full.yaml

sleep 10
echo "*** After 10 seconds: ***"
print_wl -c $CLUSTERS

