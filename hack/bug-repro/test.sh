#!/bin/bash

source common-macros.sh

CLUSTERS="manager worker1 worker2"

# Clean any earlier Kueue objects:
mkclear

# Create a Kueue object setup:
# - on manager: a CQ fitting 4 instances of "job1"
# - on both workers: a CQ fitting 2 instances of "job1"
mkapply setup1.yaml

kcfg -c kind-manager -g MultiKueueRedoAdmissionOnEvictionInWorker=true

logs_start

# Sumit 6 instances of "job1"
# (2 will be scheduled on each worker; 2 will remain unadmitted)
ksend -c kind-manager -n 6 job1.yaml
sleep 5

# Submit 1 instance of "job1" but with increased priority
ksend -c kind-manager -p 10 job1.yaml
sleep 10

for cluster in $CLUSTERS; do
  echo "--- On cluster $cluster: ---"
  print_wl -c kind-$cluster
  print_logs -c kind-$cluster > $cluster.log
done

