#!/bin/bash

source common-macros.sh

CLUSTERS="manager worker1 worker2"

mkclear
mkapply setup1.yaml

kcfg -c kind-manager -g MultiKueueRedoAdmissionOnEvictionInWorker=true

logs_start

ksend -c kind-manager -n 6 job1.yaml
sleep 5
ksend -c kind-manager -p 10 job1.yaml
sleep 10

for cluster in $CLUSTERS; do
  echo "--- On cluster $cluster: ---"
  print_wl -c kind-$cluster
  print_logs -c kind-$cluster > $cluster.log
done

