#!/bin/bash
cd "$(dirname "$0")"; export PYTHONPATH=$PWD/pylib
for lo in $(seq 0 500 18000); do hi=$((lo+500)); [ $hi -gt 18217 ] && hi=18217
  [ -f fc_${lo}_${hi}.npz ] || nice -n 8 python3 ref_fullconf.py $lo $hi >> fc.log 2>&1
done
touch fc.done
