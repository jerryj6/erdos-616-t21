#!/bin/bash
# resumable: chunk k = [1000k, 1000k+1000); args: start step
cd "$(dirname "$0")"
k=$1
while [ $k -le 65 ]; do
  lo=$((k*1000)); hi=$(( (k+1)*1000 )); [ $hi -gt 65536 ] && hi=65536
  [ -f ref_states_${lo}_${hi}.json ] || nice -n 5 python3 ref_states.py $lo $hi >> run_states.log 2>&1
  k=$((k+$2))
done
