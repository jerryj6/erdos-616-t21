#!/bin/bash
# usage: run_conf.sh TAG [drop] ; resumable (skips finished chunks)
cd "$(dirname "$0")"; export PYTHONPATH=$PWD/../../t21/w14ref/pylib:$PWD/../../pylib; ulimit -v 2000000
TAG=$1; DROP=${2:-0}; D=cf_$TAG; [ "$DROP" != 0 ] && D=${D}_d$DROP
NT=$(python3 -c "import numpy as np;print(len(np.load('st_$TAG.npz')['tr']))")
for lo in $(seq 0 200 $NT); do hi=$((lo+200)); [ $hi -gt $NT ] && hi=$NT
  [ -f $D/r_${lo}_${hi}.npy ] || taskset -c 0 nice -n 10 python3 tr_conf.py $TAG $lo $hi $DROP >> conf_$TAG.log 2>&1
done
touch $D.done
