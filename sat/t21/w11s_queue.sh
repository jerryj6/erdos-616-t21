#!/bin/bash
# sequential checkpointed chunks (each < 20 min) for sub-instance $1, at most $2 chunks; stops on UNSAT or STALL
cd "$(dirname "$0")"
for i in $(seq 1 ${2:-4}); do
  [ -f w11s_$1.UNSAT ] && break
  [ -f w11s_$1_stall.json ] && break
  timeout 1190 nice -n 1 python3 w11_sub.py run $1 1120 >> w11s_$1.out 2>&1
done
