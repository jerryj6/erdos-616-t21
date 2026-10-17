#!/bin/bash
# usage: w9loop.sh BRANCH TAG [extra args]; restarts the 18-min job until UNSAT/STALL marker or 6 rounds
cd "$(dirname "$0")"
for r in 1 2 3 4 5 6; do
  timeout 1150 python3 w9run.py "$@" tlim=1050 >> w9_$2.log 2>&1
  grep -q -E "UNSAT|STALL" w9_$2.log && break
done
