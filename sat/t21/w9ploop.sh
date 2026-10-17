#!/bin/bash
cd "$(dirname "$0")"
for r in 1 2 3 4 5 6; do
  timeout 1150 python3 w9pool.py "$@" tlim=1050 >> w9pool_$2.log 2>&1
  grep -q -E "UNSAT|CLOSED" w9pool_$2.log && break
done
