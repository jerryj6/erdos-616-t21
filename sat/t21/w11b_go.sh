#!/bin/bash
# one checkpointed Benders chunk (< 20 min)
cd "$(dirname "$0")"
W11BASE=2 timeout 1190 nice -n 1 python3 w11_benders.py run ${1:-1120} maxk=4 >> w11b_runs.out 2>&1
