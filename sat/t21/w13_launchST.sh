#!/bin/bash
# Wave 13 resume after a sandbox restart: chain S (CPU 1) and sub-chain T (CPU 0), each with its post-UNSAT certifier.
cd "$(dirname "$0")"
for R in S T; do echo "== relaunch $(date -u) (sandbox restart)" >> $(python3 -c "import json;print(json.load(open('w12_${R}_state.json'))['tag'])").log; done
W12CPU=1 setsid nohup ./w12_run.sh S sel=0,1,2 per=3 maxrounds=20 mt=1 avoidB=$(cat w13_redundantB.txt) > /dev/null 2>&1 &
W12CPU=0 setsid nohup ./w12_run.sh T sel=0,1,2 per=3 maxrounds=20 mt=1 avoidB=$(cat w13_redundantB.txt) > /dev/null 2>&1 &
sleep 3
setsid nohup ./w12_after.sh S > /dev/null 2>&1 &
setsid nohup ./w12_after.sh T > /dev/null 2>&1 &
