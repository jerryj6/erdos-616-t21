#!/bin/bash
# Wave 12 resume: (re)launch chain N driver + post-UNSAT certifier in the background.
cd "$(dirname "$0")"
[ -f w12_N_PAUSED ] && { echo "chain N paused: see w12_N_PAUSED; use w13_launchTU.sh"; exit 0; }
setsid nohup ./w12_run.sh N sel=0,1,2,11,12,15,16,21,22,23 per=3 maxrounds=12 > /dev/null 2>&1 &
sleep 3
setsid nohup ./w12_after.sh N > /dev/null 2>&1 &
