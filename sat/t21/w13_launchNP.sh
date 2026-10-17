#!/bin/bash
# Wave 13: relaunch chain N (CPU 0) and sub-chain P (CPU 1), each with its post-UNSAT certifier.
cd "$(dirname "$0")"
W12CPU=0 setsid nohup ./w12_run.sh N sel=0,1,2,11,12,15,16,21,22,23 per=3 maxrounds=12 > /dev/null 2>&1 &
W12CPU=1 setsid nohup ./w12_run.sh P sel=0,1,2 per=3 maxrounds=20 > /dev/null 2>&1 &
sleep 3
setsid nohup ./w12_after.sh N > /dev/null 2>&1 &
setsid nohup ./w12_after.sh P > /dev/null 2>&1 &
