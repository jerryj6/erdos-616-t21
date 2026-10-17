#!/bin/bash
cd "$(dirname "$0")"
W12CPU=0 setsid nohup ./w12_run.sh T sel=0,1,2 per=3 maxrounds=20 mt=1 avoidB=$(cat w13_redundantB.txt) > /dev/null 2>&1 &
sleep 2; setsid nohup ./w12_after.sh T > /dev/null 2>&1 &
