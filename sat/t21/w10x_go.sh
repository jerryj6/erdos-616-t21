#!/bin/bash
# usage: w10x_go.sh BRANCH TAG [args...]   (background, 19-min cap, nice)
cd "$(dirname "$0")"
setsid nohup timeout 1150 nice -n 2 python3 w10x_exact.py "$@" > "w10x_$2.log" 2>&1 &
