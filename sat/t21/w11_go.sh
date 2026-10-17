#!/bin/bash
# usage: w11_go.sh BRANCH TAG [opts...]   (one <=1150 s chunk, background-safe)
cd "$(dirname "$0")"
BR=$1; TAG=$2; shift 2
timeout 1150 nice -n 2 python3 w11_exact.py $BR $TAG "$@" > $TAG.log 2>&1
