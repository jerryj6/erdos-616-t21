#!/bin/bash
# no-proof kissat run for SAT-expected controls: NAME [TIME] -> NAME.res (SAT/UNSAT) / NAME.unknown
cd "$(dirname "$0")"; ulimit -v 2000000; N=$1; T=${2:-1100}
[ -f $N.res ] && exit 0
taskset -c 0 nice -n 10 ../../tools/kissat -q --time=$T $N.cnf > $N.kout 2>&1; rc=$?
case $rc in 20) echo "UNSAT (no proof)" > $N.res;; 10) echo SAT > $N.res;; *) echo "UNKNOWN(np) rc=$rc $(date -u)" >> $N.unknown;; esac
