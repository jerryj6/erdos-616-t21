#!/bin/bash
# usage: solve.sh NAME  (NAME.cnf exists) -> NAME.res (UNSAT/SAT/UNKNOWN), NAME.drat, NAME.trim ; resumable by markers
cd "$(dirname "$0")"; ulimit -v 2000000; N=$1; T=${2:-1100}
if [ ! -f $N.res ]; then
  taskset -c 0 nice -n 10 ../../tools/kissat -q --time=$T $N.cnf $N.drat > $N.kout 2>&1; rc=$?
  case $rc in 20) echo UNSAT > $N.res;; 10) echo SAT > $N.res; rm -f $N.drat;; *) echo "UNKNOWN rc=$rc $(date -u)" >> $N.unknown; rm -f $N.drat; exit 1;; esac
fi
if [ -z "$SKIPTRIM" ] && grep -q UNSAT $N.res && [ ! -f $N.trim ]; then
  taskset -c 0 nice -n 10 ../../tools/drat-trim $N.cnf $N.drat -t 20000 > $N.trim.tmp 2>&1; mv $N.trim.tmp $N.trim
fi
exit 0
