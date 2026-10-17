#!/bin/bash
# usage: w11n_dc_chain.sh BRANCH TAG   (DRAT-based instance core, then certificate + controls on it)
export PYTHONPATH=work/e616/pylib:$PYTHONPATH
cd "$(dirname "$0")"; BR=$1; T=$2; LOG=${T}_dcore.log
echo "== build $(date -u)" > $LOG
timeout 1150 nice -n 2 python3 w11n_dratcore.py build $BR $T >> $LOG 2>&1 || { echo FAIL build >> $LOG; exit 1; }
echo "== solve $(date -u)" >> $LOG
timeout 1190 nice -n 2 python3 w11n_dratcore.py solve $T >> $LOG 2>&1 || { echo FAIL solve >> $LOG; exit 1; }
echo "== trim $(date -u)" >> $LOG
timeout 1190 nice -n 2 python3 w11n_dratcore.py trim $T >> $LOG 2>&1
[ -s w11dc_tmp/w11dc_$T.core ] || { echo FAIL trim >> $LOG; exit 1; }
rm -f w11dc_tmp/w11dc_$T.drat
echo "== map $(date -u)" >> $LOG
timeout 1150 nice -n 2 python3 w11n_dratcore.py map $BR $T >> $LOG 2>&1 || { echo FAIL map >> $LOG; exit 1; }
rm -f w11dc_tmp/w11dc_$T.cnf w11dc_tmp/w11dc_$T.core
echo "DONE $(date -u)" >> $LOG
