#!/bin/bash
# resume w11n_ctrl.sh after a sandbox restart: nonk, then noSB (with DRAT), then drop=R3 again
export PYTHONPATH=work/e616/pylib:$PYTHONPATH
cd "$(dirname "$0")"; BR=$1; T=$2; LOG=${T}_cert.log
echo "== (resumed after sandbox restart $(date -u); drop=R3 drat-trim was killed by the restart)" >> $LOG
rm -f w10x_${T}_drop-R3.cnf w10x_${T}_drop-R3.cnf.drat
echo "== control nonk" >> $LOG
timeout 900 nice -n 2 python3 w10x_cert.py $BR $T nonk >> $LOG 2>&1
rm -f w10x_${T}_nonk.cnf w10x_${T}_nonk.cnf.drat
echo "== no symmetry breaking" >> $LOG
W10X_NOSB=1 timeout 1190 nice -n 2 python3 w10x_cert.py $BR $T >> $LOG 2>&1
rm -f w10x_${T}_nosb.cnf.drat
echo "DONE $(date -u)" >> $LOG
