#!/bin/bash
# usage: w11_ctrl.sh BRANCH CORETAG   -> certificate (DRAT + drat-trim) + drop-one-kind controls + nonk + noSB
cd "$(dirname "$0")"; BR=$1; T=$2; LOG=${T}_cert.log
echo "== (resumed after sandbox restart)" >> $LOG
:
:
for k in L D1 SA W7 R3 TT; do
  echo "== control drop=$k" >> $LOG
  timeout 900 nice -n 2 python3 w10x_cert.py $BR $T drop=$k >> $LOG 2>&1
  rm -f w10x_${T}_drop-$k.cnf w10x_${T}_drop-$k.cnf.drat
done
echo "== control nonk" >> $LOG
timeout 900 nice -n 2 python3 w10x_cert.py $BR $T nonk >> $LOG 2>&1
rm -f w10x_${T}_nonk.cnf w10x_${T}_nonk.cnf.drat
echo "== no symmetry breaking" >> $LOG
W10X_NOSB=1 timeout 1150 nice -n 2 python3 w10x_cert.py $BR $T >> $LOG 2>&1
echo DONE >> $LOG
