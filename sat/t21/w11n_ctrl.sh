#!/bin/bash
# Wave 11 noK4: certificate + drop-one-kind controls + nonk + noSB (= w11_ctrl.sh, kinds incl. N24, TT skipped if absent)
export PYTHONPATH=work/e616/pylib:$PYTHONPATH
cd "$(dirname "$0")"; BR=$1; T=$2; LOG=${T}_cert.log
echo "== certificate $(date -u)" > $LOG
timeout 1150 nice -n 2 python3 w10x_cert.py $BR $T >> $LOG 2>&1
sha256sum w10x_${T}.cnf w10x_${T}.cnf.drat > w10x_${T}_cert.sha256 2>/dev/null
for k in N24 L D1 SA W7 R3 TT; do
  if ! python3 -c "import json,sys; sys.exit(0 if any(i[0].lstrip('X')=='$k' for i in json.load(open('w10x_${T}.json'))['inst']) else 1)"; then echo "== control drop=$k: kind absent from instance list (vacuous)" >> $LOG; continue; fi
  echo "== control drop=$k" >> $LOG
  timeout 900 nice -n 2 python3 w10x_cert.py $BR $T drop=$k >> $LOG 2>&1
  rm -f w10x_${T}_drop-$k.cnf w10x_${T}_drop-$k.cnf.drat
done
echo "== control nonk" >> $LOG
timeout 900 nice -n 2 python3 w10x_cert.py $BR $T nonk >> $LOG 2>&1
rm -f w10x_${T}_nonk.cnf w10x_${T}_nonk.cnf.drat
echo "== no symmetry breaking" >> $LOG
W10X_NOSB=1 timeout 1150 nice -n 2 python3 w10x_cert.py $BR $T >> $LOG 2>&1
rm -f w10x_${T}_nosb.cnf.drat
echo "DONE $(date -u)" >> $LOG
