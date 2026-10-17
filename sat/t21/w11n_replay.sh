#!/bin/bash
# usage: w11n_replay.sh BRANCH TAG LOG OUTTAG  (replay with proof -> trim -c -> map; OUTTAG is the scratch name)
export PYTHONPATH=work/e616/pylib:$PYTHONPATH
cd "$(dirname "$0")"; BR=$1; T=$2; L=$3; R=${T}_rp; LOGF=${T}_replay.log
echo "== replay $(date -u)" > $LOGF
timeout 1190 nice -n 2 python3 w11n_replay.py $BR $T $L >> $LOGF 2>&1 || { echo FAIL replay >> $LOGF; exit 1; }
echo "== trim $(date -u)" >> $LOGF
timeout 1190 nice -n 2 python3 w11n_dratcore.py trim $T >> $LOGF 2>&1
[ -s w11dc_tmp/w11dc_$T.core ] || { echo FAIL trim >> $LOGF; exit 1; }
echo "== map $(date -u)" >> $LOGF
timeout 1150 nice -n 2 python3 w11n_dratcore.py map $BR $T >> $LOGF 2>&1 || { echo FAIL map >> $LOGF; exit 1; }
echo "DONE $(date -u)" >> $LOGF
