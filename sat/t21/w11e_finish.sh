#!/bin/bash
# on master UNSAT of TAG (extended oracle): dump all applicable cuts, certificate (CaDiCaL DRAT + drat-trim), nocuts control,
# independent recheck of all certificates, per-certificate encoder test.
cd "$(dirname "$0")"
T=$1; L=w11e_${T}_cert.log
echo "== finish $T $(date -u)" >> $L
timeout 900 python3 w11e_sub.py dump $T >> $L 2>&1
timeout 1150 python3 w11e_cert.py $T >> $L 2>&1
timeout 1150 python3 w11e_cert.py $T nocuts >> $L 2>&1
timeout 900 python3 w11e_recheck.py >> $L 2>&1
timeout 600 python3 w11e_enctest.py 300 21 >> $L 2>&1
echo "== finish done $(date -u)" >> $L
