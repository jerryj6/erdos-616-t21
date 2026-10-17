#!/bin/bash
# Wave 10 exact-outside follow-up queue (N-noK4 classes (3,3) and (3,4), 19 first-generation singles, K = KB bound 114).
# Each chunk <= 1150 s; on UNSAT: core extraction, DRAT certificate (drat-trim), control 'nonk'; on violation-free SAT: literal verify.
cd "$(dirname "$0")"
Q=w10x_queue.log
while pgrep -f "w10x_exact.py nok4:3,3 n33g1" > /dev/null; do sleep 10; done
for job in "nok4:3,3 n33g1" "nok4:3,4 n34g1"; do
  set -- $job; BR=$1; TAG=$2
  for chunk in 1 2 3; do
    [ -f w10x_$TAG.UNSAT ] && break
    grep -q "VIOLATION-FREE" w10x_$TAG.log 2>/dev/null && break
    echo "$(date -u +%FT%TZ) $TAG chunk $chunk" >> $Q
    [ -f w10x_$TAG.log ] && cat w10x_$TAG.log >> w10x_${TAG}_all.log
    timeout 1150 nice -n 2 python3 w10x_exact.py $BR $TAG gen1auto=1 eager2=1 tlim=1000 maxadd=800 > w10x_$TAG.log 2>&1
    tail -1 w10x_$TAG.log >> $Q
  done
  if [ -f w10x_$TAG.UNSAT ]; then
    timeout 1150 nice -n 2 python3 w10x_core.py $BR $TAG rounds=2 > w10x_${TAG}_core.log 2>&1
    timeout 1150 nice -n 2 python3 w10x_cert.py $BR ${TAG}_core > w10x_${TAG}_cert.log 2>&1
    timeout 900 nice -n 2 python3 w10x_cert.py $BR ${TAG}_core nonk > w10x_${TAG}_ctrl_nonk.log 2>&1
    rm -f w10x_${TAG}_core_nonk.cnf w10x_${TAG}_core_nonk.cnf.drat
    echo "$(date -u +%FT%TZ) $TAG UNSAT; cert: $(grep -E 's VERIFIED|s NOT' w10x_${TAG}_cert.log | head -1); nonk: $(grep solve w10x_${TAG}_ctrl_nonk.log)" >> $Q
  elif grep -q "VIOLATION-FREE" w10x_$TAG.log; then
    timeout 900 python3 w10x_verify.py w10x_${TAG}_real.json nk > w10x_${TAG}_verify.log 2>&1
    echo "$(date -u +%FT%TZ) $TAG REALIZED; see w10x_${TAG}_verify.log" >> $Q
  else
    echo "$(date -u +%FT%TZ) $TAG not decided after 3 chunks" >> $Q
  fi
done
echo "$(date -u +%FT%TZ) QUEUE DONE" >> $Q
