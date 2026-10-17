#!/bin/bash
cd "$(dirname "$0")"; export PYTHONPATH=$PWD/pylib
for c in 15116 17917 14968 certdead 15954 16054; do
  [ -f cov_$c.done ] && continue
  if [ $c = certdead ]; then f=../w14/w14_certdead.cnf; else f=../w14/w14_cert2_$c.cnf; fi
  nice -n 5 python3 ref_cov.py $f > cov_$c.log 2>&1 && touch cov_$c.done
done
