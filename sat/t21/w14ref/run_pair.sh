#!/bin/bash
cd "$(dirname "$0")"; export PYTHONPATH=$PWD/pylib
for c in 15116 17917 14968 certdead 15954 16054; do
  [ -f pair_$c.done ] && continue
  if [ $c = certdead ]; then f=../w14/w14_certdead.cnf; else f=../w14/w14_cert2_$c.cnf; fi
  nice -n 5 python3 pairref.py ref_states.npz $f > pair_$c.log 2>&1 && touch pair_$c.done
done
