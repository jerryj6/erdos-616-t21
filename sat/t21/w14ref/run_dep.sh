#!/bin/bash
cd "$(dirname "$0")"; export PYTHONPATH=$PWD/pylib
for c in 15116 17917 14968 15954 16054; do
  [ -f dep_$c.done ] && continue
  nice -n 5 python3 ref_dep.py $c > dep_$c.log 2>&1 && touch dep_$c.done
done
[ -f dep_certdead.done ] || { nice -n 5 python3 ref_dep.py certdead > dep_certdead.log 2>&1 && touch dep_certdead.done; }
