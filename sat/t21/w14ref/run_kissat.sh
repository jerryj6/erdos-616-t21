#!/bin/bash
# independent UNSAT (own solver run, own DRAT) of the small case CNFs
cd "$(dirname "$0")"; K=../../tools/kissat; DT=../../tools/drat-trim
for c in 15116 17917 14968; do
  [ -f ks_$c.done ] && continue
  nice -n 5 timeout 3000 $K -q --no-binary ../w14/w14_cert2_$c.cnf /tmp/ks_$c.drat > ks_$c.log 2>&1
  echo "kissat exit $?" >> ks_$c.log
  nice -n 5 $DT ../w14/w14_cert2_$c.cnf /tmp/ks_$c.drat -t 20000 >> ks_$c.log 2>&1
  rm -f /tmp/ks_$c.drat; touch ks_$c.done
done
