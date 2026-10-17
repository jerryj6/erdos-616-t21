#!/bin/bash
# after all case certificates verified: extract drat-trim cores (-c) and independently re-check every core CONF clause.
cd "$(dirname "$0")"; export PYTHONPATH=../../pylib
echo $$ > run_indep_all.pid
while [ ! -f w14_cert2_17917.trim ]; do sleep 60; done
for c in certdead cert2_15116 cert2_15954 cert2_16054 cert2_17917; do
  [ -f w14_$c.core ] || taskset -c 0 nice -n 10 ../../tools/drat-trim w14_$c.cnf w14_$c.drat -t 3000 -c w14_$c.core > w14_$c.core.trimlog 2>&1
  until grep -q DONE w14_indep_$c.log 2>/dev/null; do taskset -c 0 nice -n 15 python3 w14_indep_core.py w14_$c.core >> w14_indep_$c.log 2>&1 || sleep 5; done
done
touch w14_indep_all.DONE
