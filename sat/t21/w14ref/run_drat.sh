#!/bin/bash
# referee re-run of drat-trim on every certificate (resumable). Writes drat_<case>.log; core to drat_<case>.core
cd "$(dirname "$0")"
W=../w14; DT=../../tools/drat-trim
for c in 15116 17917 14968 15954 16054; do
  [ -f drat_$c.done ] && continue
  nice -n 10 $DT $W/w14_cert2_$c.cnf $W/w14_cert2_$c.drat -t 20000 -c drat_$c.core > drat_$c.log 2>&1
  touch drat_$c.done
done
if [ ! -f drat_dead.done ]; then
  nice -n 10 $DT $W/w14_certdead.cnf $W/w14_certdead.drat -t 20000 > drat_dead.log 2>&1; touch drat_dead.done
fi
