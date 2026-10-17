#!/bin/bash
# sequential checkpointed chunks (each < 20 min) of the EXTENDED-oracle Benders (w11e_sub.py) for sub-instance $1, at most $2 chunks.
# On STALL: try a literal realization (w11_realize.py) and check it with the independent w10x_verify.py.
cd "$(dirname "$0")"
for i in $(seq 1 ${2:-4}); do
  [ -f w11e_$1.UNSAT ] && break
  [ -f w11e_$1_stall.json ] && break
  timeout 1190 nice -n 1 python3 w11e_sub.py run $1 1120 >> w11e_$1.out 2>&1
done
if [ -f w11e_$1_stall.json ] && [ ! -f w11_$1_real.json ]; then
  timeout 1000 nice -n 1 python3 w11_realize.py $1 900 w11e_$1_stall.json nofv >> w11e_$1_realize.log 2>&1
  [ -f w11_$1_real.json ] && timeout 900 python3 w10x_verify.py w11_$1_real.json >> w11e_$1_realize.log 2>&1
fi

[ -f w11e_$1.UNSAT ] && [ ! -f w11e_$1_cert.log ] && ./w11e_finish.sh $1
