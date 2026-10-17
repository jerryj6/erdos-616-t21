#!/bin/bash
cd "$(dirname "$0")"
for a in "nonk" "drop=L" "drop=D1" "drop=SA" "drop=W7" "drop=R3"; do
  echo "== control $a" >> w10x_n24s_ctrl.log
  timeout 600 nice -n 2 python3 w10x_cert.py nok4:2,4 n24s_core $a >> w10x_n24s_ctrl.log 2>&1
  rm -f w10x_n24s_core_*.cnf.drat
done
echo DONE >> w10x_n24s_ctrl.log
