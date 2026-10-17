#!/bin/bash
cd "$(dirname "$0")"
while pgrep -f w10x_ctrl.sh > /dev/null; do sleep 5; done
echo "== gen-1 only (nedges=19, K=KB bound)" >> w10x_n24s_ctrl2.log
timeout 900 nice -n 2 python3 w10x_cert.py nok4:2,4 n24s_core nedges=19 >> w10x_n24s_ctrl2.log 2>&1
true
echo "== no symmetry breaking" >> w10x_n24s_ctrl2.log
W10X_NOSB=1 timeout 900 nice -n 2 python3 w10x_cert.py nok4:2,4 n24s_core >> w10x_n24s_ctrl2.log 2>&1
rm -f w10x_n24s_core_nosb.cnf.drat
echo DONE >> w10x_n24s_ctrl2.log
