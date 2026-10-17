#!/bin/bash
cd "$(dirname "$0")"
while pgrep -f "w11_ctrl_resume.sh" > /dev/null; do sleep 10; done
for L in J04 J31; do
  echo "== edge-drop control $L" >> w11n34x1_core_edgectrl.log
  timeout 1100 nice -n 2 python3 w10x_cert.py nok4:3,4 w11n34x1_core_no$L >> w11n34x1_core_edgectrl.log 2>&1
done
echo DONE >> w11n34x1_core_edgectrl.log
