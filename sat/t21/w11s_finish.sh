#!/bin/bash
# waits for the w11s queue of TAG to end; if the master went UNSAT: dump cuts, certificate + drat-trim, controls, recheck
cd "$(dirname "$0")"
while pgrep -f "w11s_queue.sh $1" > /dev/null; do sleep 20; done
if [ -f w11s_$1.UNSAT ]; then
  timeout 600 python3 w11_sub.py dump $1 >> w11s_$1_cert.log 2>&1
  timeout 1150 python3 w11s_cert.py $1 >> w11s_$1_cert.log 2>&1
  timeout 1150 python3 w11s_cert.py $1 nocuts >> w11s_$1_cert.log 2>&1
  timeout 900 python3 w11b_recheck.py >> w11s_$1_cert.log 2>&1
  timeout 900 python3 w11s_enctest.py $1 60 >> w11s_$1_cert.log 2>&1
fi
