#!/bin/bash
# Wave 12 resume: wait for chain RUN's driver to exit; if it ended UNSAT, extract a core and certify (+ controls) with
# the Wave 11 tools (w10x_core.py, w11n_ctrl.sh = w10x_cert.py + drop-one-kind + nonk + noSB). Log w12_${RUN}_after.log.
export PYTHONPATH=work/e616/pylib
cd "$(dirname "$0")"; RUN=$1; PID=$(cat w12_$RUN.pid); LOG=w12_${RUN}_after.log
while kill -0 $PID 2>/dev/null || pgrep -f "w12_cegar.py $RUN " >/dev/null; do sleep 60; done
echo "driver exited $(date -u)" >> $LOG
T=$(python3 -c "import json;s=json.load(open('w12_${RUN}_state.json'));print(s['tag'] if s.get('result')=='UNSAT' else '')")
[ -z "$T" ] && { echo "not UNSAT; nothing to certify" >> $LOG; exit 0; }
echo "UNSAT at $T; core extraction" >> $LOG
timeout 1150 taskset -c 0 nice -n 2 python3 w10x_core.py k4:3211 $T rounds=3 > ${T}_core.log 2>&1
if [ -f w10x_${T}_core.json ]; then C=${T}_core; else C=$T; fi
echo "certifying $C $(date -u)" >> $LOG
taskset -c 0 ./w11n_ctrl.sh k4:3211 $C
echo "done $(date -u); see ${C}_cert.log" >> $LOG
