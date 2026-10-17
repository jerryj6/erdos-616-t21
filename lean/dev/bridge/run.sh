#!/bin/bash
# run.sh FILE [extra lean args] : background lean run, FILE.out / FILE.done
f=$1; shift
cd work/e616lean/bridge
export LEAN_PATH=$PWD:work/e616lrat:/tmp/E/lib:/tmp/lean-tc/lib/lean
rm -f $f.done
S=$(date +%s); nice /tmp/lean-tc/bin/lean "$@" $f > $f.out 2>&1; echo "exit $? time $(( $(date +%s) - S ))s" > $f.done
