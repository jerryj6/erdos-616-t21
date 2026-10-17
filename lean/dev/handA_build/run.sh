#!/bin/bash
cd /tmp/handA
cp work/e616lean/HandA.lean HandA.lean
export LEAN_PATH=/tmp/E/lib:/tmp/lean-tc/lib/lean:/tmp/handA
rm -f HandA.done
S=$(date +%s); timeout 1100 nice /tmp/lean-tc/bin/lean HandA.lean > HandA.out 2>&1; echo "exit $? time $(( $(date +%s) - S ))s" > HandA.done
