#!/bin/bash
D=work/e616lean/bridge
for f in "$@"; do $D/run.sh $D/$f.lean -o $D/$f.olean; grep -q "exit 0" $D/$f.lean.done || break; done
