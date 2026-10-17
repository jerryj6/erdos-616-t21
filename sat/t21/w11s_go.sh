#!/bin/bash
cd "$(dirname "$0")"
timeout 1190 nice -n 1 python3 w11_sub.py run $1 ${2:-1120} >> w11s_$1.out 2>&1
