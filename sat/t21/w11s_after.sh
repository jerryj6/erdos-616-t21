#!/bin/bash
cd "$(dirname "$0")"
while pgrep -f "w11_sub.py run $1" > /dev/null; do sleep 10; done
./w11s_queue.sh $1 ${2:-4}
