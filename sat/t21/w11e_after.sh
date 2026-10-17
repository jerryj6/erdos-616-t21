#!/bin/bash
# wait for a running w11e_sub chunk of TAG to end, then continue with w11e_queue.sh TAG N
cd "$(dirname "$0")"
while pgrep -f "w11e_sub.py run $1 " > /dev/null; do sleep 10; done
./w11e_queue.sh $1 ${2:-3}
