#!/bin/bash
# Wave 11e orchestrator: C (9 gamma singles) -> if C is realized, A (13 singles of the pairs among P1,P2,P3) -> if A is
# realized, F (all 24).  UNSAT of any instance implies UNSAT of F (sub-instance = relaxation); w11e_queue.sh then runs
# w11e_finish.sh (certificate + drat-trim + controls).  Each chunk < 20 min.
cd "$(dirname "$0")"
while pgrep -f "^python3 w11e_sub.py run C " > /dev/null; do sleep 10; done
./w11e_queue.sh C 8
[ -f w11e_C.UNSAT ] && exit 0
if [ -f w11_C_real.json ]; then
  python3 w11_pack.py >> w11e_chain.log 2>&1
  ./w11e_queue.sh A 8
  [ -f w11e_A.UNSAT ] && exit 0
  if [ -f w11_A_real.json ]; then
    python3 w11_pack.py >> w11e_chain.log 2>&1
    ./w11e_queue.sh F 8
  fi
fi
