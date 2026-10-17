#!/usr/bin/env bash
# Re-check, with drat-trim, every case certificate used by the Lean theorem (26 CNF/DRAT pairs).
# Run scripts/fetch_certs.sh first. drat-trim: https://github.com/marijnheule/drat-trim (set DRAT_TRIM to override).
# Expected: 26 lines ending in "s VERIFIED". The two largest (w14_15954, w14_16054) take a few minutes each.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DT="${DRAT_TRIM:-drat-trim}"
R="$ROOT/data/raw/e616"
LOG="$ROOT/data/drat-check.log"; : > "$LOG"
pairs=()
for t in 24x_0 24x_1 24x_2 24x_3 24x_4 24x_5 24x_6 33_0 33_1 33_2 33_3 33_4 33_5 33_6 33_7 34_0 34_1 34_2 34_3 34_4; do
  pairs+=("$R/w11ref/tr/tree_$t")
done
for n in 14968 15116 15954 16054 17917; do pairs+=("$R/t21/w14/w14_cert2_$n"); done
pairs+=("$R/t21/w14/w14_certdead")
fail=0
for p in "${pairs[@]}"; do
  res=$("$DT" "$p.cnf" "$p.drat" -t 20000 2>&1 | tee -a "$LOG" | grep -a -o 's VERIFIED\|s NOT VERIFIED' | tail -1)
  echo "$(basename "$p"): ${res:-ERROR}"
  [ "$res" = "s VERIFIED" ] || fail=1
done
[ $fail = 0 ] && echo "all ${#pairs[@]} certificates VERIFIED" || { echo "some certificates FAILED (see $LOG)"; exit 1; }
