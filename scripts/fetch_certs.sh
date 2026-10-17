#!/usr/bin/env bash
# Download (or take a local copy of) the certificate tarball and lay out data/ for the Lean build and the SAT checks.
#
#   scripts/fetch_certs.sh                     # download from the GitHub release v1.0
#   scripts/fetch_certs.sh /path/to/e616-sat-certs.tar.zst   # use a local copy
#
# Environment: E616_CERTS_URL overrides the download URL.
# Needs: curl, zstd, tar, sha256sum, python3. Disk: about 9 GB (raw tarball contents + data/ layout + LRAT chunks).
#
# Result (all under data/, which is git-ignored):
#   data/raw/...            the tarball contents, unchanged (paths e616/..., e616lrat/...)
#   data/cnf/*.cnf          the 26 CNFs consumed by the Lean certificate modules (links into data/raw)
#   data/lrat/*.lrat        the 26 LRAT proofs (drat-trim -L output, lemma ids renumbered by sat/lrat/renum.py)
#   data/chunks/w14_*/      lem_j.cnf / hints_j.txt blocks for the two large certificates (sat/lrat/split.py, 100 MB)
#   data/out/               written by the Lean build (parser round-trip dumps)
# and checks every file against lean/DATA.sha256.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SHA=189bc3300f63f16ed4203989f381227b46587002e8717099076ae9c4f6510c95
D="$ROOT/data"; mkdir -p "$D"
TAR="${1:-$D/e616-sat-certs.tar.zst}"
if [ ! -f "$TAR" ]; then
  # default: the v1.0 release asset of this repository's GitHub origin
  if [ -z "${E616_CERTS_URL:-}" ]; then
    ORIGIN="$(git -C "$ROOT" remote get-url origin 2>/dev/null || true)"
    SLUG="$(printf '%s' "$ORIGIN" | sed -E 's#(\.git)?$##; s#^.*github\.com[:/]##')"
    [ -n "$SLUG" ] || { echo "cannot determine the GitHub repository; set E616_CERTS_URL or pass the tarball path" >&2; exit 1; }
    E616_CERTS_URL="https://github.com/$SLUG/releases/download/v1.0/e616-sat-certs.tar.zst"
  fi
  URL="$E616_CERTS_URL"
  echo "downloading $URL"; curl -L --fail -o "$TAR" "$URL"
fi
echo "$SHA  $TAR" | sha256sum -c -

if [ ! -f "$D/raw/.done" ]; then
  mkdir -p "$D/raw"
  zstd -dc "$TAR" | tar -xf - -C "$D/raw"
  # the tarball also carries dangling absolute symlinks from the original working tree; drop them
  find "$D/raw" -type l -delete
  touch "$D/raw/.done"
fi
( cd "$D/raw" && sha256sum -c --quiet "$ROOT/sat/SHA256SUMS.members" ) && echo "tarball members: OK"

mkdir -p "$D/cnf" "$D/lrat" "$D/out"
for f in "$D"/raw/e616/w11ref/tr/tree_*.cnf; do ln -sf "$f" "$D/cnf/$(basename "$f")"; done
for n in 14968 15116 15954 16054 17917; do ln -sf "$D/raw/e616/t21/w14/w14_cert2_$n.cnf" "$D/cnf/w14_$n.cnf"; done
ln -sf "$D/raw/e616/t21/w14/w14_certdead.cnf" "$D/cnf/w14_certdead.cnf"
for f in "$D"/raw/e616lrat/lrat/tree_*.lrat "$D"/raw/e616lrat/lrat/w14_*.lrat; do ln -sf "$f" "$D/lrat/$(basename "$f")"; done

# chunked mode for the two large certificates: split the LRAT proof into ~100 MB blocks of RUP lemmas
for n in 15954 16054; do
  N=w14_$n
  if [ ! -f "$D/chunks/$N/split.done" ]; then
    M=$(grep -m1 '^p cnf' "$D/cnf/$N.cnf" | awk '{print $4}')
    ( cd "$D" && python3 "$ROOT/sat/lrat/split.py" "$N" "$M" 100 )
    touch "$D/chunks/$N/split.done"
  fi
done

( cd "$ROOT" && sha256sum -c --quiet lean/DATA.sha256 ) && echo "data/ layout: OK (all files match lean/DATA.sha256)"
