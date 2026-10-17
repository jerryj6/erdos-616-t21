#!/bin/bash
# Rebuild /tmp Lean env from workspace copies (no network). Log: /tmp/leanre_setup.log
exec >>/tmp/leanre_setup.log 2>&1
set -x
W=/workspace/projects/ca240fa4-1a94-4a1e-9ee4-131487283720
PK=$W/lean/erdos/.lake/packages
TC=/workspace/.elan/toolchains/leanprover--lean4---v4.35.0
mkdir -p /tmp/lean-tc/bin /tmp/E/lib
[ -x /tmp/lean-tc/bin/lean ] || { cp $TC/bin/lean /tmp/lean-tc/bin/; }
if [ ! -d /tmp/lean-tc/lib/lean/Init ]; then
  mkdir -p /tmp/lean-tc/lib
  (cd $TC/lib && find lean -maxdepth 1 -name '*.so' | xargs -r -I{} cp --parents {} /tmp/lean-tc/lib/)
  (cd $TC/lib/lean && find Init Std Lean Init.* Std.* Lean.* -maxdepth 0 2>/dev/null; true)
  (cd $TC/lib && find lean \( -path 'lean/Init*' -o -path 'lean/Std*' -o -path 'lean/Lean*' \) \( -name '*.olean' -o -name '*.olean.server' -o -name '*.olean.private' -o -name '*.ir' \) -print0 | xargs -0 cp --parents -t /tmp/lean-tc/lib/)
fi
ls $TC/lib
echo TCDONE
python3 $W/work/leanre/closure.py "$@" > /tmp/E/mods.txt
wc -l /tmp/E/mods.txt
while read p m; do
  rel=$(echo $m | tr . /)
  d=$PK/$p/.lake/build/lib/lean
  mkdir -p /tmp/E/lib/$(dirname $rel)
  for ext in olean olean.server olean.private ir; do [ -f $d/$rel.$ext ] && [ ! -f /tmp/E/lib/$rel.$ext ] && cp $d/$rel.$ext /tmp/E/lib/$rel.$ext; done
done < /tmp/E/mods.txt
du -sh /tmp/E /tmp/lean-tc
echo ALLDONE
