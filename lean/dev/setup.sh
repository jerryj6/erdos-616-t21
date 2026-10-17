#!/bin/bash
# Rebuild /tmp/E (Mathlib closure for Erdos616.lean) from workspace oleans; fast path = tarball.
exec >>/tmp/e616setup.log 2>&1
W=/workspace/projects/ca240fa4-1a94-4a1e-9ee4-131487283720
TAR=$W/work/e616lean/E616lib.tar
[ -x /tmp/lean-tc/bin/lean ] || bash $W/work/leanre/setup.sh   # toolchain part (also builds a closure; fine)
if [ -f $TAR ] && [ ! -f /tmp/E/ok ]; then mkdir -p /tmp/E && tar xf $TAR -C /tmp/E && touch /tmp/E/ok && echo FROMTAR && exit 0; fi
PK=$W/lean/erdos/.lake/packages
if [ -f $W/work/e616lean/mods.txt ]; then cp $W/work/e616lean/mods.txt /tmp/E616mods.txt; else python3 $W/work/leanre/closure.py Mathlib.Data.ENat.Lattice Mathlib.Algebra.BigOperators.Group.Finset.Basic Mathlib.Data.Fintype.Powerset Mathlib.Data.Finset.Prod Mathlib.Data.Fintype.EquivFin Mathlib.Data.Fintype.Card Mathlib.Data.Finset.Powerset > /tmp/E616mods.txt; fi
mkdir -p /tmp/E/lib
while read p m; do
  rel=$(echo $m | tr . /); d=$PK/$p/.lake/build/lib/lean
  mkdir -p /tmp/E/lib/$(dirname $rel)
  for ext in olean olean.server olean.private ir ir.sig; do [ -f /tmp/E/lib/$rel.$ext ] || cp $d/$rel.$ext /tmp/E/lib/$rel.$ext 2>/dev/null; done
done < /tmp/E616mods.txt
(cd $PK/importGraph/.lake/build/lib/lean && find . \( -name '*.olean' -o -name '*.olean.server' -o -name '*.olean.private' -o -name '*.ir' -o -name '*.ir.sig' \) -print0 | xargs -0 cp --parents -n -t /tmp/E/lib/)
touch /tmp/E/ok
(cd /tmp/E && tar cf $TAR.tmp lib ok && mv $TAR.tmp $TAR)
echo BUILT; du -sh /tmp/E
