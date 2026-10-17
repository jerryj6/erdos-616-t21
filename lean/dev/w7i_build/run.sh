#!/bin/bash
# Rebuild env (if needed) and check W7I.lean; logs go to work/e616lean/w7i_build/ (persistent).
P=/workspace/projects/ca240fa4-1a94-4a1e-9ee4-131487283720; D=$P/work/e616lean/w7i_build
TC=/workspace/.elan/toolchains/leanprover--lean4---v4.35.0
exec > $D/run.log 2>&1
date
while pgrep -f 'e616lean/setup.sh' > /dev/null; do sleep 5; done
[ -f /tmp/E/ok ] && [ -x /tmp/lean-tc/bin/lean ] || bash $P/work/e616lean/setup.sh
# missing pieces of the fast toolchain copy (see md): core .ir.sig files and Lake
if [ ! -f /tmp/lean-tc/sig.ok ]; then
  (cd $TC/lib/lean && find . -name '*.ir.sig' -print0 | xargs -0 cp -n --parents -t /tmp/lean-tc/lib/lean/)
  (cd $TC/lib/lean && cp -rn Lake Lake.olean Lake.olean.private Lake.olean.server Lake.ir Lake.ir.sig /tmp/lean-tc/lib/lean/)
  touch /tmp/lean-tc/sig.ok
fi
date; echo ENVREADY
mkdir -p /tmp/w7 && cd /tmp/w7
cp $P/work/e616lean/Full.lean E616Full.lean; cp $P/work/e616lean/W7I.lean W7I.lean; cp $P/work/e616lean/HandA.lean HandA.lean
md5sum E616Full.lean W7I.lean HandA.lean
cp W7I.lean W7ICheck.lean
for t in W7I.W7I_leaf W7I_cross tri_false mkTri U_sub_W U_le4 U_ge3 step1 step2 step3_core step3 star; do echo "#print axioms Erdos616R21.$t" >> W7ICheck.lean; done
cp W7I.lean W7INeg.lean; printf '\n-- negative control: must FAIL\nexample : (1:ℕ) = 2 := rfl\n' >> W7INeg.lean
cat > Glue.lean <<'EOG'
import HandA
import W7I
/-- HandA's leaf hypothesis `W7I_leaf` is discharged by W7I.lean. -/
theorem W7I_leaf_holds : Erdos616R21.W7I_leaf := Erdos616R21.W7I.W7I_leaf
#print axioms W7I_leaf_holds
EOG
export LEAN_PATH=/tmp/E/lib:/tmp/lean-tc/lib/lean:/tmp/w7
run() { n=$1; shift; S=$(date +%s); nice python3 $D/rssrun.py $D/$n.out /tmp/lean-tc/bin/lean "$@" > $D/$n.rc; echo "$n: exit $(cut -d' ' -f1 $D/$n.rc) time $(( $(date +%s) - S ))s maxRSS_kB $(cut -d' ' -f2 $D/$n.rc)" | tee -a $D/summary.txt; }
rm -f $D/summary.txt
run E616Full -o E616Full.olean E616Full.lean
run W7I -o W7I.olean W7I.lean
run W7ICheck W7ICheck.lean
run W7INeg W7INeg.lean
run HandA -o HandA.olean HandA.lean
run Glue Glue.lean
date; echo ALLDONE
