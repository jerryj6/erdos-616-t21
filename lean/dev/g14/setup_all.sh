#!/bin/bash
# Fresh-sandbox setup for the G14 bridge: toolchain copy (+ .ir.sig, Lake), Mathlib closure /tmp/E, core G14 modules /tmp/g14,
# Mathlib-side work dir /tmp/g14m (E616Full). Log: /tmp/g14setup.log
exec >>/tmp/g14setup.log 2>&1
W=/workspace/projects/ca240fa4-1a94-4a1e-9ee4-131487283720
TC=/workspace/.elan/toolchains/leanprover--lean4---v4.35.0
[ -x /tmp/lean-tc/bin/lean ] || bash $W/work/leanre/setup.sh
(cd $TC/lib/lean && find . -name '*.ir.sig' -print0 | xargs -0 cp -n --parents -t /tmp/lean-tc/lib/lean/)
cp -rn $TC/lib/lean/Lake* /tmp/lean-tc/lib/lean/
[ -f /tmp/E/ok ] || { mkdir -p /tmp/E && tar xf $W/work/e616lean/E616lib.tar -C /tmp/E && touch /tmp/E/ok; }
echo TC_E_DONE
bash $W/work/e616lean/g14/build.sh
mkdir -p /tmp/g14m; cp $W/work/e616lean/g14/runm.sh /tmp/g14m/run.sh; cp $W/work/e616lean/bridge/E616Full.lean /tmp/g14m/
# restore saved oleans of finished modules (case lemmas etc.)
[ -d $W/work/e616lean/g14/olean ] && cp -n $W/work/e616lean/g14/olean/*.olean /tmp/g14/ 2>/dev/null
cd /tmp/g14m && ./run.sh E616Full && cat E616Full.done
echo SETUP_DONE
