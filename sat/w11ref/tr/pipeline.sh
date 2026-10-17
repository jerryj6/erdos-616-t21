#!/bin/bash
# resumable §5 pipeline (every step skips if its output marker exists)
cd "$(dirname "$0")"; export PYTHONPATH=$PWD/../../t21/w14ref/pylib:$PWD/../../pylib; ulimit -v 2000000
PY="taskset -c 0 nice -n 10 python3"
echo "== pipeline start $(date -u)" >> pipeline.log
full() {  # full(TAG a c flags...) : universe + matrix + Φ + solve
  T=$1; shift
  [ -f st_$T.npz ] || $PY tr_states.py "$@" >> pipeline.log 2>&1
  [ -f cf_$T.done ] || ./run_conf.sh $T
  [ -f phi$T.cnf ] || { $PY tr_cnf.py $T phi$T.cnf.tmp >> pipeline.log 2>&1 && mv phi$T.cnf.tmp phi$T.cnf; }
  ./solve.sh phi$T 1100 >> pipeline.log 2>&1
  echo "phi$T: $(cat phi$T.res 2>/dev/null) $(grep -h 's [A-Z]' phi$T.trim 2>/dev/null) $(date -u)" >> pipeline.log
}
export SKIPTRIM=1; full 33 3 3; unset SKIPTRIM
# re-run of the universe with the final tr_core.py (must equal st_33.npz)
[ -f st33_recheck.log ] || { mkdir -p /tmp/rck && cp tr_core.py tr_states.py /tmp/rck/ && (cd /tmp/rck && $PY tr_states.py 3 3) > st33_recheck.tmp && $PY -c "
import numpy as np; a=np.load('st_33.npz'); b=np.load('/tmp/rck/st_33.npz')
print('st_33 identical:', all((a[k]==b[k]).all() for k in ['tr','SB','SO','first','cnt']))" >> st33_recheck.tmp && mv st33_recheck.tmp st33_recheck.log; }
# controls on the lemma side (new universe): no NK, no N24
:    33k 3 3 nonk
for T in 33k; do grep -q SAT phi$T.res 2>/dev/null && ! grep -q UNSAT phi$T.res && [ ! -f ctrl_$T.log ] && $PY tr_ctrlcheck.py phi$T $T 0 33 > ctrl_$T.log 2>&1; done
# naive second implementation on samples (50 traces / 50 conflict pairs / 50 non-conflict pairs of the full matrix)
[ -f indep33.done ] || { $PY tr_indep.py 33 50 11 > indep33.log 2>&1 && touch indep33.done; }
# dependency of the certificate clauses (pairs_33tree.npy) on each pair-rule family: 1 A, 2 F1, 4 L, 8 SAME, 16 D1 at (P_k,F),
# 32 single rules at (P_k,F), 64 rules at the (F,F') 5-pair, 128 CLS inside pair rules
for D in 64 32 16 8 128 4 2 1; do
  [ -f cfd_33_${D}_pairs_33tree.done ] || $PY tr_drop.py 33 $D pairsfile=pairs_33tree.npy >> dep33.log 2>&1
done
# bonus classes, same tree certificate (run_treeT.sh TAG)
for T in 34 24x; do
  case $T in 34) A="3 4";; 24x) A="2 4 no24";; esac
  [ -f st_$T.npz ] || $PY tr_states.py $A >> pipeline.log 2>&1
  [ -f cf_$T.done ] || ./run_conf.sh $T
  [ -f pairs_$T.npy ] || $PY -c "
import numpy as np, glob
U=np.load('st_$T.npz'); NT=len(U['tr']); pr=[]; lo=0
f={int(x.split('/')[-1][2:-4].split('_')[0]): x for x in glob.glob('cf_$T/r_*_*.npy') if 'tmp' not in x}
while lo<NT:
    R=np.unpackbits(np.load(f[lo]),axis=1)[:,:NT]; r,c=np.nonzero(R); pr.append(np.stack([r+lo,c],1)); lo+=len(R)
np.save('pairs_$T.npy', np.concatenate(pr))"
  ./run_treeT.sh $T >> pipeline.log 2>&1
done
# lemma-side controls, no proof (SAT expected): no NK (33k), no N24 (33x)
for T in 33k 33x; do
  case $T in 33k) A="3 3 nonk";; 33x) A="3 3 no24";; esac
  [ -f st_$T.npz ] || $PY tr_states.py $A >> pipeline.log 2>&1
  [ -f cf_$T.done ] || ./run_conf.sh $T
  [ -f phi$T.cnf ] || { $PY tr_cnf.py $T phi$T.cnf.tmp >> pipeline.log 2>&1 && mv phi$T.cnf.tmp phi$T.cnf; }
  rm -f phi$T.drat; ./solve_np.sh phi$T 1500
  echo "phi$T (control): $(cat phi$T.res 2>/dev/null) $(tail -1 phi$T.unknown 2>/dev/null) $(date -u)" >> pipeline.log
  grep -qx SAT phi$T.res 2>/dev/null && [ ! -f ctrl_$T.log ] && $PY tr_ctrlcheck.py phi$T $T 0 33 > ctrl_$T.log 2>&1
done
# full (unsplit) Φ_33 certificate last (slow drat-trim; the case-split certificate run_tree.sh is the primary one)
./solve.sh phi33 1100 >> pipeline.log 2>&1
echo "phi33 full: $(grep -h 's [A-Z]' phi33.trim 2>/dev/null) $(date -u)" >> pipeline.log
echo "== pipeline end $(date -u)" >> pipeline.log
touch pipeline.done
