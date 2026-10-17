> **Internal working note.** This file is a raw report written while the proof was being developed and checked. It is kept for provenance. Run names and timings refer to the original working environment. The curated statements are in `paper/` and `README.md`.

> **Paths.** File paths in this report have been rewritten to their location in this repository wherever the file is
> included (`lean/`, `sat/`, `docs/`, `data/`). Paths still beginning with `work/`, `candidates/` or `/tmp/` name exploratory
> scripts, build directories or logs from the original working environment that are not part of the proof and were not
> published; nothing the final theorem or the certificate checks depends on is among them.

# Lean formalization: Erdős #616 at r = 21 — statement, reduction, §1 lemmas, lower bound

Plan / dependency DAG / estimate: docs/lean-reports/plan.md.

## Status (milestone 2, 2026-10-16 ~17:15 EDT): **Full.lean checks, 0 sorry, 0 errors** (milestone 1 at ~17:05 had everything except the last three rows)
Check: `lean Full.lean` (+ `#print axioms` block) → `exit 0` in 4 s; every listed theorem depends only on
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`). Negative control: appending `example : (1:ℕ) = 2 := rfl` → `exit 1`
("Type mismatch"), so the file is really elaborated. Warnings only (style: deprecated `push Not` alternatives, `<;>` lint,
unused section variables).

| item (hand proof: docs/proof-notes.md §1, §6.0, §7.3; loop.md §3) | Lean name | status |
|---|---|---|
| formal-conjectures defs copied verbatim (`Set.HasFiniteTransversal`, `Finset.IsUniform`, `Finset.hypergraphInduce`, `Hypergraph.localTransversalBound`) | — | ✅ |
| r = 21 statement `localTransversalBound 21 60 1 = 4` | `Statement` | stated |
| local hypothesis (a = 1) ⟺ property L (subfamily with union ≤ v has common vertex) | `local_iff_propL` | ✅ |
| L ⟺ "empty-intersection subfamilies span > v"; suffices for **minimal** empty-intersection families | `propL_iff_span`, `propL_of_minimal` | ✅ |
| UB reduction: no counterexample ⇒ `≤ 4`; τ ≥ 5 ⟺ every ≤4-set avoided | `le_four_of_noCounter`, `counter_of_not_transversal` | ✅ |
| **LB: EHT example H(21,10,7)** (10-point core, edges = 7-subsets + 14 private points), transported to `Fin n`: `4 ≤ t(21)` | `HL_uniform`, `HL_propL`, `HL_not_transversal3`, `four_le` | ✅ |
| **Statement ⟺ no counterexample** (both directions; uses `3*21-3` literally) | `erdos_616_r21_iff` | ✅ |
| F1 (2- and 3-wise intersecting) | `inter2`, `inter3` | ✅ |
| L1 / Lemma A(i): \|E∩E'\| ≥ 5 | `inter_ge5` | ✅ |
| Lemma A(ii): some pair meets in exactly 5 (EHT cover argument, m = 6..17 table) | `exists_cover4`, `arithA`, `lemmaA` | ✅ |
| Lemma R.1 / R.2 / R.3, Cor R1 | `R1`, `R2`, `R3`, `single_card` | ✅ |
| Lemma S(a) (A-, C-, O-parts), S(b), S(c) both sides | `S_a_A`, `S_a_C`, `S_a_O`, `S_b`, `S_c`, `S_c'` | ✅ |
| Lemma K (both lines) | `K_A`, `K_C`, `K_meets`, `K_bound` | ✅ |
| Lemma T (existence + all properties of witnesses) | `T_exists`, `T_props` | ✅ |
| D1 | `D1` | ✅ |
| W7-5 = CP' (49-triple inequality) | `CP` | ✅ |
| cross-type classes: 1 ≤ α, γ ≤ 4, α+γ ≥ 5, \|G∩G'\| = α+γ (input to N.0 / N8.0 / n4-referee step 3) | `cross_class` | ✅ |
| N.0: {E1,E2,G,G'} spans exactly 61 for every class | `K4_span` | ✅ |
| rigid base configuration (5-pair + singles of every type, 5/5/12, disjoint outsides) | `rigid_base` | ✅ |

So: **t(21) = 4 is now formally equivalent (in Lean, against the formal-conjectures definition) to `∀ n H, ¬ Counter H`**, and
the lower bound half is done. What remains is exactly the upper-bound case analysis: W6-U, W7-I, the N-split, and the
three computer-assisted leaves (G14, w10x, w11) with their encoding-soundness bridges (see plan §1.3, §3).

Formal statement of the counterexample predicate (what the remaining work must refute):
```lean
structure Counter (H : Finset (Finset V)) : Prop where
  unif : ∀ e ∈ H, e.card = 21
  propL : PropL H 60          -- ∀ F ⊆ H, F.Nonempty → (F.biUnion id).card ≤ 60 → ∃ x, ∀ e ∈ F, x ∈ e
  avoid : ∀ B : Finset V, B.card ≤ 4 → ∃ e ∈ H, Disjoint e B
```
Conventions in the lemmas: a 5-pair is `a b ∈ H` with `(a ∩ b).card = 5`, `M = a ∩ b`; a single of type `x` is `F` with
`F ∩ (a ∩ b) = {x}`; A-part `F ∩ (a \ b)`, C-part `F ∩ (b \ a)`, outside part `F \ (a ∪ b)`.

## Check log (milestone 2; Check.lean = Full.lean + 28 `#print axioms` lines)
```
exit 0 time 4s
errors: 0; sorryAx occurrences: 0
'Erdos616R21.erdos_616_r21_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.four_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.local_iff_propL' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.propL_of_minimal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.inter3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.inter_ge5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.lemmaA' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.R1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.R2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.R3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.single_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.D1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.S_a_A' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.S_a_C' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.S_a_O' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.S_b' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.S_c' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.S_c'' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.K_A' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.K_C' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.K_meets' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.K_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.T_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.T_props' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.CP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.cross_class' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.K4_span' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.rigid_base' depends on axioms: [propext, Classical.choice, Quot.sound]
warning summary (style only): {'Unused tactic linter: `<;>` should be replaced with `;` or b': 14, 'Unused tactic linter: `tauto` does nothing.': 5, 'this tactic is never executed': 5, 'Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice': 9, 'Variable name `hb` is not explicitly referenced.': 1, 'automatically included section variable(s) unused in theorem': 1}
negative control (milestone 1; Full.lean + `example : (1:ℕ) = 2 := rfl`): exit 1, "error: Type mismatch"
```

## Environment
Lean 4.35.0 (/tmp/lean-tc), Mathlib rev 56a00585 oleans copied from lean/erdos/.lake (targeted closure of the imports below,
1633 modules incl. `.ir.sig`; ImportGraph copied whole). Rebuild: `work/e616lean/setup.sh` (fast path: tarball
work/e616lean/E616lib.tar; module list work/e616lean/mods.txt). Compile in /tmp/w with `bg.sh FILE` (background; `FILE.done`).
Note: the old work/leanre/setup.sh omits `.ir.sig` files, which Lean 4.35 needs (error "unknown declaration ...initFn").

```bash
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
```
```bash
#!/bin/bash
# bg.sh FILE : compile in background, output FILE.out, marker FILE.done
cd /tmp/w; f=$1; rm -f $f.done
export LEAN_PATH=/tmp/E/lib:/tmp/lean-tc/lib/lean
( S=$(date +%s); /tmp/lean-tc/bin/lean $f > $f.out 2>&1; echo "exit $? time $(( $(date +%s) - S ))s" > $f.done ) 
```

## Full source: lean/Erdos616/Basic.lean (1202 lines)
*[1202-line Lean listing omitted here: it duplicates a source file now under `lean/` (see `docs/path-map.md`).]*
