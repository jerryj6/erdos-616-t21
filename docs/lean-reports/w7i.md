> **Internal working note.** This file is a raw report written while the proof was being developed and checked. It is kept for provenance. Run names and timings refer to the original working environment. The curated statements are in `paper/` and `README.md`.

> **Paths.** File paths in this report have been rewritten to their location in this repository wherever the file is
> included (`lean/`, `sat/`, `docs/`, `data/`). Paths still beginning with `work/`, `candidates/` or `/tmp/` name exploratory
> scripts, build directories or logs from the original working environment that are not part of the proof and were not
> published; nothing the final theorem or the certificate checks depends on is among them.

# Lean formalization, part W7-I: Theorem W7-I (triangle case impossible), Erdős #616, r = 21

Status (milestone 1 at 17:58 EDT; logs re-run after a sandbox reset, 18:25 EDT = 22:25 UTC): **DONE. lean/Erdos616/W7I.lean checks: 0 errors, 0 sorry.**
Every theorem depends only on `propext, Classical.choice, Quot.sound`. The negative control fails as it should.
**No SAT/DRAT certificate is used.** The finite step of upper.md §7.3 is replaced by the hand Steps 0–4 of §7.4
(the refereed hand proof), so no encoding bridge to w7_core_A_c3 / ref_w7_min is needed.

## Main results
* `Erdos616R21.W7I.W7I_leaf` is **exactly the body of HandA.lean's `def W7I_leaf : Prop`**, with `W7I_prop` and `CrossPair`
  unfolded verbatim:
  `∀ n (H : Finset (Finset (Fin n))), Counter H → ∀ X Y G G', (X ∈ H ∧ Y ∈ H ∧ G ∈ H ∧ G' ∈ H ∧ (X ∩ Y).card = 5 ∧
   ∃ v w, v ≠ w ∧ G ∩ (X ∩ Y) = {v} ∧ G' ∩ (X ∩ Y) = {w}) → (G ∩ G' ∩ (X \ Y)).card ≠ 1 ∧ (G ∩ G' ∩ (Y \ X)).card ≠ 1`.
  It lives in the sub-namespace `W7I` so that it does not clash with HandA's `def Erdos616R21.W7I_leaf`.
  **Glue checked:** a file importing both HandA (md5 4d9a8976…, the version at 21:56 UTC) and W7I proves
  `theorem W7I_leaf_holds : Erdos616R21.W7I_leaf := Erdos616R21.W7I.W7I_leaf` (exit 0; axioms standard; log below).
* `Erdos616R21.W7I_cross` is the same statement for any type `V` with `[DecidableEq V]`, stated in the `cross_class` style of Full.lean.
* `Erdos616R21.tri_false`: no `Tri H Q A B K xab xak xbk` exists when `Counter H` holds (the triangle form of W7-I).

## Lemma map (hand proof → Lean)
| upper.md | Lean (W7I.lean) | uses from Full.lean |
|---|---|---|
| Tri-0 (structure of the triangle) | `structure Tri`, `mkTri` (5-pair + cross pair with a=1 ⇒ Tri), `Tri.swapAB/swapBK` (S3 symmetry), `Tri.L_AB`, `sub_C`, `decompA`, `Qs_card` | `single_card`, `S_c`, `cross_class` |
| Tri-2 (Y-edges) | `Y_sub` (Y∩Q ⊆ A∪B, by R.3), `Y_xak`/`Y_xbk` (by CP' at (Q,A,K)), `Y_xab`, `Y_three` (≥3 points in Q_a∪Q_b), `Y_notQK` | `R3`, `CP`, `inter_ge5` |
| W7-2 (W-edges) | `W_card`, `W_e3` (\|W∩C0\| ≥ 3 via S(b) twice), `W_split` (\|W∩C0\|+\|W∩O_a\| = 4), `W_rhs`, `W_cstar` (the point c*(q)) | `single_card`, `S_b` |
| CP' (W7-5) instance | `hit` | `CP` |
| Step 0 (incl. (A)) | `U_sub_W` (U_k ⊆ every W^k_q), `U_le4`, `U_ge3`, `tight_trace` | `CP`, `R2`, `R3` |
| Step 1 | `step1` | – |
| Step 2 | `step2` | – |
| Step 3 | `step3_core`, `U_split`, `step3` (every \|U_k\| = 3) | – |
| Step 4 | `star` (★, stated as a disjunction), `tri_false` (six orderings + `omega`) | – |
| c = 1 version (E1↔E2 swap, referee §4) | `W7I_cross`, second conjunct | – |

Design choice (a simplification, faithful to the proof): `U H Q A B K` is the union of the traces on Q_a∪Q_b of **all**
(A,B)-singles of a type in C0, not of one chosen Y per type. Step 0 is proved for every such Y. In Step 0's e = 3 case the
competing single Y' of type m is produced by R.2 inside the proof. So there are no choice functions, and the referee's
remark "the Y's are a fixed choice" is not needed.

## Build (reproducible; each run ≤ 10 s, max RSS of lean ≈ 1.9 GB, mostly mmapped oleans; script work/e616lean/w7i_build/run.sh)
```
# env: /tmp/E (Mathlib closure from work/e616lean/E616lib.tar) + /tmp/lean-tc (toolchain copy), via work/e616lean/setup.sh.
# NOTE: in a fresh sandbox, work/leanre/setup.sh does not copy the core *.ir.sig files or lib/lean/Lake. Without them
# /tmp/lean-tc fails with "(interpreter) unknown declaration ...spec_0" / "unknown module prefix 'Lake'". Fix used here:
#   cd $TC/lib/lean && find . -name '*.ir.sig' -print0 | xargs -0 cp -n --parents -t /tmp/lean-tc/lib/lean/
#   cp -rn $TC/lib/lean/Lake* /tmp/lean-tc/lib/lean/        (TC=/workspace/.elan/toolchains/leanprover--lean4---v4.35.0)
mkdir -p /tmp/w7 && cd /tmp/w7
cp lean/Erdos616/Basic.lean E616Full.lean; cp lean/Erdos616/W7I.lean .
export LEAN_PATH=/tmp/E/lib:/tmp/lean-tc/lib/lean:/tmp/w7
nice /tmp/lean-tc/bin/lean -o E616Full.olean E616Full.lean     # exit 0, 6 s
nice /tmp/lean-tc/bin/lean -o W7I.olean W7I.lean               # exit 0, 5-6 s
```
For integration: W7I.lean starts with `import E616Full` (an unchanged copy of Full.lean, md5 61699761…); the body is a
self-contained `namespace Erdos616R21` block with no name clashes against Full.lean or HandA.lean (checked by the glue file).
## Logs (rerun by work/e616lean/w7i_build/run.sh; raw files in that directory)
### summary.txt (exit code, wall time, max RSS of the lean child)
```
E616Full: exit 0 time 5s maxRSS_kB 1942548
W7I: exit 0 time 3s maxRSS_kB 1913940
W7ICheck: exit 0 time 3s maxRSS_kB 1901968
W7INeg: exit 1 time 2s maxRSS_kB 1896924
HandA: exit 0 time 10s maxRSS_kB 1957976
Glue: exit 0 time 1s maxRSS_kB 1811820
```
### md5 of the checked copies
```
61699761fc9839d65c9dbd6cc8c5549e  E616Full.lean
ae6006677a52acee141869e292f272e4  W7I.lean
4d9a8976cacf9d48262a09f91a6bd9c9  HandA.lean
```
### W7I.lean output (errors: 0; warnings, all linter / unused-variable / unused section-variable):
```
W7I.lean:24:0: warning: automatically included section variable(s) unused in theorem `Erdos616R21.eq_of_mem_singleton'`:
W7I.lean:27:0: warning: automatically included section variable(s) unused in theorem `Erdos616R21.mem_of_eq_singleton'`:
W7I.lean:66:62: warning: Variable name `z` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
W7I.lean:85:49: warning: Variable name `z` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
W7I.lean:225:0: warning: automatically included section variable(s) unused in theorem `Erdos616R21.Y_C`:
W7I.lean:225:13: warning: Variable name `T` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
W7I.lean:231:0: warning: automatically included section variable(s) unused in theorem `Erdos616R21.Y_xab`:
W7I.lean:333:0: warning: automatically included section variable(s) unused in theorem `Erdos616R21.W_QAW`:
W7I.lean:403:0: warning: automatically included section variable(s) unused in theorem `Erdos616R21.W_rhs`:
W7I.lean:734:0: warning: automatically included section variable(s) unused in theorem `Erdos616R21.U_split`:
W7I.lean:734:17: warning: Variable name `T` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
```
### W7ICheck.lean = W7I.lean + `#print axioms` lines
```
'Erdos616R21.W7I.W7I_leaf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.W7I_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.tri_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.mkTri' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.U_sub_W' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.U_le4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.U_ge3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.step1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.step2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.step3_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.step3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.star' depends on axioms: [propext, Classical.choice, Quot.sound]
```
### Negative control W7INeg.lean = W7I.lean + `example : (1:ℕ) = 2 := rfl` (must fail)
```
: Type mismatch
  rfl
has type
  ?m.7 = ?m.7
```
### Glue with HandA (HandA.lean compiled locally against the same E616Full)
```lean
import HandA
import W7I
/-- HandA's leaf hypothesis `W7I_leaf` is discharged by W7I.lean. -/
theorem W7I_leaf_holds : Erdos616R21.W7I_leaf := Erdos616R21.W7I.W7I_leaf
#print axioms W7I_leaf_holds
```
```
HandA errors: 0
'W7I_leaf_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Full source: lean/Erdos616/W7I.lean (944 lines, md5 ae6006677a52acee141869e292f272e4)
*[944-line Lean listing omitted here: it duplicates a source file now under `lean/` (see `docs/path-map.md`).]*
