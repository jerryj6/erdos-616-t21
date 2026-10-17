> **Internal working note.** This file is a raw report written while the proof was being developed and checked. It is kept for provenance. Run names and timings refer to the original working environment. The curated statements are in `paper/` and `README.md`.

# Lean bridge for the N-K4 leaf (G14) of t(21) = 4 (Erdős #616)

**STATUS (2026-10-16 ≈19:25 EDT): DONE.** `Erdos616R21.NK4_leaf_proved : NK4_leaf` (HandA's statement) compiles in
lean/Erdos616/G14/Leaf.lean with 0 sorry and no hypotheses; axioms = standard three + native_decide aux axioms of the G14
checkers and the LRAT checkers (see Milestone 7).

Started 2026-10-16 ~17:10 EDT. Files: lean/Erdos616/G14/ (G14Check.lean = core-only checkers + glue; T.txt = var→trace table),
lean/Erdos616/G14/Bridge.lean (Mathlib side, to come). Status lines are appended per milestone below.

## Design (milestone 0, 17:20 EDT)
Split into two layers so the heavy computation runs in core Lean (no Mathlib, natively compiled) and the hand proofs live on the
Mathlib side:
1. **G14Check.lean (core only).** 16-bit masks over the 16 core points (bit order of the G14 CNFs: v,w,al0,al1,g0,g1,g2,m0,m1,m2,
   a3_0,a3_1,a4_0,a4_1,c3,c4). `ok b o` = per-edge rules (literal port of the referee's ref_states.ok), `states b` = o-box filtered by
   `ok`, `rulesAt`/`feasible` = pairwise rules (literal port of pairref.feasible; z_U eliminated by its least admissible value
   `5 - |I| - Σz`, sound because every rule other than Lemma A is an upper bound on z_U), `compatTr t t'`. `T` = DIMACS var-1 → trace
   (w14_conf.npz['T'], 18 217 sorted distinct masks; spot check: unit var 15117 of the 15116 case ↦ T[15116] = 50060 =
   {al0,al1,m0,m1,m2,c3,c4}). `checkCNF f extra`: every clause is (CONF) `[-u,-v]` with `T[u] ≠ T[v]` and `compatTr` false, or
   (COV) a positive clause equal to the full avoider list of a needed core 4-set B, or the designated extra clause (unit x_r / the
   51-literal dead-avoider clause). `univOK`: every 16-bit trace with an admissible state is in `T`.
2. **Glue theorem (core only, planned in the same file):** abstract `Model` = predicate `occ` on traces with (lt) traces < 2^16,
   (univ) occurring traces have a state, (cov) every needed B has an occurring avoider, (conf) distinct occurring traces are
   `compatTr`. Then `checkCNF f extra ∧ univOK ∧ extra satisfied ⇒ f.eval (assign M) = true`, `assign M v := occ T[v]`.
3. **Mathlib side (BridgeG14.lean):** from `Counter H` + a labelled (3,2,1,1) K4 base (core injection `c : Fin 16 → V` with the
   membership table `Pm`, O_q = P_q \ core) build the Model (`occ t := ∃ F ∈ H non-base, tr F = t`): cov from τ ≥ 5; univ from the
   per-edge lemmas; conf from the pairwise lemmas (Lemma A, F1, L, D1, S(a), S(b), W7-I). Root split on B* = {w,g0,g1,g2} and the
   288-group by **relabelling the core** (c ∘ g is again a labelled base), so no invariance of any computed object is needed.

## Milestone 1 (≈17:55 EDT): checkers run natively on all certificate CNFs; glue + root split proved (0 sorry)
**Computation (native, compiled with leanc; bench = lean/dev/g14/Bench.lean, logs bench*.log there).**
* `T.map states`: 18 217 traces, **49 967 states in total — exactly the authors' and the referee's count** (21 s native).
* `univOK ()` = **true** (every 16-bit trace with an admissible state is in T; 50 s native).
* `clauseOK` over every clause of: w14_cert2_15116 (668 659 cl., 4.4 s), w14_cert2_14968 (1 024 649 cl., 10.7 s),
  w14_cert2_17917 (759 549 cl., 6.0 s), w14_certdead (594 808 cl., 3.9 s): **every clause accepted except exactly one per file,
  which is the designated extra clause** (unit `[x_r]` for the case files; the 51-literal dead-avoider clause for certdead).
  So all CONF clauses are conflicts under the Lean `compatTr` and all COV clauses are exact avoider lists of needed 4-sets.
  15954 and 16054 (3.9 M / 4.2 M clauses) running.
* So the "37 M pairs" risk is gone: only the ≈11 M binary clauses that occur in the 6 CNFs are checked, at ≈0.2 M clauses/s,
  with the per-trace state lists computed once (z_U eliminated in closed form; z_0..z_3 enumerated).
* native_decide uses the compiled code: `lean --load-dynlib=libG14Check.so` (built by `leanc -c -DLEAN_EXPORTING` +
  `leanc -shared … -lleanshared`); test: states of 3000 traces by native_decide in 3.5 s; negative control `pc (Pm 0) = 12`
  by native_decide fails ("is false"). Heavy values are function arguments, not closed terms (closed terms are evaluated at
  module initialisation, which made the first attempt hang).

**Proved in Lean (core only, `#print axioms` = [propext, Classical.choice, Quot.sound]):**
* `G14.eval_of_check` (G14Glue.lean): for every abstract trace model `M` (fields `lt`, `univ`, `cov`, `conf`),
  `univOK () = true → checkCNF f extra = true → extra satisfied → f.eval (assign M) = true`.
* `G14.root_split` (G14Root.lean): from `univOK () = true`, `rootOK = true` (B* = {w,g0,g1,g2} = mask 114; 70 avoiders in T =
  51 dead atoms ⊔ 19 alive, each with an explicit relabelling `s` (permutations inside m3 and a4 only) mapping it onto one of
  the 5 representatives, `validPerm s` = permutation of 0..15 preserving every `Pm q`), the five case refutations
  `∀ M, M.occ T[r]! → False` and the dead refutation, and a family of models `M s` (model of the base relabelled by `s`) with
  `hpull : validPerm s → (M s0).occ t → (M s).occ (pull s t)`, derive False.
Left for the next milestones: native_decide theorems `univOK () = true`, `rootOK = true`, `checkCNF (parse cnfText_k) extra_k = true`
(importing the LRAT cert modules) ⇒ the five case lemmas + dead lemma; then the Mathlib side (Model from Counter + labelled base).
### lean/Erdos616Checkers/G14Check.lean
*[204-line listing omitted: the source is the file named in the heading.]*
### lean/Erdos616/G14/Glue.lean
```lean
import G14Check
/-!
# G14 glue (core Lean only): an abstract trace model satisfies every CNF accepted by `checkCNF`.
-/
open Std.Sat

namespace G14

/-- Abstract trace model: `occ t` = "some non-base edge has core trace `t`". The four fields are exactly what the
Mathlib side must prove from a counterexample (`lt`: traces are 16-bit masks; `univ`: per-edge rules give an
admissible state; `cov`: τ ≥ 5 on needed core 4-sets; `conf`: pairwise rules). -/
structure Model where
  occ : Nat → Prop
  lt : ∀ t, occ t → t < 65536
  univ : ∀ t, occ t → (states t).isEmpty = false
  cov : ∀ B, neededB B = true → ∃ t, occ t ∧ t &&& B = 0
  conf : ∀ t t', occ t → occ t' → t ≠ t' → compatTr t t' = true

open Classical in
/-- the induced assignment: atom `v` (DIMACS variable `v+1`) is true iff trace `T[v]` occurs -/
noncomputable def assign (M : Model) (v : Nat) : Bool := decide (M.occ T[v]!)

theorem assign_true {M : Model} {v : Nat} : assign M v = true ↔ M.occ T[v]! := by
  unfold assign; simp

theorem idx_of_occ (M : Model) (hu : univOK () = true) {t : Nat} (ht : M.occ t) :
    ∃ v, v < T.size ∧ T[v]! = t := by
  unfold univOK at hu
  have h := List.all_eq_true.1 hu t (List.mem_range.2 (M.lt t ht))
  rw [M.univ t ht, Bool.false_or] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨_, h.1, h.2⟩

theorem stArr_get {u : Nat} (hu : u < T.size) : (T.map states)[u]! = states T[u]! := by
  have hu' : u < (T.map states).size := by simpa using hu
  rw [getElem!_pos (T.map states) u hu', getElem!_pos T u hu, Array.getElem_map]

theorem compatV_eq {u v : Nat} (hu : u < T.size) (hv : v < T.size) :
    compatV (T.map states) u v = compatTr T[u]! T[v]! := by
  unfold compatV compatTr
  rw [stArr_get hu, stArr_get hv]

theorem covOK_sound (M : Model) (hu : univOK () = true) (lits : List (Nat × Bool))
    (h : covOK lits = true) : lits.any (fun (i, n) => assign M i == n) = true := by
  unfold covOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hpos, h⟩ := h
  split at h
  · rename_i B _
    rw [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hB, heq⟩ := h
    obtain ⟨t, ht, htB⟩ := M.cov B hB
    obtain ⟨v, hv, hTv⟩ := idx_of_occ M hu ht
    have hmem : v ∈ avoiders B := by
      unfold avoiders
      rw [List.mem_filter, List.mem_range, hTv, htB]
      exact ⟨hv, rfl⟩
    rw [← heq, List.mem_map] at hmem
    obtain ⟨⟨i, n⟩, hl, hl1⟩ := hmem
    have hl2 : n = true := List.all_eq_true.1 hpos _ hl
    simp only at hl1
    subst hl1 hl2
    refine List.any_eq_true.2 ⟨(i, true), hl, ?_⟩
    simp only [beq_iff_eq]
    rw [assign_true, hTv]; exact ht
  · exact absurd h (by simp)

theorem clauseOK_sound (M : Model) (hu : univOK () = true) (extra lits : List (Nat × Bool))
    (he : extra.any (fun (i, n) => assign M i == n) = true)
    (h : clauseOK (T.map states) extra lits = true) : lits.any (fun (i, n) => assign M i == n) = true := by
  unfold clauseOK at h
  split at h
  · rename_i u v
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨hu', hv'⟩, hne⟩, hc⟩ := h
    rw [compatV_eq hu' hv'] at hc
    cases h1 : assign M u
    · simp [h1]
    cases h2 : assign M v
    · simp [h2]
    have := M.conf _ _ (assign_true.1 h1) (assign_true.1 h2) hne
    rw [hc] at this
    exact absurd this (by simp)
  · rw [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · subst h; exact he
    · exact covOK_sound M hu lits h

/-- **Glue theorem.** A trace model satisfies every CNF accepted by `checkCNF` (given the extra clause holds). -/
theorem eval_of_check (M : Model) (hu : univOK () = true) (f : CNF Nat) (extra : List (Nat × Bool))
    (hc : checkCNF f extra = true) (he : extra.any (fun (i, n) => assign M i == n) = true) :
    f.eval (assign M) = true := by
  unfold checkCNF checkCNFWith at hc
  unfold CNF.eval
  rw [Array.all_eq_true] at hc ⊢
  intro i hi
  exact clauseOK_sound M hu extra _ he (hc i hi)

end G14
```
### lean/Erdos616/G14/Root.lean
```lean
import G14Glue
/-!
# G14 root split (core Lean only): B* = {w,g0,g1,g2}; its 70 avoiders in `T` are the 51 "dead" ones (refuted by
w14_certdead) and 19 alive ones, each mapped by a base automorphism `s` (a permutation of the 16 core labels preserving
every `P_q`, here inside m3 and a4 only) onto one of the 5 representatives.
-/
open Std.Sat
namespace G14

def Bstar : Nat := 114
def deadAtoms : List Nat := [10077, 10179, 10236, 10291, 11638, 11693, 11748, 11796, 11851, 11899, 11945, 12952, 13007, 13062, 13110, 13165, 13213, 13259, 14278, 14329, 14378, 14400, 14449, 14469, 16050, 16052, 16135, 16137, 16171, 16173, 16988, 16990, 17073, 17075, 17109, 17111, 17837, 17839, 17841, 17876, 17878, 17880, 17915, 17916, 17927, 17929, 17931, 17966, 17967, 17978, 17979]
def deadClause : List (Nat × Bool) := deadAtoms.map fun a => (a, true)
def reps : List Nat := [14968, 15116, 15954, 16054, 17917]
/-- (atom of an alive avoider, atom of its representative, relabelling `s` with `s[i]` = old label of new label `i`) -/
def rootData : List (Nat × Nat × List Nat) := [(14968, 14968, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
  (15042, 14968, [0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 10, 11, 12, 13, 14, 15]),
  (15080, 14968, [0, 1, 2, 3, 4, 5, 6, 8, 9, 7, 10, 11, 12, 13, 14, 15]),
  (15116, 15116, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
  (15954, 15954, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
  (16003, 15954, [0, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 11, 12, 13, 14, 15]),
  (16054, 16054, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
  (16088, 15954, [0, 1, 2, 3, 4, 5, 6, 9, 7, 8, 10, 11, 12, 13, 14, 15]),
  (16139, 16054, [0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 10, 11, 12, 13, 14, 15]),
  (16175, 16054, [0, 1, 2, 3, 4, 5, 6, 8, 9, 7, 10, 11, 12, 13, 14, 15]),
  (16892, 15954, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 12, 14, 15]),
  (16941, 15954, [0, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 11, 13, 12, 14, 15]),
  (16992, 16054, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 12, 14, 15]),
  (17026, 15954, [0, 1, 2, 3, 4, 5, 6, 9, 7, 8, 10, 11, 13, 12, 14, 15]),
  (17077, 16054, [0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 10, 11, 13, 12, 14, 15]),
  (17113, 16054, [0, 1, 2, 3, 4, 5, 6, 8, 9, 7, 10, 11, 13, 12, 14, 15]),
  (17917, 17917, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
  (17968, 17917, [0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 10, 11, 12, 13, 14, 15]),
  (17980, 17917, [0, 1, 2, 3, 4, 5, 6, 8, 9, 7, 10, 11, 12, 13, 14, 15])]

/-- relabelled trace: new bit `i` = old bit `s[i]` -/
def pull (s : List Nat) (t : Nat) : Nat :=
  (List.range 16).foldl (fun acc i => if t.testBit s[i]! then acc ||| 2 ^ i else acc) 0

/-- `s` is a permutation of `0..15` preserving every base edge -/
def validPerm (s : List Nat) : Bool :=
  s.length == 16 && s.all (· < 16) && s.Nodup &&
  Q4.all fun q => (List.range 16).all fun i => (Pm q).testBit s[i]! == (Pm q).testBit i

def rootOK : Bool :=
  neededB Bstar && rootData.all (fun e => validPerm e.2.2 && reps.contains e.2.1 && decide (e.2.1 < T.size)) &&
  (List.range T.size).all fun a => T[a]! &&& Bstar != 0 || deadAtoms.contains a ||
    rootData.any fun e => e.1 == a && pull e.2.2 T[a]! == T[e.2.1]!

/-- **Root split.** Given refutations of the five representative cases and of the dead-avoider clause (each a
model-level statement, discharged by the LRAT-checked CNFs), no family of trace models that is closed under
relabelling by valid permutations can exist. `M s` is the model of the base relabelled by `s`; `hpull` says a trace
occurring for the reference labelling `s0` occurs, relabelled, for every valid `s`. -/
theorem root_split (hu : univOK () = true) (hr : rootOK = true)
    (caseR : ∀ r ∈ reps, ∀ M : Model, M.occ T[r]! → False)
    (caseDead : ∀ M : Model, (deadClause.any fun (i, n) => assign M i == n) = true → False)
    (M : List Nat → Model) (s0 : List Nat)
    (hpull : ∀ s, validPerm s = true → ∀ t, (M s0).occ t → (M s).occ (pull s t)) : False := by
  unfold rootOK at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨hB, hdata⟩, hall⟩ := hr
  obtain ⟨t, ht, htB⟩ := (M s0).cov Bstar hB
  obtain ⟨v, hv, hTv⟩ := idx_of_occ (M s0) hu ht
  have h := List.all_eq_true.1 hall v (List.mem_range.2 hv)
  rw [hTv, htB] at h
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact absurd h (by decide)
  · apply caseDead (M s0)
    refine List.any_eq_true.2 ⟨(v, true), ?_, ?_⟩
    · unfold deadClause
      exact List.mem_map.2 ⟨v, List.elem_iff.1 h, rfl⟩
    · simp only [beq_iff_eq]
      rw [assign_true, hTv]; exact ht
  · obtain ⟨e, he, h1⟩ := List.any_eq_true.1 h
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨-, h2⟩ := h1
    have hd := List.all_eq_true.1 hdata e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
    obtain ⟨⟨hval, hrep⟩, -⟩ := hd
    have := hpull e.2.2 hval t ht
    rw [h2] at this
    exact caseR e.2.1 (List.elem_iff.1 hrep) (M e.2.2) this

end G14
```

## Milestone 2 (≈18:10 EDT): native_decide checks pass in Lean; 4 of 6 certificate pieces linked to the model
Run: `lean --load-dynlib=/tmp/g14/libG14.so` (libG14.so = compiled G14Check + LratCheck), LEAN_PATH = /tmp/g14 : copy of
sat/lrat/ (LratCheck.olean, certs/*.olean) : toolchain. Logs: lean/dev/g14/logs/ (runcases.log, *.out).
```
G14Univ exit 0 time 78s        -- theorem univ_ok : univOK () = true ; theorem root_ok : rootOK = true  (native_decide)
G14Case15116 exit 0 time 29s   -- chk15116 : checkCNF (parseDimacs E616.w14_15116.cnfText) [(15116,true)] = true
G14Case17917 exit 0 time 30s
G14CaseDead exit 0 time 34s    -- chkDead : checkCNF (parseDimacs E616.w14_certdead.cnfText) deadClause = true
'G14.case15116' depends on axioms: [propext, Classical.choice, Quot.sound,
   G14.chk15116._native.native_decide.ax_1_1, E616.w14_15116.certOk_eq._native.native_decide.ax_1_1]
'G14.caseDead' depends on axioms: [propext, Classical.choice, Quot.sound,
   G14.chkDead._native.native_decide.ax_1_1, E616.w14_certdead.certOk_eq._native.native_decide.ax_1_1]
'G14.univ_ok' / 'G14.root_ok': [propext, Classical.choice, Quot.sound, <own native_decide aux axiom>]
```
`G14.case15116 (hu : univOK () = true) (M : Model) (h : M.occ T[15116]!) : False` (likewise 17917; 14968 running), and
`G14.caseDead (hu) (M) (h : deadClause satisfied by assign M) : False` — each = `E616.w14_*.not_exists_sat` applied to
`⟨assign M, eval_of_check M hu _ _ chk_r …⟩`. The CNF in the statement is literally the LRAT agent's `parseDimacs cnfText`
of the same module, so no file identity has to be trusted.
Native bench (not yet as Lean theorems): w14_cert2_15954 (3 896 902 clauses, 82 s) and w14_cert2_16054 (4 181 029 clauses,
103 s): every clause accepted except the unit `[x_r]`. These two are LRAT-checked in chunk mode with the parser
`LratChunk.parseDimacsFast`; their Lean case lemmas will import only the `w14_*_Data` module (84 MB) and take the
`not_exists_sat` of the `_Final` module (1 GB of block oleans) as a hypothesis, to stay under the memory budget.
Mathlib side (lean/Erdos616/G14/Bridge.lean, compiles, 0 sorry so far): bit-mask lemmas (`maskOf`, `testBit_maskOf`,
`pc_eq_card`), `LBase` (labelled base: `P : Fin 4 → Finset V`, injective `c : Fin 16 → V`, membership table, pairwise
intersections inside the core), `tr`, `testBit_tr`, `card_core` (|S ∩ core| = pc m for any mask m describing S on the
core), `card_part` (|S| = |S∩core| + Σ_q |S∩O_q| + |S \ ⋃P|).

## Milestone 3 (≈18:45 EDT): all six certificate pieces are Lean theorems
`runcases.log` (lean/dev/g14/logs/): G14Univ 49s, G14Case15116 25s, G14Case17917 26s, G14CaseDead 26s, G14Case14968 30s,
G14Case16054 85s, G14Case15954 80s — **all exit 0**. Axioms:
```
'G14.univ_ok' / 'G14.root_ok': [propext, Classical.choice, Quot.sound, <own native_decide aux>]
'G14.case15116' / case17917 / case14968 / caseDead: [propext, Classical.choice, Quot.sound, G14.chk*._native…,
                                                    E616.w14_*.certOk_eq._native…]   (UNSAT proved inside)
'G14.case15954_of' / 'G14.case16054_of': [propext, Classical.choice, Quot.sound, G14.chk*._native…]
```
`case15954_of`/`case16054_of` take `hns : ¬ ∃ a, (LratChunk.parseDimacsFast E616C.w14_*.cnfText).eval a = true` as a hypothesis —
this is literally the statement of `E616C.w14_*.not_exists_sat` in the chunked `w14_*_Final` modules (≈1 GB of block oleans),
which are not imported here for memory reasons. Discharging it = one `import w14_*_Final` + `exact E616C.w14_*.not_exists_sat`
in a final assembly file (to be done when memory allows). Sources: G14Case15954.lean / G14Case16054.lean as in lean/Erdos616/G14/.

## Milestone 4 (≈19:05 EDT): Mathlib side compiles — EdgeSound and PairSound proved, 0 sorry
Build env (fresh sandbox): `bash lean/dev/g14/setup_all.sh` (toolchain copy incl. .ir.sig + Lake, /tmp/E from E616lib.tar,
core modules via build.sh, Mathlib-side dir /tmp/g14m with runm.sh). BridgeG14 now imports `E616Full` (same source as Full.lean).
Compiled oleans saved to `olean/` (build output, not included).
```
BridgeG14      exit 0 time 8s   (Parts A–E; L3_edge placeholder gone; fixes: `\\` precedence, Nat.pow_le_pow_right (n := 2),
                                 validPerm_spec, relabel_st, card_inter_UX, UX_O, card_O, card_filter_add_card_filter_not, …)
BridgeG14Pair  exit 0 time 7s
'Erdos616R21.LBase.pairSound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.LBase.edgeSound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.NK4_leaf_of' depends on axioms: [propext, Classical.choice, Quot.sound]
@Erdos616R21.LBase.pairSound : ∀ {V : Type u_1} [inst : DecidableEq V] {H : Finset (Finset V)}
  (B : Erdos616R21.LBase H), Erdos616R21.Counter H → Erdos616R21.W7I H → B.PairSound
```
PairSound proof (BridgeG14Pair.lean): z := st (F ∩ F') ∈ zbox (z_mem_zbox); zumin ≤ |(F∩F')\\⋃P| ≤ u(F),u(F') (zumin_le, zU_le);
Lemma A trivial for zumin; F1 = inter3; SAME = S_a_O (F∩F' ⊆ P_i∪P_j ⇒ I ⊆ P_i∪P_j, z_q = 0 off i,j, z_U = 0) + W7I + S_b with
A-part = pc(I∧P_i∧¬P_j) + z_i (partA, via card_inter_P on (F∩F')\\P_j); L on X∪{F,F'} via new L6 (propL) for all 11 X with
region counting (card_inter_UX, outX_eq, osX_eq, 16-way case split on X's bits); D1 at derived 5-pairs both directions.
### lean/Erdos616/G14/BridgePair.lean
*[460-line listing omitted: the source is the file named in the heading.]*
### lean/Erdos616/G14/Bridge.lean (Parts A–E, as compiled)
*[1152-line listing omitted: the source is the file named in the heading.]*

## Milestone 5 (≈19:15 EDT): BridgeG14Final.lean compiles — NK4_leaf (HandA's statement) from the certificate facts, 0 sorry
Built in /tmp/g14m after HandA (HandA exit 0 39s). BridgeG14Final exit 0 time 7s.
```
'Erdos616R21.NK4_leaf_of_certs' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.lbase_of_K4' depends on axioms: [propext, Classical.choice, Quot.sound]
Erdos616R21.NK4_leaf_of_certs : G14.univOK () = true →
  G14.rootOK = true →
    (∀ r ∈ G14.reps, ∀ (M : G14.Model), M.occ G14.T[r]! → False) →
      (∀ (M : G14.Model),
          (G14.deadClause.any fun x =>
                match x with
                | (i, n) => G14.assign M i == n) =
              true →
            False) →
        Erdos616R21.NK4_leaf
```
* `W7I_of_prop`: HandA's W7I_prop (≠ 1) + S_a_A/S_a_C (≥ 1) ⇒ bridge W7I (≥ 2 on each side).
* `lbase_of_K4`: K4_3211 (HandA labels P0..P3 = E1,E2,G,G') ⇒ LBase. **Label order note:** the G14 Pm table has triple sizes
  |012|=|013|=1, |023|=2, |123|=3, while HandA's K4_3211 has |P0P2P3|=3, |P1P2P3|=2; so the base is P := (E2, E1, G, G')
  (swap of the first two), which matches exactly. Region counts via exact_pair_card; points from card_eq_one/two/three;
  injectivity via the decided column lemma G14_col (decide +kernel) + within-region distinctness.
* `NK4_leaf_of_certs (hu hr caseR caseDead) : NK4_leaf`.
### lean/Erdos616/G14/BridgeFinal.lean
*[219-line listing omitted: the source is the file named in the heading.]*

## Milestone 6 (≈19:20 EDT): G14Assembly.lean — HandA's NK4_leaf modulo only the two chunked UNSAT statements
Case modules re-run after the sandbox reset (runcases.log): Univ 49s, 15116 46s, 17917 25s, Dead 24s, 14968 32s, 16054 81s,
15954 77s — all exit 0. G14Assembly (in /tmp/g14m, imports BridgeG14Final + all case modules): MAXRSS 1801 MB.
```
'Erdos616R21.NK4_leaf_of_chunked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 G14.chk14968._native.native_decide.ax_1_1,
 G14.chk15116._native.native_decide.ax_1_1,
 G14.chk15954._native.native_decide.ax_1_1,
 G14.chk16054._native.native_decide.ax_1_1,
 G14.chk17917._native.native_decide.ax_1_1,
 G14.chkDead._native.native_decide.ax_1_1,
 G14.root_ok._native.native_decide.ax_1_1,
 G14.univ_ok._native.native_decide.ax_1_1,
 E616.w14_14968.certOk_eq._native.native_decide.ax_1_1,
 E616.w14_15116.certOk_eq._native.native_decide.ax_1_1,
 E616.w14_17917.certOk_eq._native.native_decide.ax_1_1,
 E616.w14_certdead.certOk_eq._native.native_decide.ax_1_1]
exit 0 time 1s MAXRSS 1801 MB
```
Statement: `NK4_leaf_of_chunked (h15954 : ¬ ∃ a, (LratChunk.parseDimacsFast E616C.w14_15954.cnfText).eval a = true)
(h16054 : … w14_16054 …) : NK4_leaf`. The two hypotheses are verbatim the statements of `E616C.w14_*.not_exists_sat`.
Linking them in one environment needs importing w14_15954_Final + w14_16054_Final (1.15 GB of oleans each; Lean loads
oleans fully, so RSS ≈ 1.8 GB + 2.3 GB) — over the 2.5 GB budget. Core-only closing files G14Close15954/16054.lean (one
chunked case each, no Mathlib) are being run to check the statements match: see milestone 7.
### lean/Erdos616/G14/Assembly.lean
```lean
import BridgeG14Final
import G14Univ
import G14Case15116
import G14Case17917
import G14Case14968
import G14Case15954
import G14Case16054
import G14CaseDead
/-!
# Erdős #616, r = 21: HandA's `NK4_leaf`, with every certificate fact discharged except the UNSAT statements of the two
chunked certificates (w14_15954, w14_16054), which are taken as hypotheses literally equal to the statements of
`E616C.w14_15954.not_exists_sat` / `E616C.w14_16054.not_exists_sat` (modules `w14_*_Final`, ≈1.15 GB of oleans each).
`G14Close.lean` discharges them.
-/
namespace Erdos616R21

theorem NK4_leaf_of_chunked
    (h15954 : ¬ ∃ a : Nat → Bool, (LratChunk.parseDimacsFast E616C.w14_15954.cnfText).eval a = true)
    (h16054 : ¬ ∃ a : Nat → Bool, (LratChunk.parseDimacsFast E616C.w14_16054.cnfText).eval a = true) :
    NK4_leaf := by
  apply NK4_leaf_of_certs G14.univ_ok G14.root_ok
  · intro r hr M hM
    simp only [G14.reps, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact G14.case14968 G14.univ_ok M hM
    · exact G14.case15116 G14.univ_ok M hM
    · exact G14.case15954_of h15954 G14.univ_ok M hM
    · exact G14.case16054_of h16054 G14.univ_ok M hM
    · exact G14.case17917 G14.univ_ok M hM
  · exact G14.caseDead G14.univ_ok

end Erdos616R21

#print axioms Erdos616R21.NK4_leaf_of_chunked
```

## Milestone 7 (≈19:25 EDT): **NK4_leaf proved, no hypotheses, 0 sorry** (lean/Erdos616/G14/Leaf.lean)
```lean
import G14Assembly
import w14_15954_Final
import w14_16054_Final
/-!
# Erdős #616, r = 21: HandA's leaf `NK4_leaf`, proved (G14), no hypotheses.
-/
namespace Erdos616R21

theorem NK4_leaf_proved : NK4_leaf :=
  NK4_leaf_of_chunked E616C.w14_15954.not_exists_sat E616C.w14_16054.not_exists_sat

end Erdos616R21

#print axioms Erdos616R21.NK4_leaf_proved
```
Run (LEAN_PATH = /tmp/g14m : /tmp/g14 : /tmp/g14lrat : data/chunks/w14_15954 : …/w14_16054 : /tmp/E/lib : toolchain;
script /tmp/g14m/fullrun.sh, measured with lean/dev/g14/rss.py):
```
'Erdos616R21.NK4_leaf_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 G14.chk14968._native.native_decide.ax_1_1,
 G14.chk15116._native.native_decide.ax_1_1,
 G14.chk15954._native.native_decide.ax_1_1,
 G14.chk16054._native.native_decide.ax_1_1,
 G14.chk17917._native.native_decide.ax_1_1,
 G14.chkDead._native.native_decide.ax_1_1,
 G14.root_ok._native.native_decide.ax_1_1,
 G14.univ_ok._native.native_decide.ax_1_1,
 E616.w14_14968.certOk_eq._native.native_decide.ax_1_1,
 E616.w14_15116.certOk_eq._native.native_decide.ax_1_1,
 E616.w14_17917.certOk_eq._native.native_decide.ax_1_1,
 E616.w14_certdead.certOk_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.hlast._native.native_decide.ax_1_1,
 E616C.w14_16054.hlast._native.native_decide.ax_1_1,
 E616C.w14_15954.B0.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.B1.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.B10.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.B2.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.B3.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.B4.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.B5.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.B6.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.B7.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.B8.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.B9.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_16054.B0.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_16054.B1.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_16054.B2.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_16054.B3.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_16054.B4.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_16054.B5.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_16054.B6.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_16054.B7.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_16054.B8.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_16054.B9.ok_eq._native.native_decide.ax_1_1]
exit 0 time 2s MAXRSS 1797 MB
```
Core-only closing checks (one chunked case each): G14Close15954 exit 0, MAXRSS 626 MB; G14Close16054 exit 0, MAXRSS 625 MB
(logs lean/dev/g14/logs/G14Close*.out). The B-block oleans are read from the workspace and mapped lazily, so the full
assembly fits (1.8 GB).

**Trust base of NK4_leaf_proved:** Lean kernel + the three standard axioms + the `native_decide` aux axioms listed above, i.e.
the compiled code of G14Check (univOK, rootOK, checkCNF on the six certificate CNFs; run through libG14.so) and of the LRAT
checkers (LratCheck / LratChunk: certOk_eq for 14968, 15116, 17917, certdead; block ok_eq + hlast for 15954, 16054).
Everything else (encoding soundness: Model from Counter + LBase, EdgeSound, PairSound, relabelling/root split, K4 ⇒ LBase,
W7I_prop ⇒ W7I) is kernel-checked Lean with axioms [propext, Classical.choice, Quot.sound].
Sources: HandA.lean md5 4d9a8976cacf9d48262a09f91a6bd9c9, E616Full.lean md5 61699761fc9839d65c9dbd6cc8c5549e (both as of 23:07 UTC).
Saved oleans: `olean/` (build output, not included) (G14*.olean, libG14.so, E616Full, HandA, BridgeG14{,Pair,Final}, G14Assembly, G14Full).
Rebuild in a fresh sandbox: bash lean/dev/g14/setup_all.sh; runcases.sh (7 modules, ~6 min); in /tmp/g14m compile
HandA, BridgeG14, BridgeG14Pair, BridgeG14Final, G14Assembly (runm.sh) and G14Full (fullrun.sh).
