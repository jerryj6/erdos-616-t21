> **Internal working note.** This file is a raw report written while the proof was being developed and checked. It is kept for provenance. File paths, run names and timings refer to the original working directory, not to this repository; see `docs/path-map.md` for the correspondence. The curated statements are in `paper/` and `README.md`.

# Lean formalization plan: t(21) = 4 (Erdős #616, r = 21)

Written 2026-10-16 (~15:45 EDT). Companion file with Lean sources and check logs: candidates/lean-erdos616.md.
Hand proofs: candidates/erdos-616-t21-upper.md ("upper.md"), candidates/erdos-616-loop.md §3 ("loop.md").
Referee files: erdos-616-t21-referee.md, -n4-referee.md, -w10-referee.md, -w11-referee.md, -w14-referee.md.

## 0. Target statement (matches formal-conjectures)
Source: https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/ErdosProblems/616.lean
(`erdos_616 : ∀ r ≥ 3, Hypergraph.localTransversalBound r (3*r-3) 1 = erdos_616.answer r`), with the definition from
FormalConjecturesForMathlib/Combinatorics/Hypergraph/Extremal.lean:

```lean
noncomputable def localTransversalBound (r v a : ℕ) : ℕ∞ :=
  ⨅ (b : ℕ) (_ : ∀ (n : ℕ) (H : Finset (Finset (Fin n))), H.IsUniform r →
    (∀ S : Finset (Fin n), S.card ≤ v →
      (H.hypergraphInduce S : Set (Finset (Fin n))).HasFiniteTransversal a) →
    (H : Set (Finset (Fin n))).HasFiniteTransversal b), (b : ℕ∞)
```
(`Set.HasFiniteTransversal F k := ∃ S : Finset V, S.card ≤ k ∧ ∀ e ∈ F, ∃ v ∈ S, v ∈ e`,
`Finset.IsUniform H r := ∀ e ∈ H, e.card = r`, `hypergraphInduce H S := H.filter (· ⊆ S)`, all from Finite.lean.)

r = 21 instance: **`Hypergraph.localTransversalBound 21 60 1 = 4`** (3·21−3 = 60). Note the infimum is over *valid bounds* b, so
the statement is the conjunction of
* (UB) `∀ n H, H.IsUniform 21 → Local60 H → HasFiniteTransversal H 4`, and
* (LB) some H on some Fin n is 21-uniform, Local60, and has no transversal of size 3 (so no b ≤ 3 is valid; monotonicity in b).

The formal-conjectures repo pins Lean v4.33.1 and its own Mathlib; our local toolchain is 4.35.0 + Mathlib rev 56a00585.
I copy the four definitions verbatim (same namespaces `Set` / `Finset` / `Hypergraph`) instead of importing FormalConjecturesUtil;
`Mathlib.Combinatorics.Hypergraph.Basic` exists in our Mathlib but is not needed by these defs. Porting = replacing the copied defs by
the import (they are definitionally identical; a one-line `example : ... := rfl` check on their side would confirm).

## 1. Dependency DAG
Legend: **[H]** pure hand lemma (formalize directly); **[B]** encoding-soundness bridge (every CNF clause/variable meaning must be
derived from [H] lemmas); **[C]** certificate check (CNF UNSAT, DRAT→LRAT, checked by Lean's verified LRAT checker
`Std.Tactic.BVDecide.LRAT`, trusted via `Lean.ofReduceBool`, i.e. the compiler is in the trust base);
**[F]** finite computation that is small enough for `decide`/kernel or a verified-by-construction Lean function.
Status: ✅ = formalized here with 0 sorry; ◻ = not yet.

```
                        erdos616_r21 : localTransversalBound 21 60 1 = 4
                         /                                        \
   LB: H(21,10,7) example  [H]  ✅ (four_le)             UB: no counterexample  ✅ (reduction only)
   Statement ⟺ ∀ n H, ¬Counter H : erdos_616_r21_iff ✅
   core = 10 pts, edges = 7-subsets ∪ 14 private pts       │  le_four_of_noCounter    ✅
   (EHT Thm 6(II), t=3; 120 edges, n = 1690)                │
                                                          Counter H := 21-unif ∧ PropL60 ∧ τ≥5 (every 4-set avoided)
                                                           │   local60 ↔ PropL60 (subfamily, union ≤ 60 ⇒ common pt)  ✅
                                                           │   PropL60 ⇒ minimal empty-∩ subfamilies span ≥ 61      ✅
                                                           │   F1: 2-wise and 3-wise intersecting                   ✅
                                                           │   L1 / Lemma A(i): |E∩E'| ≥ 5                           ✅
                                                           │   Lemma A(ii): some pair meets in exactly 5   [H]      ✅
                                                           │   Lemma R.1/R.2/R.3, Cor R1                   [H]      ✅
                                                           │   Lemma S(a)(b)(c), K, T                      [H]      ✅
                                                           │   cross-type classes, K4 span = 61, rigid base [H]   ✅
                                                           │   CP' (W7-5)                                  [H]      ✅
                                                           │   D1                                          [H]      ✅
                 ┌─────────────────────────────────────────┼──────────────────────────────────────────┐
         Case U (all 5-pairs uniform)              Case I (triangle, a=1 or c=1)               Case N
         W6-U  [H] + [F]                            W7-I  [H] (Tri-0, Tri-2, W7-2,            (n4-referee split, step 3)
         (propagation G, relatives, Lemma H;        W7-5=CP', Steps 0–4; fully by hand        NK dichotomy [H]
          Kneser K(9,4) connectivity: 126/126,      in upper.md §7.4; the DRAT cert            │
          closure to all 715 9-subsets of a         w7_core_A_c3 is only a cross-check)        ├─ N-K4 (3,2,1,1)
          13-set: [F], decide-able ~10^5 steps)                                               │   G14.1 relaxation Φ  [B] ← the big bridge
                                                                                              │   (18 217 traces / 49 967 states [F];
                                                                                              │    CONF: 37.6 M conflict pairs, each must
                                                                                              │    follow from A, F1, L(2/3/4 base + new),
                                                                                              │    R.3, S(a), S(b), W7-I, D1;
                                                                                              │    COV: 1730 clauses, pure bit tests [F];
                                                                                              │    symmetry 288/576-group step [H+F])
                                                                                              │   UNSAT: w14_certdead + 5 reps  [C]
                                                                                              └─ N-noK4 (NK everywhere)
                                                                                                  classes (2,4),(3,3),(3,4) [H: N8.0]
                                                                                                  (2,4): w10x exact pool encoding [B]
                                                                                                         (Lemma KB pool bound [H],
                                                                                                          totalizers/AND defs [B], tags
                                                                                                          E21, A, L/XL, R1, R3, SA, D1, W7, NK)
                                                                                                         UNSAT [C]
                                                                                                  (3,3),(3,4): w11 encodings [B] (+ N24 tag
                                                                                                         = the (2,4) theorem), UNSAT [C]
```
Order of logical use (no circularity, n4-referee step 5): W7-I ⇒ NT everywhere; G14 ⇒ no (3,2,1,1)-K4 ⇒ NK; NK ⇒ (2,4) closed;
NK + (2,4) ⇒ (3,3), (3,4) closed; W6-U closes "all uniform"; N8.0 + W7-I + non-uniformity ⇒ one of the leaves.

### 1.1 Pure hand lemmas [H] (formalize as ordinary Lean theorems about `Counter H`)
Setting lemmas (upper.md §1; loop.md §3): local60 ↔ PropL60; F1; L1; Lemma A; R.1–R.3; Cor R1; S(a)(b)(c); K; T; D1;
Tri-0..Tri-5, W7-1..W7-5 (CP'); W7-I Steps 0–4; W6-U's G, Relatives, H; N.0 (K4 count), N.4/N8.0 dichotomy and the
class enumeration under NK; Lemma KB (pool bound); the G14.1 *per-edge* rules (S13.1 lemma list) and the pairwise rules
(each is a 3–5-edge union count). All are inclusion–exclusion on ≤ 5 sets + the choice principle "τ ≥ 5 ⇒ every 4-set is avoided".
In Lean they reduce to `Finset.card_union_add_card_inter`, `card_sdiff`, disjointness, and `omega`.

### 1.2 Finite computations [F]
* W6-U: Kneser K(9,4) reachability (126 nodes) and the 715-set closure on 13 points. Small: kernel `decide` over `Finset (Fin 13)`
  is slow; better a `Nat` bitmask BFS with a proof that each step is an instance of propagation G, evaluated by `decide` or
  `native_decide`.
* W7-I: no computation needed (hand Steps 0–4).
* G14 state universe (18 217 traces × integer box) and COV clause list: must be produced by a Lean function whose output is
  proved to over-approximate the per-edge rules (soundness only needs ⊇).
* LB example H(21,10,7): τ > 3 and Local60 — hand argument (any ≤ 3 edges' 7-subsets of a 10-set share a point because
  3·7 > 2·10; 4 edges already span ≥ 4·14 + 7 = 63 > 60); no computation.

### 1.3 Encoding-soundness bridges [B] (the expensive part)
For each certificate CNF φ, one needs a Lean theorem: *Counter H (+ case hypotheses) ⇒ ∃ assignment satisfying φ*.
* **G14 (N-K4).** Variables x_t = "some non-base edge has core trace t". COV clauses: immediate from τ ≥ 5 (bit tests).
  CONF clauses ¬x_t ∨ ¬x_t': for each of up to 37.6 M pairs, "no admissible state pair (t,o),(t',o') is compatible" where
  compatibility is a conjunction of ~8 rule families quantified over integer overlap vectors z. Feasible route: write `compat`
  as a Lean `Bool` function, prove `compat_sound : Counter H → (edges F F' with traces t t') → compat t o t' o' = true` once by
  hand (it is the conjunction of the [H] pairwise lemmas), then generate the CNF *inside Lean* (`def phi : CNF Nat`), check
  `phi` = the certificate file (or skip the file and feed LRAT directly), and check UNSAT with the verified LRAT checker. The
  per-pair evaluation must run compiled (`ofReduceBool`/`native_decide`); kernel reduction of 37 M pairs is hopeless.
  Symmetry step (G14.4 item 3): prove that each of the 288 group elements is a base automorphism (finite, [F]) and that the
  counterexample predicate is relabelling-invariant ([H]).
* **w10x (2,4) and w11 (3,3),(3,4) (N-noK4).** Exact pool encoding: one Boolean per (slot edge, named or pool point) with K pool
  points (K = 114 / 104), totalizer and AND auxiliaries, lemma instances tagged E21, A, L/XL, R1, R3, SA, D1, W7, NK, TT, N24.
  The bridge must (i) build a model from a real counterexample (choose an injection of the relevant outside points into the
  pool — this is exactly Lemma KB), (ii) show every instance clause holds (each tag = one [H] lemma), (iii) show the totalizer
  definitions are satisfiable by the intended values (standard, but needs a verified totalizer encoding). Again the clean route
  is a verified Lean encoder that regenerates the CNF, rather than reasoning about the Python output.
* **Leaf CNF UNSAT [C].** DRAT → LRAT (drat-trim -L) → `Std.Tactic.BVDecide.LRAT` checker. A parallel agent is already doing
  this in work/e616lrat/ (I did not touch it). That gives "this DIMACS file is UNSAT" but **not** the bridge.

## 2. What is formalized in this session (details, sources and logs in candidates/lean-erdos616.md)
Lean file work/e616lean/Full.lean (~1 100 lines), 0 sorry, axioms = propext / Classical.choice / Quot.sound only:
* statement for r = 21 with the formal-conjectures definitions copied verbatim;
* **`erdos_616_r21_iff`: `localTransversalBound 21 (3*21-3) 1 = 4 ↔ ∀ n (H : Finset (Finset (Fin n))), ¬ Counter H`**
  — this includes the full lower bound (EHT example H(21,10,7), transported to `Fin n`);
* local condition ⟺ property L ⟺ span form; reduction to minimal empty-intersection families;
* F1, L1, Lemma A (both halves, incl. the m = 6..17 cover table), R.1–R.3, Cor R1, S(a)(b)(c), K, T, D1, CP' (W7-5),
  cross-type class bounds, N.0 span-61 count, rigid base configuration.
Not formalized: everything below the "rigid base" node (W6-U, Tri-*, W7-2, W7-I Steps 0–4, N.4/N8.0 split, KB, the per-edge
and pairwise rule lists of S13.1/G14, and all three encoding bridges).

Parallel work (not mine; candidates/lean-erdos616-lrat.md, work/e616lrat/): all 34 load-bearing leaf CNFs (W7-I cross-check,
w10x (2,4), w11 (3,4)/(3,3), the six G14 N-K4 CNFs) are UNSAT-checked in Lean via `Std.Tactic.BVDecide.LRAT.check_sound` +
`native_decide`. That closes the [C] boxes of the DAG; the [B] bridges (CNF ⇐ lemmas) remain the critical path. A bridge's
target type is now fixed: it must produce, from `Counter H` (+ case hypotheses), an assignment `a` with
`(parseDimacs cnfText).eval a = true`, contradicting that file's `not_exists_sat`.

## 3. Realistic estimate (agent-time, assuming the current hand proofs are right)
| block | size (Lean lines, rough) | effort |
|---|---|---|
| statement + UB/LB reductions + PropL + F1 + L1 + A + R + S + K + T + D1 | 800–1 200 | DONE this session (~1 100 lines) |
| LB example H(21,10,7) | 300–500 | DONE this session |
| W6-U (G, relatives, H + verified 715-closure computation) | 800–1 500 | 3–7 days |
| W7-I (Tri-0/2, W7-2, CP', Steps 0–4) | 1 500–2 500 | 1–2 weeks |
| N-split (N.0, N8.0, NK dichotomy, class enumeration) | 400–800 | 2–4 days |
| G14 bridge: verified trace/state enumerator + compat_sound + in-Lean CNF + LRAT + symmetry | 3 000–6 000 | 3–6 weeks; compiled evaluation of ~37 M pairs is the risk |
| w10x/w11 bridges: verified exact-pool encoder (KB injection, totalizers, 12 tag families) + LRAT | 4 000–8 000 | 4–8 weeks |
| LRAT checks of the leaf CNFs (parallel effort, work/e616lrat/) | – | days, mostly CPU/memory |
Total: roughly 2–4 months of focused work, dominated by the two bridge families. The single biggest de-risking step would be
to replace the w10x/w11 pool encodings by a G14-style trace relaxation if one is UNSAT for N-noK4 (one bridge design instead of two),
and to shrink G14's CONF set to its UNSAT cores (~2 M clauses total across the 6 CNFs) before bridging, since only the
clauses that the LRAT proof uses need a soundness proof.
Trust base at the end: Lean kernel + `Lean.ofReduceBool` (compiler) for the LRAT checks and the large compat evaluations.
