> **Internal working note.** This file is a raw report written while the proof was being developed and checked. It is kept for provenance. Run names and timings refer to the original working environment. The curated statements are in `paper/` and `README.md`.

> **Paths.** File paths in this report have been rewritten to their location in this repository wherever the file is
> included (`lean/`, `sat/`, `docs/`, `data/`). Paths still beginning with `work/`, `candidates/` or `/tmp/` name exploratory
> scripts, build directories or logs from the original working environment that are not part of the proof and were not
> published; nothing the final theorem or the certificate checks depends on is among them.

# Lean formalization, part HAND-A: W6-U, the Case-N split, Lemma KB, and assembly of t(21) = 4 from leaf Props

Written 2026-10-16 (~17:45 EDT). Source: `lean/Erdos616/HandA.lean` (892 lines; it imports `E616Full`, which is an
unchanged copy of `lean/Erdos616/Basic.lean` compiled as a module). **0 sorry.** Axioms: `propext`, `Classical.choice`,
`Quot.sound` only. Check time 24 s (Lean 4.35.0, Mathlib 56a00585, targeted imports). Build artefacts are in
`work/e616lean/handA_build/`: `HandA.olean`, logs, a `#print axioms` check copy, and `run.sh`.

## Milestone log
- 17:10 EDT: read the plan, Full.lean, upper.md §1/§6.3/N.4/N8.0/X.2, and the n4-referee. Designed the proof.
- 17:25 EDT: drafted HandA.lean. Env: /tmp/lean-tc lacked `Lake` and the `.ir.sig` files for Init/Std/Lean, so I copied
  them from /workspace/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean. Full.lean then compiles as module
  `E616Full` in 7 s (to /tmp/handA/E616Full.olean).
- 17:40 EDT: **all of HandA compiles, 0 sorry** (four fix rounds). Axioms checked. `HandA.olean` is importable (`import HandA`
  works with LEAN_PATH=/tmp/E/lib:/tmp/lean-tc/lib/lean:/tmp/handA).

## Final theorem
```lean
theorem erdos_616_r21_of_leaves (hW7 : W7I_leaf) (hK4 : NK4_leaf) (h24 : noK4_24_leaf)
    (h33 : noK4_33_leaf) (h34 : noK4_34_leaf) :
    Hypergraph.localTransversalBound 21 (3 * 21 - 3) 1 = 4
```
It is proved via `erdos_616_r21_iff` (Full.lean) and `noCounter_of_leaves`.

## Leaf Props (exact statements; these must be discharged by the other parts)
All leaves quantify over `n : ℕ` and `H : Finset (Finset (Fin n))` with `Counter H` (Full.lean). Write
`a = (G ∩ G' ∩ (X \ Y)).card` and `c = (G ∩ G' ∩ (Y \ X)).card`. `CrossPair H X Y G G'` means: X, Y, G, G' ∈ H,
`(X ∩ Y).card = 5`, and `∃ v w, v ≠ w ∧ G ∩ (X ∩ Y) = {v} ∧ G' ∩ (X ∩ Y) = {w}`.
| leaf | hypotheses beyond `Counter H` | conclusion |
|---|---|---|
| `W7I_leaf` | – | `W7I_prop H`: every CrossPair has `a ≠ 1 ∧ c ≠ 1` |
| `NK4_leaf` | `W7I_prop H` | `¬ K4_3211 H` (4 edges pairwise ∩ = 5, quadruple ∩ = ∅, triples \|P0P1P2\| = 1, \|P0P1P3\| = 1, \|P0P2P3\| = 3, \|P1P2P3\| = 2) |
| `noK4_24_leaf` | `W7I_prop H`, `NK_prop H` | no CrossPair with (a,c) = (2,4) |
| `noK4_33_leaf` | `W7I_prop H`, `NK_prop H`, `N24_prop H` | no CrossPair with (a,c) = (3,3) |
| `noK4_34_leaf` | `W7I_prop H`, `NK_prop H`, `N24_prop H` | no CrossPair with (a,c) = (3,4) |

`NK_prop H` says every CrossPair has `(G ∩ G').card ≠ 5`. `N24_prop H` says no CrossPair has (a,c) ∈ {(2,4),(4,2)}.
The hypotheses of each leaf are exactly the ones the refereed tree allows it to use (n4-referee step 5): G14 uses W7-I;
w10x uses NK; w11 uses NK + N24. There is no circularity. NK and N24 are *derived* inside `noCounter_of_leaves`
(NK from NK4_leaf, N24 from noK4_24_leaf plus the swap); they are not assumed.

## What is proved (all 0 sorry)
1. **Theorem W6-U** (`W6U : Counter H → AllUniform H → False`), upper.md §6.3. The two finite computations of the
   hand proof are replaced by short arguments, so **no computation is used**:
   - `good_step` = propagation G. `good_swap` = two G-steps swap one point of N for one point of (X∩S)∖Y.
   - `good_reach` = induction on |N∖T|, which replaces the Kneser K(9,4) connectivity check.
   - `good_relative` = relatives. `good_H` = Lemma H.
   - `good_all`: every S∖D (D a 4-subset of S) is reached in two relative steps, because the complements walk on
     K(13,4) and any two 4-sets of a 13-set have a common disjoint 4-set. This replaces the 715-set closure.
   - `good_base` builds the 13-set S = M ∪ A0 ∪ C0 from Lemma A + R2 + uniformity.
   - In `W6U`, s0 plus a partition of S∖{s0} into 4 triples gives four good edges. The union bound
     (12 + 4·12 = 60) needs no disjointness. Only *one* application of Lemma H is needed, to get W2 ∩ (W1∖S) = ∅,
     which forces the empty intersection. L4 then gives the contradiction.
   - "Good pair" is defined as `Good H S X Y`: X∩Y ⊆ S, and every single F of type y has F∩(X∪Y) = S∖(N∖{y}).
2. **Case-N split** (n4-referee steps 1–5, N.4/N8.0):
   - `parts_eq_of_44`.
   - `nonuniform_cross`: a non-uniform pair has a CrossPair of class ≠ (4,4). The same-type case goes through a
     third-type single.
   - `crossPair_class` (wraps `cross_class`).
   - `K4_of_32`: class (3,2) gives `K4_3211` with P = (X, Y, G, G').
   - `crossPair_swap`: E1↔E2.
   - `K4_of_not_NK`: ¬NK + W7-I gives (a,c) ∈ {(3,2),(2,3)}, hence a K4. The (2,3) case uses the swap.
   - `noCounter_of_leaves`: the case analysis is done by `omega` over a,c ∈ [2,4], a+c ≥ 5, a+c ≠ 5, ¬(4,4), which
     leaves (2,4) / (4,2) / (3,3) / (3,4) / (4,3). The (4,2) and (4,3) cases use the swap.
3. **Lemma KB** (X.2):
   - `KB`: for slots `F : ι → Finset V` with |F s| = 21 and ν s ≤ |F s ∩ B|, we have 2·|sharedPts| ≤ Σ(21 − ν s).
     This is double counting.
   - `KB_pool`: an injection of the shared points into `Fin K` whenever |Sh| ≤ K.
   - `nu_single` (ν = 9, i.e. |F ∩ (a∪b)| = 9 for a single) and `nu_any` (ν = 5).

## What is left (not in my scope)
The five leaves. Their bridges + LRAT certificates belong to the W7I / BridgeW10 / BridgeG14 agents. To plug in:
`import HandA`, then prove `W7I_leaf` etc. in exactly the form above, and apply `erdos_616_r21_of_leaves`. If another
part states a leaf differently (e.g. over arbitrary `V`, or with a different K4 labelling), it needs a ≤ 20-line
adapter. `K4_3211`'s labelling is (P0,P1,P2,P3) = (E1,E2,G,G') for a class-(3,2) pair. It is the w13/w14 base up to an
S4 relabelling (n4-referee).

## Check log (HandACheck = HandA.lean + `#print axioms`)
```
HandACheck.lean:439:5: warning: Variable name `hS13` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hS13
Note: This linter can be disabled with `set_option linter.unusedVariables false`
'Erdos616R21.W6U' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.nonuniform_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.K4_of_not_NK' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.noCounter_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.erdos_616_r21_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.KB' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.KB_pool' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos616R21.nu_single' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`HandA.lean` compiled to `HandA.olean`: `exit 0 time 24s`, empty output (no warnings). Then `Use.lean` (`import HandA`) gives:
```
'Erdos616R21.erdos_616_r21_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]
Erdos616R21.erdos_616_r21_of_leaves : Erdos616R21.W7I_leaf →
  Erdos616R21.NK4_leaf →
    Erdos616R21.noK4_24_leaf →
      Erdos616R21.noK4_33_leaf → Erdos616R21.noK4_34_leaf → Hypergraph.localTransversalBound 21 (3 * 21 - 3) 1 = 4
```

## Full source: lean/Erdos616/HandA.lean
*[892-line Lean listing omitted here: it duplicates a source file now under `lean/` (see `docs/path-map.md`).]*
