## Wave 10 exact-outside (2026-10-15, ~12:45–14:40 EDT; exact pool encoding, w10x_*)
**Result.**
- **N-noK4, class (2,4): CLOSED. COMPUTED, certificate verified.** UNSAT of a sound exact encoding, with a drat-trim-VERIFIED DRAT
  certificate (X.5).
- **Consequence:** in N-noK4 no 5-pair has cross-type singles of class (2,4) or (4,2).
  - Together with N8.0 (a uniform pair is impossible by W6-U, and NK leaves the classes (2,4),(4,2),(3,3),(3,4),(4,3),(4,4)), an
    N-noK4 counterexample now needs a 5-pair of class (3,3) or (3,4)/(4,3).
- **N-K4 (3,2,1,1), 24 first-generation singles: NOT decided.** The same encoding at the proved pool bound K=144 did not converge
  within the budget (X.6). This is not a result.
- No realized configuration was found.

Scope of the claim. The certificate proves this:
- there is no hypergraph containing the (2,4) base together with its 19 first-generation singles (16 of them occur in the core)
- that satisfies L on the encoded subfamilies, the proved lemmas listed in X.3 at the 5-pairs encoded, and NK.

Every one of those is a proved consequence of {L, τ ≥ 5, W7-I, N-noK4}. So the instance is impossible in N-noK4.
It is not a proof of anything in N-K4: the control *nonk* is SAT (X.5).

### X.1 Encoding (work/e616/t21/w10x_exact.py)
**Points.**
- The 61 named points of the base B0..B3 (all of B0∪…∪B3).
- K POOL points u0..u{K−1}, which lie outside the base.
- Implicit PRIVATE points: a new edge F has 21 − |F∩(named∪pool)| of them, and each lies in no other model edge.

**Variables and exactness.** One boolean per (new edge, named or pool point). A model solution is therefore a literal partial
hypergraph, and every union is exact:
|∪S| = 21|S| − Σ_a (mult_S(a) − 1)^+, where the sum runs over named and pool points only.

**Edges.**
- Base edges are constants.
- Each new edge is "an edge avoiding a given 4-set" (τ ≥ 5).
- If the 4-set is N∖{y} for a base 5-pair (Bi,Bj), the edge is the type-y single of that pair.

**Clauses.** Each clause is either the definition of an auxiliary variable (totalizer or AND) or an instance of a proved statement, tagged:
- **E21:** |F∩(named∪pool)| ≤ 21.
- **AV:** F avoids its 4-set (τ ≥ 5).
- **A (Lemma A):**
  - |F∩Bk| ≥ 5;
  - |F∩G| ≥ 5 for every pair of new edges. This is exact, because private points are never shared.
- **L:**
  - eager: L on S∪{F} for every set S of base edges, and F1 with one base edge (= L on {Bk,F,G} given Lemma A);
  - lazy: L on any subfamily, in two forms:
    - counter form: triples = common point; 4-families: Σpairs − Σtriples ≤ 23 unless there is a 4-fold common point, with sound escapes at counter caps;
    - exact per-point form "XL": Σ_a (mult−1)^+ ≤ 21m − 61, used whenever the counter form was not tight.
- **R1:** a single of a base 5-pair contains its type.
- **R3 (R.3):** a single of ANY 5-pair meets both sides in exactly 5.
- **SA (S(a)/R.3):** cross-type singles of ANY 5-pair have disjoint parts outside X∪Y.
  - Eager at the base pairs, as binary clauses that also cover the pool. So a pool point lies in at most one single per base pair.
- **D1 (§6.0):** at ANY 5-pair (X,Y), N ⊄ L ⇒ |L∩(X∪Y)| ≤ 9.
- **W7 (Theorem W7-I):** cross-type singles of ANY 5-pair meet in ≥ 2 points on each side.
- **NK (N-noK4 hypothesis, N8.0):** cross-type singles of ANY 5-pair meet in ≥ 6 points.
- **TT (W7-1 + W7-I):** no trace triangle on any edge.
- **POOL:** every pool column is used by 0 or ≥ 2 slots.
- **SB:** lex-leader (columns sorted decreasingly as vectors over the new edges) on the pool columns, and on each class of named
  points with the same base signature that lie in no avoid set. Every constraint is invariant under these column permutations.
  - Checked: no R1 point lies in such a class (w10x_core.py prints `R1 points inside a symmetry class: []`).

**Eager layer `eager2` (instances of the same lemmas, at the KNOWN 5-pairs):**
- W7(+NK) and SA for every pair of edges at every base 5-pair;
- R3 and D1 for every third edge at every second-generation pair (Bi,F), F a single of a base pair through Bi.
  These are 5-pairs by R.3.

**Lazy loop:**
1. solve;
2. decode the literal hypergraph;
3. check L on EVERY subfamily (exact DFS) and R3/SA/D1/W7/NK/TT at EVERY 5-pair;
4. add the violated instances (round-robin over kinds; an instance violated again is re-added in exact per-point form);
5. repeat.

"Violation-free SAT" would be an explicit configuration. UNSAT is checked by a separate rebuild with a DRAT proof (w10x_cert.py).

### X.2 Lemma KB (pool bound; PROVED)
Setup:
- G is a counterexample that contains the base.
- The model edges are edges of G ("slots"; two slots may be the same edge).
- U = V∖(B0∪…∪B3), and Sh = {u ∈ U : u lies in ≥ 2 slots}.

**Claim.** |Sh| ≤ ⌊½ Σ_s (21 − ν_s)⌋. Here ν_s is a proved lower bound on |F_s ∩ base|:
- ν = 9 for a single of a base 5-pair (R.3: |F∩(Bi∪Bj)| = 5+5−1);
- ν = 5 otherwise (Lemma A).

**Proof.** Each u ∈ Sh is counted at least twice in Σ_s |F_s∖base| ≤ Σ_s (21 − ν_s). ∎

**Use in the encoding.** Map Sh injectively into the pool. Every other outside point of a slot is private, and the unused columns are
empty, which satisfies POOL. So with K ≥ the bound, every clause is satisfied by the real configuration (aux = intended meaning).

**Bounds.**
- 19 singles: K = 114.
- 24 K4 singles: K = 144.
- 19 singles + 5 generic (noK4 cn24): K = 154.

**Refinement (proved, not needed here).** S(a) puts a shared point in at most one single per base pair, so
|Sh| ≤ Σ_{s ∉ g*} (21 − ν_s), where g* is the largest group. This is tighter only for unbalanced edge sets.

**Duplicates are covered.** Coinciding slots need all their outside points in the pool, and that is counted. Every encoded statement is
evaluated literally on the slot list, so a duplicate changes no union or intersection.

### X.3 Encoding controls (w10x_selftest.py; exactness and soundness against the literal semantics)
**Method.** Take a model solution S. For sampled instances that S violates, and for sampled instances S satisfies:
- build a fresh model;
- add that one instance;
- solve with every edge bit FIXED to S.

Expected: violated → UNSAT, satisfied → SAT.

**Results:** k4 (6 edges, K=8) and nok4:2,4 (6 edges, K=8), 25 + 25 instances each, both forms:
- **0 mismatches for the exact forms** (XL, XR3, XSA, XD1, XW7, XTT).
- **0 soundness mismatches for any form.** No satisfied instance was ever excluded.
- The counter forms sometimes fail to exclude a violating S (k4: L 2/8, SA 2/4; nok4: L 2/7). This is the expected
  non-tightness at caps, and the loop then escalates to the exact form.
- A first run showed a "mismatch". It was a harness artefact (instance (X,Y) order), fixed and re-run.

### X.4 Run on the N-noK4 (2,4) instance (log w10x_n24s.log, checkpoint w10x_n24s.json)
**Setup.**
- Edges: the first 24 edges of w9_cn24.json, i.e. 19 first-generation singles + 5 generic τ-edges from W9.
- K = 154 (the KB bound), eager2.

**Iterations:**

| it | result | time | instances | clauses | violations |
|---|---|---|---|---|---|
| 0 | SAT | 190 s | 6016 | 5.9 M | 6230 |
| 1 | SAT | 20 s | | | 3243 |
| 2 | SAT | 87 s | 7616 | 10.0 M | 2037 |
| 3 | **UNSAT** | 23 s | 7616 | 10.0 M | — |

**Core (w10x_core.py: a selector per lazy instance, assumptions, get_core; log w10x_n24s_core.log).**
- 380 instances: W7(+NK) 84, SA 102, D1 95, R3 93, L 3, XL 3. It is stable under re-solving.
- It mentions only the base and 16 first-generation singles:
  - (E1,E2): m0, m1, m2;
  - (E1,G): ag0, ag1, al0, al1;
  - (E2,G): cl0..cl3;
  - (E1,H): ah1;
  - (E2,H): cl0..cl3.
- No generic edge, and no TT instance.
- The 6 L-families are {E1,F2,F3,F10}, {E1,H,F7,F11}, {E1,H,F8,F11}, {E1,F0,F4,F8}, {E1,F2,F4,F9} and {E1,G,F4,F18} (indices into w9_cn24.json).

### X.5 Certificate and controls (w10x_cert.py: deterministic CNF rebuild, CaDiCaL 1.5.3 DRAT, work/e616/tools/drat-trim)
Certificates:
- **(C1) 24-edge model, K=154, 380 core instances:**
  - w10x_n24s_core.cnf (p cnf 470489 1892225) + w10x_n24s_core.cnf.drat;
  - `solve UNSAT 32.2s`, drat-trim **`s VERIFIED`** (11.6 s).
- **(C2) gen-1 only (19 edges, K=114 = its KB bound), same instances:**
  - w10x_n24s_core_n19.cnf (p cnf 304920 1352137) + .drat;
  - `UNSAT 25.0s`, **`s VERIFIED`** (9.8 s).
  - So the five generic W9 edges are not needed.
- **(C3) without any symmetry breaking (W10X_NOSB=1):** `UNSAT 30.0s`, **`s VERIFIED`** (11.7 s). So SB is not needed.

SHA-256 values are in w10x_n24s_cert.sha256 (cnf af466672…, drat 037bc6cc…, n19 cnf ad8ef018…, n19 drat e69d5fbd…).

Controls on the same 380 instances (log w10x_n24s_ctrl.log). Each one removes one ingredient, and **every one is SAT**:

| removed | result |
|---|---|
| NK | SAT, 66 s |
| L instances | SAT, 33 s |
| D1 | SAT, 88 s |
| SA | SAT, 33 s |
| W7(+NK) | SAT, 80 s |
| R3 | SAT, 36 s |

So every lemma kind is used. NK is essential, so **the statement is specific to N-noK4**. Also, the eager part plus all
6384 eager2 instances is SAT (it 0 of the run), so the base model is consistent.

### X.6 Run on N-K4 (3,2,1,1), 24 first-generation singles (w10x_k4s*.log, checkpoint w10x_k4s.json)
- **Sound run (K=144, eager2).**
  - it 0: SAT (166 s, 5.75 M clauses, 8085 violations).
  - After a restart: it 0 SAT (296 s, 7.7 M clauses, 5286 violations).
  - A third chunk (restored 7984 instances, 7.7 M clauses) did not finish its first solve within the 1150 s cap.
  - Memory was ≈1.4 GB.
  - **UNKNOWN. Not a result.**
- **Earlier variants.** Without eager2, and with K=36 (constructive only), runs k4b / k4c36 / k4e36 never fell below ≈2.5–8k violations
  per round. Accidental 5-pairs among new edges keep importing R3/SA/D1/W7 obligations.
- **Constructive side runs (NOT sound, K=36 < bound):**
  - forcing every new–new intersection ≥ 6 (`tame=1`): UNSAT in 64 s;
  - also forcing every new–base intersection outside the edge's own pair ≥ 6 (`tame=2`): UNSAT in 0.3 s.
  - Meaning, heuristically only: a configuration cannot avoid further 5-pairs among the new edges.
- **Why the K4 instance is harder than noK4 (2,4).** It has 6 base 5-pairs instead of 5, and 24 singles in 6 groups, so the pool
  bound is 144. More importantly, the solver keeps finding solutions with thousands of accidental 5-pairs among new edges. The noK4
  (2,4) run dropped to about 2000 violations by it 2 and then closed. The K4 run was still above 5000 after two rounds, each over 160 s.
- **Next step for K4.** Run the same pipeline on the 19-edge-style sub-instances: the singles of 3–4 base pairs, each at its own KB
  bound. The (2,4) core used only 16 of 19 singles. Alternatively, keep chunking with a larger memory budget.

### X.7 Follow-up: N-noK4 class (3,3) (gen1auto = all 19 first-generation singles, K = 114 = KB bound; w10x_n33g1.log)
- First chunk: violations went 1080 (it 1) → 106 → 115 → 88 → 83 → 84 → 184 → 188 → 234 → 56 → 99 → 81 → 86 → 44 (it 14).
  Clauses reached 10.2 M at it 14. Undecided when this section was written.
- A background queue (w10x_queue.sh, log w10x_queue.log) continues (3,3) for up to 3 more 19-minute chunks, then (3,4).
  - On UNSAT it runs core extraction, the DRAT certificate and the nonk control automatically.
  - On violation-free SAT it runs w10x_verify.py, a literal check of L on all subfamilies plus all 5-pair lemmas plus τ.
- **Read w10x_queue.log before citing anything about (3,3)/(3,4).** If both close, N-noK4 is closed (by N8.0 and W6-U), with the
  same caveats as X.5.

### X.8 Honest caveats
- The certificate verifies the CNF. The CNF's correctness rests on two things:
  - (i) the encoder (w10x_exact.py), spot-checked by the X.3 control;
  - (ii) the lemmas used: Lemma A, L, R.1, R.3/S(a), D1, W7-I, NK (=N-noK4), τ ≥ 5 and KB. All are proved in this file and refereed (§1, D1, W7-I).
- **No independent re-implementation of the encoder exists yet.** A referee should:
  - re-derive the 380 core instances from w10x_n24s_core.json;
  - check that each tag corresponds to its lemma;
  - ideally re-encode the core with a second, independent encoder.
- TT (W7-1) is NOT used by the core.
- The certificate is for class (2,4) under NK only. N-K4 is untouched by it (control nonk is SAT).

### X.9 Files (work/e616/t21/)
- Encoder and tools: w10x_exact.py (encoder + lazy loop), w10x_core.py (UNSAT core), w10x_cert.py (CNF + DRAT + drat-trim, controls),
  w10x_selftest.py (encoding control), w10x_verify.py (independent literal checker + τ), w10x_go.sh, w10x_ctrl.sh, w10x_ctrl2.sh,
  w10x_queue.sh.
- Data: w10x_n24s.json (checkpoint, 7616 instances), w10x_n24s_core.json (380), w10x_n24s_core.cnf/.drat, w10x_n24s_core_n19.cnf/.drat,
  w10x_n24s_cert.sha256.
- Logs: w10x_n24s.log, w10x_n24s_core.log, w10x_n24s_cert.log, w10x_n24s_ctrl.log, w10x_n24s_ctrl2.log, w10x_k4*.log, w10x_n33g1*.log.
