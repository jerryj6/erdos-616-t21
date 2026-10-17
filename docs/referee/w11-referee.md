> **Internal working note.** This file is a raw report written while the proof was being developed and checked. It is kept for provenance. Run names and timings refer to the original working environment. The curated statements are in `paper/` and `README.md`.

> **Paths.** File paths in this report have been rewritten to their location in this repository wherever the file is
> included (`lean/`, `sat/`, `docs/`, `data/`). Paths still beginning with `work/`, `candidates/` or `/tmp/` name exploratory
> scripts, build directories or logs from the original working environment that are not part of the proof and were not
> published; nothing the final theorem or the certificate checks depends on is among them.

# Referee report: Wave 11 N-noK4 classes (3,3) and (3,4)/(4,3) (Erdős #616, r = 21)
Referee run 2026-10-15, started 19:15 EDT. Hostile reading. IN PROGRESS (sections are filled in as work completes).
- **Scope:** docs/proof-notes.md, "Wave 11 noK4 (3,3)/(3,4)" W11.0–W11.6 (W11.5/W11.6 sit after the B11 sections).
- **Taken as SOUND without re-checking:** everything refereed in docs/referee/t21-referee.md and
  docs/referee/w10-referee.md (Lemma KB, R.1–R.3, S(a), D1, W6-U, W7-I, NK under N-noK4, the (2,4) theorem).
- **Independent work:** work/e616/w11ref/ (new directory). Encoder written from the statements; reuses only the
  predecessor referee's CNF helpers (sat/w10ref/ref_enc.py), never w9/w10x/w11 code. Only the instance lists
  (which edges each lemma instance names) are read from the authors' checkpoints.

## 1. Coverage argument (W11.1): **SOUND**
**Base forced.** Let (E1,E2) be a 5-pair (N = M = {v,w,m0,m1,m2}) with cross-type singles G (type v), H (type w) of class (a,c),
a on the E1 side. R.3: |G∩E1| = |G∩E2| = 5 with G∩M = {v}, so A_G = G∩E1∖M and C_G = G∩E2∖M have 4 points each (same for H).
S(a): G, H have no common point outside E1∪E2; so |G∩H| = a + c and the outside parts are disjoint 12-sets. Everything else in
E1, E2 is a named "rest" point. This is exactly base_nok4(a,c): 5 + (16) + (16) + 12 + 12 = 61 points; unique up to relabelling.
My encoder rebuilds it from these relations and asserts them (ref_enc11.py: |G∩H| = a+c, the four 5-pairs to E1/E2, disjoint
outsides). (4,3) is (3,4) with E1↔E2 swapped (the definition of a 5-pair and of class is symmetric). ✔
- Base 5-pairs: exactly E1E2, E1G, E1H, E2G, E2H (|G∩H| = 6 resp. 7). Asserted. ✔
**Slots exist in every configuration of the class.**
- 16 first-generation singles. For a base pair (Bi,Bj), N = Bi∩Bj, y ∈ N not realised by a base edge: τ ≥ 5 gives an edge F
  avoiding N∖{y}; R.1 (N is a transversal) gives y ∈ F, so F is a type-y single. The generic list has 3+4+4+4+4 = 19; sel drops the
  three (E1,H)-singles of types al0,al1,al2 (fewer edges = relaxation). I re-derived the list and checked it against the
  authors' setup() output name by name (xcheck_slots.py): identical avoid sets in the same order, for both classes. ✔
- **J31** = an edge avoiding {al0,al1,al2,cl0}. τ ≥ 5 says no 4-set is a transversal, so such an edge exists. Nothing else is
  assumed (my encoder adds only AV for it: no R1, no single-status, no R3/SAbase). It is not a base edge (E1,G,H ∋ al0, E2 ∋ cl0).
  It may coincide with a first-generation single (e.g. an m-single); the literal semantics make that harmless (w10 referee §1a:
  repeated edges are evaluated literally, and the KB count already covers shared outside points). ✔
  - For (3,3) "al0,al1,al2" is all of A_G∩A_H and cl0 one of the 3 points of C_G∩C_H; for (3,4) one of 4. Any choice is WLOG
    (the other cl_i are symmetric in the base), but none is needed: the slot is just *some* edge avoiding that fixed named set. ✔
**Pool bound K = 104.** Lemma KB: a first-generation single has ν = 9 (R.3: |F∩(Bi∪Bj)| = 9), so ≤ 12 points outside the 61;
J31 has ν = 5 (Lemma A with any one base edge gives ≥ 5 base points), so ≤ 16 outside. Σ = 16·12 + 16 = 208, and every point
outside the 61 that lies in ≥ 2 slots is counted ≥ 2 times: |pool| ≤ 104. My encoder computes this bound independently
(ν = 9 only when the avoid set is N∖{y} of a base pair) and gets KB = 104; J31 is counted with ν = 5, correctly. ✔
(The authors' w10x_w11n34min.json records K = 142 — a leftover from the 22-slot parent run — but the certificate log
w11n34min_cert.log shows the CNF was built with K = 104; my independent run uses K = 104 in any case.)
**One instance per class, no case split.** Correct: every model edge exists in every configuration of the class, and all
instances are conditional lemma instances, so UNSAT of one instance excludes the class. ✔

## 2. Tag N24 (Wave-10 (2,4) theorem used as a lemma at arbitrary 5-pairs): **SOUND**
- The Wave-10 statement (refereed SOUND) is: in any configuration satisfying {L, τ ≥ 5, W7-I, N-noK4}, no 5-pair (X,Y) has
  two cross-type singles of class (2,4) or (4,2). Its hypotheses are *global* (N-noK4 = no (3,2,1,1)-K4 anywhere; Case N is an
  existential case, not a property of a distinguished pair), and its proof forces the (2,4) base from R.3/S(a) at *whatever*
  5-pair carries the class. So it holds at derived 5-pairs (slot–slot, base–slot) as well as at base pairs.
- No circularity: the Wave-10 certificate uses only L, R3, SA, D1, W7, NK (no N24, no (3,3)/(3,4) fact).
- Application: every N24 instance [N24, X, Y, Z1, Z2] is encoded (authors and mine) conditionally on |X∩Y| = 5 (counting pool
  points), |Z1∩N| = |Z2∩N| = 1 and Z1∩Z2∩N = ∅ (different types). Under these hypotheses Z1∩Z2∩(X∖Y) = A_{Z1}∩A_{Z2}, so the
  consequent "(|Z1∩Z2∩(X∖Y)|, |Z1∩Z2∩(Y∖X)|) ∉ {(2,4),(4,2)}" is exactly the theorem. Nothing is asserted when the hypotheses fail.
  Checked in w10x_exact.py (pre5 + single + single + qa, then the two forbidden (2,4)/(4,2) value pairs) and re-encoded by me.
- The N24 instances in the cores: 50 ((3,4)) and 95 ((3,3)); eager ones at base pairs, the rest at derived pairs. All are of
  the above conditional form, so "applied only where hypotheses hold" is guaranteed by the encoding, not by the instance list.

## 3. Independent re-encoding (work/e616/w11ref/)
**Encoder ref_enc11.py.** Base, 16 singles and J31 rebuilt from the definitions (§1); only the instance lists are read from the
authors' checkpoints (w10x_w11n34min.json sha256 4053982…, 637 instances; w10x_w11n33z1_dcore.json sha256 2bb2011…, 2394).
Model = the predecessor's (sat/w10ref/ref_enc.py): slot bits over 61 named + K = 104 pool points, privates implicit,
NO symmetry breaking and NO "pool point in 0 or ≥ 2 slots" restriction. Eager: AV (and R1, R3-at-base, SAbase for the 16 singles
only), E21, Lemma A (slot–base, slot–slot), D1 at the 5 base pairs, L on {base subfamily}+slot, F1. Lazy instances in exact
per-point form conditional on their hypotheses: R3, D1, SA, W7(+NK), L, and **N24** (§2). Auxiliaries: Tseitin AND and full
Sinz counters (both directions). Option `compact` (used for (3,3) only, to stay under 2 GB): (i) L on 3 edges is encoded as
"common point" — equivalent given the eager Lemma A clauses, since three pairwise-≥5 edges without a common point have union
≤ 48 < 61; (ii) L on 4 edges: with no common point mult ≤ 3, so Σ(mult−1)^+ = #[mult≥2] + #[mult≥3] ≤ 23; (iii) the D1 and
L4 cardinality bounds use pysat's one-directional kmtotalizer, guarded by the hypothesis literal(s). (ii)/(iii) only drop
clauses that a real configuration satisfies anyway, so UNSAT of the compact CNF still implies UNSAT of the statements.
Solver: **Glucose 4 (pysat 1.9.dev16)**, not CaDiCaL. Checker: work/e616/tools/drat-trim.

### 3a. (3,4)/(4,3), instance w11n34min: **SOUND — UNSAT, `s VERIFIED`**
- ref_n34.cnf (full, non-compact encoding; 670797 vars, 2530515 clauses; regenerated byte-identically with `oldcap`,
  sha256 798ed3b9…): **Glucose 4 UNSAT in 130.7 s** (RSS 301 MB). DRAT ref_n34.cnf.glucose4.drat (27.2 MB):
  **drat-trim `s VERIFIED`** in 26.8 s; core 73479 clauses, 19547 lemmas, 0 RAT lemmas. Log solve_n34_glucose4.log.
- Authors' certificate files re-hashed: `sha256sum -c` OK for w10x_w11n34min.cnf/.drat and w10x_w11n33z1_dcore.cnf/.drat.
- Authors' (3,4) certificate re-checked by me: drat-trim on w10x_w11n34min.cnf + .drat → **`s VERIFIED`** (46.8 s; core 56905 of
  1544863 clauses, 0 RAT; log w11ref/authdrat34.log).

### 3b. (3,3), instance w11n33z1_dcore — RUNNING
- ref_n33c.cnf (compact encoding; 2071895 vars, 6924878 clauses; 2394 instances; K = 104): first Glucose 4 attempt (19:39 EDT)
  killed by a sandbox restart (~20:26 EDT, no result). Restarted 20:30 EDT; killed again by a
  sandbox restart at ~21:14 EDT after ~16 CPU-min (CPU 0 shared by ~6 jobs). **Restarted 21:17 EDT** (run_n33s.sh → solve_n33c_glucose4.log).
- Hedge against further restarts (≈ every 50 min today): **cube-and-conquer** on the same CNF, cube33.py: split on J31's membership
  bits of v, w, m0, m1, m2 (32 cubes, exhaustive, so all-UNSAT ⇒ UNSAT); each cube = CNF + 5 units, Glucose 4 + DRAT, drat-trim on
  (cube CNF, proof); results persist in cube33_results.jsonl, finished cubes are skipped after a restart. Started 21:41 EDT.
  By 22:04 EDT 11/32 cubes were refuted and `s VERIFIED` (all near-trivial, solve 0.0 s, cores of 6–74 clauses: the 8 cubes with v, w ∉ J31, and
  [¬v, w, ¬m0] with ≤ 1 of m1, m2);
  cube [¬v, w, ¬m0, m1, m2] was the first hard one. **Another sandbox restart at ~22:04 EDT** killed it and the plain solve
  (≈ 20 CPU-min, no result). Switched to an adaptive version, cube33b.py (started 22:07 EDT): 900 s budget per cube; a cube that
  times out is replaced by its 4 children on the next two J31 bits (ag0, ah0, cl1, cl2, cg0, ch0, a0*, c0*), so the pending
  leaves always cover the unrefuted space; queue in cube33_queue.json, results cube33_results.jsonl, log cube33b.log.
  Observation (heuristic only): in the hard branch J31 is quickly forced to contain w, m1, m2, ag0, ah0, cl1, cl2 (each opposite
  polarity refuted in ≤ 0.4 s, all `s VERIFIED`), so splitting on those bits gave no speed-up; since 22:42 EDT the splitter
  probes candidate bits with a 3000-conflict budget and splits only on bits where both polarities survive.
  Probe result (23:06 EDT, cube [¬v,w,¬m0,m1,m2,ag0,ah0,cl1,cl2]): every remaining named J31 bit has one polarity refuted within
  3000 conflicts (cg0 ∈ J31, ch0 ∉ J31, J31 avoids all a0*, c0*), so J31's named part is essentially forced and J31-bit splitting
  is useless. Another restart at ~22:59 EDT. Since 23:08 EDT the hard cube runs **unbounded with MapleLCMDistChronoBT**
  (pysat 'maplechrono', DRAT; again not CaDiCaL), run_hard.sh; the remaining 20 level-0 cubes (v ∈ J31) follow with Glucose 4.
  23:31 EDT: MapleChrono abandoned after ~24 CPU-min on the hard cube (no result). Found a third non-CaDiCaL solver binary,
  **Kissat 4.0.4** (from the PyPI wheel passagemath-kissat 10.8.13, aarch64; installed as work/e616/tools/kissat). Since 23:32 EDT
  Kissat runs on the **full** ref_n33c.cnf (no cubes) with binary DRAT streamed to disk, then drat-trim (run_kissat33.sh,
  kissat33.log). The 13 cube refutations above stay valid but are no longer needed if this finishes.

  **00:17 EDT (Oct 16): the full-CNF Kissat run was killed by another sandbox restart at ~23:43 EDT after ~517 s CPU (no result;
  kissat33.out). Resumed cube-and-conquer with Kissat instead (cube33k.py / run_cube33k.sh, log cube33k.log; same queue
  cube33_queue.json and results file, same covering invariant). State at resume: 19 leaves refuted and `s VERIFIED` (all Glucose 4),
  21 pending: the hard leaf [¬v,w,¬m0,m1,m2,ag0,ah0,cl1,cl2] (now on Kissat, 20000 s budget), 4 cubes [¬v,w,m0,·,·] and the 16
  level-0 cubes with v ∈ J31 (Kissat, 1200 s budget each, split into 4 children on timeout).**
  01:01 EDT: hard leaf still running on Kissat (~13 CPU-min so far on a CPU shared 3-way; binary DRAT 660 MB in /tmp).
  (3,3) controls moved to Kissat as well (ctrl33k.sh; drop=N24 running since 00:45 EDT, then nonk).
  **Sandbox restart ~01:03 EDT killed both (hard leaf after ~800 CPU-s, no result).** Restarts now come every ~45 min, so a
  monolithic solve is hopeless. Since 01:08 EDT: cube33L.py (run_cube33L.sh, log cube33L.log): Kissat with a 400 CPU-s budget
  per leaf; a leaf that times out is split into cube+[x], cube+[¬x] with x chosen by a unit-propagation lookahead
  (product of implied-literal counts) over the 17×61 named slot bits; every refuted leaf drat-trim'd; queue persists.
  (01:16 EDT: one wasted split on a root-fixed variable — x = slot0∋v, refuted child `s VERIFIED`, other child = same cube; lookahead
  now skips failed literals.) Controls restarted 01:08 EDT.
  01:42 EDT: lookahead splitting gave no easy leaves after 6 levels (every child timed out at 150 s). Paused (queue kept, 28 leaves).
  **Referee WLOG clauses (add_wlog.py → ref_n33cw.cnf = ref_n33c.cnf + 6815 clauses, 1648 aux vars):**
  (a) POOL — a pool point in some slot is in ≥ 2 slots. WLOG because, checked clause-family by clause-family in ref_enc11.py,
  every statement depends on a pool point p only through ANDs of ≥ 2 *distinct* slots' bits at p (intersections in A, F1, SA,
  R3/D1/SA/W7/N24 hypotheses and consequents, L multiplicities), except E21 (|slot| ≤ 21, monotone down) and the D1 body
  L∩(X∪Y) (an ATMOST, monotone down; with L ∈ {X,Y} its hypothesis |L∩X∩Y| ≤ 4 is false); deleting p from its unique slot
  (it becomes one of that slot's implicit private points) therefore keeps every statement true.
  (b) LEX — pool columns (17-bit membership vectors) lexicographically non-increasing in pool index. WLOG because all
  constructions range uniformly over the 104 pool indices (base edges and avoid sets contain no pool point), and (a) is
  permutation-invariant. (The authors use the analogous POOL and SB families: 1768 POOL clauses = 104·17, as here.)
  Semantically this is just canonical labelling: a configuration is encoded with its outside points of multiplicity ≥ 2 (at most
  KB = 104 of them) as pool points in lex order and all others as implicit privates. Empirical check: the drop=N24 SAT model
  (§4c) had **80 single-slot pool points**; after normalising it by (a)+(b) (23 multi-slot columns, sorted) the literal re-check
  is identical (only the same 4 N24 instances violated, eager 0; c33_N24w.cnf.*). This redundant freedom is the likely reason my
  encoding was so much harder than the authors'.
  So UNSAT of ref_n33cw.cnf ⇒ the (3,3) statements are inconsistent. Since 01:44 EDT: Kissat on the full ref_n33cw.cnf
  (run_kw33.sh → kw33.log; proof /tmp/kw33.drat; then drat-trim on ref_n33cw.cnf).
  Restart ~01:58 EDT killed that run (~6 CPU-min). 02:02–02:09 EDT: the lookahead cube tree continued on ref_n33cw.cnf (still
  timeouts, queue 29 leaves). 02:09 EDT: full Kissat on ref_n33cw.cnf relaunched right after the restart (proof now written to
  the persistent disk, ref_n33cw.kissat.drat, so drat-trim can run in a later window); ~15 CPU-min by 02:40 EDT, proof 570 MB, no
  result yet. Fallback prepared: cube33M.py (leaves = ranges of m, the number of shared outside points; under POOL+LEX
  "m ∈ [lo,hi]" ⇔ column lo−1 non-empty ∧ column hi empty, so the ranges partition [0,104]; split on timeout).
  Restart ~02:49 EDT killed the full run (~19 CPU-min, no result). 02:51–03:10 EDT cube33M: leaves m ∈ [41,104] and [41,72]
  both timed out at 500 s (full CPU) — the m-split is not easier either. 03:10 EDT: Kissat --unsat tried (abandoned after 5 min for:)
  **(c) named-group LEX** (add_wlog.py `named` → ref_n33cw2.cnf = ref_n33c.cnf + 8873 clauses): lex order also inside each group
  of interchangeable named rest points a0* (11, only in E1), c0* (11, only in E2), og* (12, only in G), oh* (12, only in H).
  WLOG: avoid sets / single types involve only M, al, ag, ah, cl, cg, ch, and a rest point enters only via base membership
  (identical within its group) and uniform per-point constructions; blocks are disjoint, so all can be sorted at once.
  Empirical: the N24 model normalised by (a)+(b)+(c) re-checks identically (c33_N24w2.cnf.*). The authors' SB is the analogous
  family ("lex-leader on pool columns and on columns of interchangeable named points", w10x_exact.py docstring).
  Since 03:15 EDT: Kissat on the full ref_n33cw2.cnf (run_kw2_33.sh → kw2_33.log, proof ref_n33cw2.kissat.drat on disk).

### 3c. Authors' (3,3) certificate w10x_w11n33z1_dcore.cnf/.drat: **`s VERIFIED`** (re-checked 00:20–00:44 EDT Oct 16)
- `sha256sum -c w10x_w11n33z1_dcore_cert.sha256`: both files OK (cnf 69911893…, drat 3efdd06d…).
- drat-trim (work/e616/tools/drat-trim, backward mode): **`s VERIFIED`**, verification 1464 s (CPU 0 shared 3-way); core 366021 of
  4641833 clauses, 341436 of 6296537 lemmas, **0 RAT lemmas**. Log authdrat33.log/.out. (Authors reported 669 s, core consistent.)
- This certifies the *authors'* CNF (which includes their symmetry breaking SB, 14645 clauses; refereed separately: the authors'
  nosb run is also UNSAT+VERIFIED per w11n33z1_dcore_cert.log, not re-run by me). The CNF-to-statement link is checked by §3b.

## 4. Controls (my encoder)
### 4c. (3,3) controls (my compact encoder, Kissat 4.0.4; ctrl33k.sh)
- **drop=N24: SAT** (Kissat, 01:49 EDT; ~41 min wall on shared CPU 0). Literal re-check of the model (ref_check11.py, ctrl33k_N24.log):
  all 2299 non-N24 instances hold (W7 285, SA 511, R3 319, D1 786, L 398), eager violations 0; of the 95 N24 instances 91 hold and
  4 are violated (c33_N24.cnf.viol_inst.json: [E1,E2; G, slot0], [E1,E2; G, slot2], [E2,G; E1, slot9], [E2,G; E1, slot10]). So N24 is
  needed for this instance list — matches the authors' drop=N24 SAT.
- nonk: running.
### 4a. Soundness control against the authors' literal configurations (does my encoding exclude a real configuration?)
- The authors' violation-free 16-single configurations (t21/w10x_w11n34m_real.json, w10x_w11n33m_real.json; τ = 2, so they
  contain no J31) were mapped onto my slots by ref_check11.py `real` (fix34_real.json, fix33_real.json): every core instance not
  involving J31 holds literally (viol lists empty). Then: my encoder with option `noJ31` (16 slots, KB = 96 ≤ K), slot bits FIXED
  to the real configuration, all eager statements + every such instance.
- **(3,4): SAT** (548 instances, 1.82 M clauses; real_ctrl34.log). My encoding accepts a literally valid configuration. ✔
- **(3,3): SAT** (2015 instances, compact encoding, 5.65 M clauses; real_ctrl33.log). The 3 instances that mention J31 but are
  vacuous at the real configuration (their 5-pair hypothesis fails before J31 is read) were left out. ✔
- So neither encoding (full or compact) over-constrains on a real configuration of the 16 singles; together with the authors'
  τ = 2 observation this also confirms that J31 is the edge doing the work.
### 4b. (3,4) drop-one-kind controls (my encoder, full encoding; each SAT model re-checked literally by ref_check11.py) — (interim) logs ctrl34_KIND.log
| drop | result | literal re-check of the model (core instances) |
|---|---|---|
| N24 | **SAT** 152.6 s | only N24 violated (3); all else holds; eager violations 0 |
| L | **SAT** 19.6 s | only L violated (4) |
| D1 | **SAT** 38.7 s | only D1 violated (15) |
| SA | **SAT** 42.1 s | only SA violated (28) |
| W7 | **SAT** 341.8 s | only W7 violated (23) |
| R3 | **SAT** 153.6 s | only R3 violated (6) |
| nonk (W7 without the |Z1∩Z2| ≥ 6 part) | **SAT** 89.8 s | every instance holds under nonk semantics; eager violations 0 |
- **Verdict (3,4) controls: SOUND.** Each kind (N24, L, D1, SA, W7, R3) is needed for this instance list, and the result is specific
  to N-noK4 — matching the authors' w11n34min_cert.log, now reproduced with a different encoder and solver.
- In the L/D1/SA models the checker also finds one slot–slot–slot triple without a common point (F1 for three slots is not an eager
  statement of the encoding, only for base+2 slots). Harmless: a control only shows that the dropped kind is *needed within this
  instance list*; the N24 model is clean even under that extra literal test.

## §5 independent (3,3) via trace encoding (started 2026-10-16 12:55 EDT; sat/w11ref/tr/)
Route: the slot/pool re-encoding of §3b never finished (sandbox resets every ~45 min; cube tree stalled; cube33L put on hold,
file w11ref/cube33L.hold, queue kept). New route in the style of the refereed Wave 14 N-K4 model Φ, but written from scratch
(tr_core.py imports nothing from w9/w10x/w11/w13/w14/w14ref). Only the authors' literal realization JSONs are read, as DATA.
### 5.1 The model Φ_{a,c} and its soundness (PROVED)
**Base.** As §1: E1=P0, E2=P1, G=P2 ∋ v, H=P3 ∋ w, core C = points in ≥ 2 base edges = {v,w,m0..2, al*(a), ag*/ah*(4−a),
cl*(c), cg*/ch*(4−c)}, |C| = 21−a−c (15 for (3,3)); private parts O_q, |O| = (8+a, 8+c, 12, 12). tr_core.base() asserts all
defining relations (five 5-pairs, |G∩H| = a+c, types, Σ = 61).
**State of a non-base edge X:** (b, o) with b = X∩C, o_q = |X∩O_q|, u = 21−|b|−Σo ≥ 0. **Universe** = all (b,o) passing the per-edge
rules below, over the FULL integer box 0 ≤ o_q ≤ |O_q|, |b|+Σo ≤ 21 (lower bounds only from Lemma A, which is itself a rule).
**Per-edge rules (edge_ok)**, each an instance of a refereed lemma with X and base edges only: A (|X∩P_q| ≥ 5); F1 (X meets every
P_i∩P_j, incl. G∩H); L on {S, X} for every S ⊆ base, |S| ≥ 2 (exact union, common point only possible in core); at each base
5-pair (P_i,P_j): D1, R3 for X single, and for X single + base single P_k of another type: SA (X∩P_k ⊆ P_i∪P_j, incl. o_k = 0) and
CLS(a,c) on a = |X∩P_k∩P_i∖P_j|, c = |X∩P_k∩P_j∖P_i|; at each derived 5-pair (P_i,X) (|X∩P_i| = 5, N = X∩P_i incl. o_i private
points): D1 for every base P_j with N ⊄ P_j, R3 for base singles, and for two base singles P_j,P_k of different types SA
(P_j∩P_k ⊆ P_i∪X) and CLS(|P_j∩P_k∩P_i∖X|, |P_j∩P_k∩X∖P_i|).
CLS(a,c) := a,c ≥ 2 (W7-I) ∧ a+c ≥ 6 (NK: N-noK4 + N.0) ∧ (a,c) ∉ {(2,4),(4,2)} (N24, Wave 10). N34 is NOT used (flag off).
**Pair rules (pair_ok)** for two DISTINCT non-base edges F,F' with states s,s': compatible iff SOME integer overlap vector
z_q = |F∩F'∩O_q| ∈ [max(0,o_q+o'_q−|O_q|), min(o_q,o'_q)], z_U ∈ [0, min(u,u')] (the complete set of integer possibilities; core
overlap is b∧b') satisfies all of: A; F1 with each P_q; L on {S,F,F'} for every S, |S| ≥ 2 (exact); SAME: both singles of a base
5-pair, different types ⇒ SA (no common point outside P_i∪P_j: core, other O's, U) + CLS; derived 5-pair (P_k,F) (both orders):
D1 for F' (N ⊄ F'), and if F' is single there: R3 (|F'∩P_k| = |F'∩F| = 5) and, for each base single P_j of another type,
SA (F'∩P_j ⊆ P_k∪F, incl. O_j points of F' outside F) + CLS(|F'∩P_j∩P_k∖F|, |F'∩F∩P_j∖P_k|); derived 5-pair (F,F') (|F∩F'| = 5):
D1 for every base P_j with N ⊄ P_j, R3 for base singles, and two base singles P_j,P_k of different types: SA (P_j∩P_k ⊆ F∪F')
+ CLS. A trace pair is a CONFLICT iff no state pair is compatible.
**Φ:** x_t per trace of the universe; COV(B) = ∨_{t∩B=∅} x_t for every core 4-set B meeting all four base edges; CONF ¬x_t∨¬x_t'.
**Claim.** An N-noK4 counterexample with a class-(a,c) 5-pair gives a model x_t := [some non-base edge has core trace t].
*Proof.* Every non-base edge satisfies the per-edge rules (each is a lemma instance with that edge and base edges), so its
trace is in the universe. COV: τ ≥ 5 gives an edge avoiding B; B meets every base edge, so that edge is non-base and its trace
avoids B. CONF: two non-base edges with traces t ≠ t' are distinct; their true states and true overlaps (which lie in the stated
integer ranges) satisfy every pair rule, each an instance of a lemma (A, F1, L, R3, SA=R.3/S(a), D1, W7-I, NK, N24) at a 5-pair
whose hypotheses are tested exactly from the counts; hence (t,t') is not a conflict. ∎ Several edges per trace are harmless (no
clause relates a trace to itself). Restricting τ ≥ 5 to core 4-sets is a weakening. NK uses N-noK4 at every 5-pair (global
hypothesis; refereed in the w10 report §3); N24 is the refereed Wave 10 theorem, valid at every 5-pair (§2 above).
### 5.2 Milestones
- 13:02 EDT universe (tr_states.py, st_33.npz): **10 674 traces, 35 493 states** (sizes 4:9, 5:95, 6:653, 7:2316, 8:4143,
  9:3455, 10:2, 15:1).
- 13:03 EDT positive control (tr_real.py; authors' literal 16-single configuration w10x_w11n33mN_real.json, the N24-respecting
  one, read as data; base labelling and private parts asserted literally): **16 edges all in the universe, edge_ok failures 0,
  120 pairs, pair-rule violations at the TRUE overlaps 0.** On w10x_w11n33m_real.json (built without N24) 2 edges and 2 pairs
  fail, and with the N24 line removed from CLS all pass: the rules are not stricter than the lemmas, and N24 is live.
- 13:05 EDT full conflict matrix (tr_conf.py, all trace pairs, no symmetry transport) running in resumable 200-row chunks.
- 13:19 EDT full matrix done (54 chunks): **9 653 036 conflict pairs** of 56.96 M (density 0.169). Φ_33 = phi33.cnf: 10 674 vars,
  **1325 COV clauses** (core 4-sets meeting all four base edges; every COV non-empty, min 24 literals) + 9 653 036 CONF.
- 13:21 EDT **Kissat 4.0.4 on the full Φ_33 (no symmetry breaking, no units, no case split): `s UNSATISFIABLE` in ≈ 2 min**;
  binary DRAT phi33.drat (33 MB). drat-trim running (CPU 0 shared 3–4 ways).
- 13:2x EDT controls already in: (i) symmetry sanity (tr_sym.py): the base group (m, al, cl permutations, G↔H with v↔w, E1↔E2
  with al↔cl; order 864) maps the universe and every state set onto itself (not needed: no symmetry is used); (ii) **(3,4)
  positive control**: authors' literal 16-single (3,4) configuration w10x_w11n34m_real.json: 16/16 edges in st_34, 0 edge
  failures, 120 pairs, 0 pair-rule violations at true overlaps; (iii) second, naive implementation tr_indep.py (builds concrete
  21-sets on explicit points and runs a GENERIC lemma checker over the family {E1,E2,G,H,F[,F']} — every 5-pair of the family,
  every subfamily for L — sharing no rule code with tr_core): per-edge, the whole o-box of 3 sampled traces (5450 rejected
  states) are all rejected by the generic checker and every accepted state passes; 3 sampled conflict pairs confirmed.
  Larger sample (100 traces / 100 conflict pairs / 100 non-conflict pairs) running (indep33.log).
- 13:45 EDT global elimination (tr_gac.py, RUP rule as in w14): 1561 + 96 traces eliminated, fixpoint with 9017 alive, no
  wipeout (so Φ_33 is not refuted by propagation alone; the refutation needs search). Random sub-formulas (COV + 30% / 15% of
  CONF) are SAT — the UNSAT needs the dense conflict graph.
- ~14:00 EDT sandbox reset killed the first drat-trim run of phi33 after ≈ 16 CPU-min (CPU 0 shared 3–4 ways). 14:03 EDT drat-trim
  relaunched alone on CPU 0 (tr/waiter.sh; all my other jobs on hold: ctrl33k.hold, cube33L.hold, tr/pipeline.hold).
- 14:30 EDT **case-split certificate (tr_case.py, run_case.sh) as a hedge against the slow full drat-trim.** Root: B* = the needed
  core 4-set with fewest avoiders = **{v, al0, al1, al2}** (24 avoiding traces — the trace-level shadow of the authors' J31).
  Stab(B*) in the base group (m/al/cl permutations, order 216) has **8 orbits** on these 24 (asserted: union = all 24).
  WLOG step (semantic, as in w14 referee item 3): a counterexample has a non-base edge avoiding B*, with trace t = g(r) for an
  orbit representative r; g⁻¹ applied to the whole configuration fixes the base family and gives an edge with trace r. So
  Φ_33 is refuted once Φ_33 ∧ x_r is refuted for the 8 representatives. Per case: propagate x_r (neighbours false), positive units
  (a COV with one live literal) and the RUP elimination rule; the case CNF is a SUBSET of Φ_33 (all 1325 COV + only the binary CONF
  clauses used by the justifications, + CONF among still-alive traces when no wipeout) plus the unit x_r; DRAT = derived units
  (each RUP) then the empty clause, or kissat's text proof of (case CNF + units).
  * cases 0, 1, 2 (r = traces #2531, #2538, #2818): **wipeout by propagation** (5212 / 4318 / 3105 derived units; case CNFs with
    46 710 / 70 055 / 68 982 CONF): drat-trim **`s VERIFIED`** (≈0.2 s each, 0 RAT).
  * case 3 (r = #2827): no wipeout (5804 alive); case CNF 2 393 850 CONF; Kissat `s UNSATISFIABLE`; drat-trim running.
- **14:47 EDT MAIN RESULT: Φ_33 is refuted by 8 case certificates, all drat-trim `s VERIFIED`** (tr_tree.py / run_tree.sh, log
  tr/tree.log). Same root step as the hedge above (B* = {v,al0,al1,al2}, 8 Stab(B*)-orbit representatives r); per case a
  propagation + branching refutation emitted directly as DRAT (no SAT solver): at a node with cube c, every derived literal u
  (positive unit from a COV with one live literal; ¬s for conflict neighbours of true traces; RUP elimination) is the lemma
  (u ∨ ¬c); a node is closed by (¬c), RUP from its children's closing lemmas + the branching COV(B) (child i = c ∪ {t_i, ¬t_1..¬t_{i−1}}
  over the live avoiders of the unsatisfied needed B with fewest live avoiders), or, at a leaf, from the emptied COV.
  | case | r (trace #) | tree nodes / leaves / depth | lemmas | CONF clauses in case CNF | drat-trim |
  |---|---|---|---|---|---|
  | 0 | 2531 | 1 / 1 / 0 | 5 213 | 218 410 | `s VERIFIED` 0.5 s |
  | 1 | 2538 | 1 / 1 / 0 | 4 319 | 185 177 | `s VERIFIED` 0.4 s |
  | 2 | 2818 | 1 / 1 / 0 | 3 106 | 96 381 | `s VERIFIED` 0.3 s |
  | 3 | 2827 | 10 / 9 / 1 | 26 953 | 823 591 | `s VERIFIED` 1.5 s |
  | 4 | 4075 | 4 / 3 / 1 | 13 350 | 718 431 | `s VERIFIED` 1.2 s |
  | 5 | 5525 | 1 / 1 / 0 | 5 161 | 171 920 | `s VERIFIED` 0.4 s |
  | 6 | 5532 | 1 / 1 / 0 | 6 859 | 293 820 | `s VERIFIED` 0.6 s |
  | 7 | 5691 | 1 / 1 / 0 | 6 584 | 234 384 | `s VERIFIED` 0.5 s |
  All 0 RAT lemmas. **Certificate-to-Φ check (tr_certcheck.py, certcheck33.log): in every case CNF the positive clauses are exactly
  the 1325 COV(B) (avoider lists recomputed from the universe, all present) plus the single unit x_r of that case's representative;
  every binary clause is a CONF pair of the full matrix; no other clauses.** Root step re-asserted there: B* is a needed 4-set,
  |Stab(B*)| = 216, the 8 orbits cover all 24 avoiders of B*.
  Logical chain: (1) an N-noK4 counterexample with a (3,3) 5-pair gives a model of Φ_33 (§5.1, PROVED); (2) COV(B*) ∈ Φ_33 gives a
  non-base edge with trace t avoiding B*, t = g(r) (orbit cover, checked); (3) g⁻¹ fixes the labelled base family (each generator
  checked to map P_q's core part onto P_{π(q)}'s and |O_q| = |O_{π(q)}|), so the relabelled counterexample has an edge of trace r;
  (4) Φ_33 ∧ x_r is UNSAT (VERIFIED). Hence **no N-noK4 counterexample has a 5-pair of class (3,3).**
  The universe was re-enumerated with the final tr_core.py: identical (st33_recheck.log). The unsplit Φ_33 (Kissat UNSAT) still
  lacks a finished drat-trim (two runs of 16 and 36 CPU-min were killed by resets); it is queued last and is no longer needed.
- 14:55 EDT naive second implementation on the clauses the certificates actually use: the 8 tree CNFs contain 1 803 882 distinct
  CONF clauses (pairs_33tree.npy); **200 random ones re-checked by tr_indep.py (concrete sets + generic lemma checker over the
  whole family, all state pairs × all integer overlaps): 200/200 confirmed conflicts, 0 disagreements**; per-edge: 200 sampled
  universe traces, all their states pass the generic checker, 19 random non-universe states all fail (indep33tree.log; the
  "non-conflict" line of that log is a skipped step). A 1000-clause sample is running (indep33tree1000.log).
- 15:25 EDT further checks on the (3,3) certificate:
  * **1000** random CONF clauses of the 8 case CNFs re-checked by the naive generic checker: 1000/1000 confirmed (indep33tree1000.log).
    Full-matrix samples (indep33.log, indep33nc.log): per-edge, the complete o-box of 150 sampled traces (375 976 rejected
    states) is rejected by the generic checker and every accepted state passes; 150 conflict pairs confirmed; **100 random
    NON-conflict pairs all found compatible by the generic checker** (so tr_core is neither stricter nor looser on the sample).
  * Realization control: the 15 distinct traces of the N24-respecting literal configuration violate **0** of the 9.65 M CONF clauses.
  * drat-trim cores of the 8 cases (tree_33_K.core): union = **136 987 CONF clauses** (+ 536 COV/unit clause occurrences).
    Dependency of these core clauses (tr_drop.py, depcore33.log; clauses that stop being conflicts when one pair-rule family is
    dropped): A 4 491, F1 0, L (≥2 base edges + F,F') 7 539, SAME (base 5-pair, SA+CLS) 570, D1 at (P_k,F) 644, single-rules at
    (P_k,F) (R3/SA/CLS with a base single) 8 830, rules at the derived 5-pair (F,F') 1 961, **CLS (W7-I/NK/N24) inside pair rules
    9 932**. So the certificate uses the N-noK4-specific facts (NK, N24) at derived 5-pairs, not only through the per-edge universe.
  * Lemma-side necessity controls (Φ without NK, universe 12 492 traces / 15.84 M CONF; Φ without N24): Kissat with proof
    logging timed out (1100 s, UNKNOWN); re-queued without proof logging (solve_np.sh, 1500 s) at the end of tr/pipeline.sh.
    These are necessity controls only; they have no bearing on soundness.
- **15:25 EDT BONUS (3,4)/(4,3): Φ_34 refuted, 5 case certificates all `s VERIFIED`** (same code; flags: N24 on, N34 off, nothing
  about (3,3) used). Universe st_34: 6 553 traces / 21 952 states (core 14 points); full matrix (cf_34); positive control: the
  authors' literal (3,4) 16-single configuration passes (above). Root B* = {v,al0,al1,al2} (20 avoiders), |Stab(B*)| = 864,
  5 orbits; cases: 4 wipeouts at the root + 1 tree of 4 nodes; case CNFs 22 904–200 960 CONF; drat-trim `s VERIFIED`, 0 RAT
  (tree_34.log). certcheck34.log: every case CNF = the 985 COV (complete, exact) + unit x_r + CONF pairs of Φ_34 only; orbit
  cover asserted. (4,3) is (3,4) with E1↔E2 swapped (§1). This independently re-proves the W11 (3,4) closure, consistent with §3a.

## §5 final (2026-10-16 15:35 EDT)
- (2,4) re-proved WITHOUT N24 via independent trace encoding: 7 cases, all drat-trim s VERIFIED, certcheck clean (tr/tree_24x.log, tr/certcheck24x.log).
- Old-encoding nonk control never completed (lost to resets; ctrl33k.hold restored). New-encoding no-NK / no-N24 necessity controls undecided; they bear on necessity only, not soundness.
- FINAL VERDICT: N-noK4 (3,3) SOUND (independent trace encoding, 8 verified cases); (3,4)/(4,3) SOUND; (2,4) SOUND.
