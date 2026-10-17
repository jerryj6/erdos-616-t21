> **Internal working note.** This file is a raw report written while the proof was being developed and checked. It is kept for provenance. Run names and timings refer to the original working environment. The curated statements are in `paper/` and `README.md`.

> **Paths.** File paths in this report have been rewritten to their location in this repository wherever the file is
> included (`lean/`, `sat/`, `docs/`, `data/`). Paths still beginning with `work/`, `candidates/` or `/tmp/` name exploratory
> scripts, build directories or logs from the original working environment that are not part of the proof and were not
> published; nothing the final theorem or the certificate checks depends on is among them.

# Independent referee: Wave 14 global encoding (refutation of N-K4, Erdős #616 r=21)
Started 2026-10-16 12:20 EDT. Adversarial referee; own code in sat/t21/w14ref/ (imports nothing from w13_/w14_ scripts).
**VERDICT (12:52 EDT): G14 is SOUND. No gap found in items (1)–(5).** The N-K4 (3,2,1,1) branch is refuted by Φ, provided the
lemmas it rests on (§1 Lemma A/R/S, D1, W7-I) are sound; those were already refereed SOUND (docs/referee/t21-referee.md).
Out of scope here (must be refereed separately before claiming t(21)=4): N.4's dichotomy N-K4 / N-noK4 and the W11 N-noK4 closure.

## Summary per item
| item | verdict | basis |
|---|---|---|
| (1a) G14.1 relaxation: universe of traces / states | SOUND | each per-edge rule re-derived (below); my full-box enumeration gives the same 18 217 traces / 49 967 states |
| (1b) COV | SOUND | B core 4-set meeting all P_q ⇒ avoider (τ≥5) is non-base and its trace avoids B; clauses = exact avoider lists |
| (1c) CONF, every family | SOUND | A, F1, SAME, L (2/3/4 base), D1-derived re-derived; every binary clause of all 6 CNFs re-checked; authors' full 37.57 M graph ⊆ my independent graph |
| (1d) same trace / several edges per trace | SOUND (no issue) | x_t only asserts existence; CONF only for t≠t'; no self-clauses in any CNF; traces equal to a base trace never avoid a needed B |
| (2) symmetry, 19→5 reps, 51 dead | SOUND | own 288-group; 70 avoiders of B* = 51 dead ⊔ orbits of the 5 units; certdead verified |
| (3) own encoder + UNSAT | SOUND | own states, own conflict checker, own COV; own kissat proofs for 15116, 17917 → drat-trim VERIFIED |
| (4) pending re-checks/controls | DONE | 16054/17917 core re-checks done (authors 0 disagreements; mine: all clauses, 0); F1/L3 controls settled by dependency (unused) |
| (5) 12 realizations | SOUND | literal L-check + my states/pairs + no CNF clause violated |


## Milestone log (EDT)
- 12:40 Read G14.1–G14.4, N.0, NK4, S13.1, w13_enum/w14_compat/w14_indep (statements only). SHA-256 of all 10 case CNF/DRAT files
  match w14_cert2.sha256. Referee drat-trim re-runs (work/e616/tools/drat-trim, own core output w14ref/drat_<case>.core):
  15116, 17917, 14968, 15954 `s VERIFIED`; 16054, certdead running.
- Authors' queue: run_indep_all finished (w14_indep_all.DONE): 16054 1 952 309/1 952 309 and 17917 353 380/353 380 core CONF
  clauses re-checked, 0 disagreements (their logs). Controls: drop A, drop OO → SAT (recorded); drop SAME, drop D1d → TIMEOUT
  (1200 s, undecided); F1, L3 in progress when the box reset.
- 12:44 (after a box reset 12:28) Referee's own code, sat/t21/w14ref/ (imports nothing from w13_/w14_; reads the authors'
  files only as DATA: CNF/DRAT, var→trace table w14_conf.npz['T'], realization JSONs):
  * ref_states.py: per-edge rules re-implemented from S13.1's lemma list, enumerated over the FULL integer box
    0 ≤ o_q ≤ |O_q|, |b|+Σo ≤ 21 (no {L,L+1} shortcut): **18 217 traces, 49 967 states — identical to w13_feas.json /
    w14_states.json** (ref_universe.py; T == sorted(w13_feas)).
  * pairref.py (numba): literal pairwise rules A, F1, SAME (S(a)+W7-I+S(b)), L on EVERY ≥2-subset of base edges (incl. all four),
    D1 at derived pairs, exhaustive integer z_0..z_3, z_U. **Every binary clause of every certificate CNF (not only cores) is a
    genuine conflict: 15116 666 928/666 928, 17917 757 818, 14968 1 022 918, 15954 3 895 171, 16054 4 179 298, certdead
    593 077 — 0 disagreements, 0 self-pairs.** Sensitivity control (ref_density.py): 20 000 random trace pairs, my conflict
    density 0.2203 vs authors' matrix 0.22025; authors-conflict-but-mine-compatible = 0 (1 pair the other way: mine is stricter
    because it enumerates z exactly and also uses L on all four base edges).
  * ref_cov.py: in all 6 CNFs the non-binary clauses are exactly the 1730 COV(B) (B = core 4-set meeting all P_q; 1730 of 1820,
    recomputed), each EQUAL to my avoider list, + the unit x_r (case CNFs) or the 51-literal dead-avoider clause (certdead, all
    literals avoid B*). No other clauses.
  * ref_orbit.py: own group H (permutations inside α, γ, m3, a3, a4; |H| = 288; each fixes every P_q setwise); B* = {w,g0,g1,g2}
    is H-invariant; the 5 units are vars 15117, 14969, 15955, 16055, 17918 (= index+1 of the named reps), all avoid B*;
    **avoiders of B* = 70 = 51 dead (certdead clause) ⊔ 19 = H-orbits of the 5 reps; uncovered 0.**
  * drat-trim re-run by me on all 6 (CNF, DRAT): all `s VERIFIED`. kissat (own run, own DRAT) on 15116: `s UNSATISFIABLE`.
  * ref_real.py: the 12 realizations re-verified LITERALLY (21-uniform, base labelling exact, property L on all 2^m
    subfamilies: 0 violations); 117 non-base edges all in my state set, 532 pairs all compatible under my checker, and no
    binary clause of any certificate CNF is violated by a realization.
- 12:48 Dependency of MY drat-trim cores under MY checker (ref_dep.py; core CONF clauses that stop being conflicts when one
  family is dropped):
  | case | core CONF | A | F1 | SAME | OO (L, 2 base) | L, 3 base | L, 4 base | D1d |
  |---|---|---|---|---|---|---|---|---|
  | 15116 | 283 537 | 128 435 | 0 | 48 | 83 937 | 0 | 0 | 78 |
  | 17917 | 353 380 | 162 125 | 0 | 0 | 96 690 | 0 | 0 | 1 315 |
  | 14968 | 494 409 | 240 186 | 0 | 40 | 133 236 | 0 | 0 | 5 492 |
  | 15954 | 1 705 470 | 1 121 730 | 0 | 374 | 607 706 | 0 | 0 | 54 076 |
  | 16054 | 1 952 309 | 1 320 304 | 0 | 695 | 698 099 | 0 | 0 | 55 751 |
  | certdead | 253 375 | 108 457 | 0 | 0 | 71 375 | 0 | 0 | 573 |
  **Consequence (completes the F1 and L3 controls in the strongest form): the whole certificate stays valid with pairwise F1
  and L on ≥3 base edges removed** (every core clause is still a conflict without them; COV and the DRAT are unchanged).
  The pairwise trust base is just Lemma A, OO (= L on {P_k,P_l,F,F'}), D1 at derived 5-pairs, and SAME (S(a)+W7-I+S(b)) in 4 of
  6 pieces. (Authors' w14_dep counted F1 60 / SAME 148 because their bound-based compat needs F1-forced z lower bounds; my
  exact z enumeration recovers those conflicts from A/OO.) Drop-SAME and drop-D1d "is Φ then SAT?" controls (authors' lazy loop,
  1200 s) remain TIMEOUT/undecided; they are necessity controls only and have no bearing on soundness — not pursued.
- 12:50 Full independent conflict graph (ref_fullconf.py, all 18 217² ordered pairs, no transport): mine 37 588 274 unordered
  conflicts, symmetric, empty diagonal; **authors' w14_conf.npz (37 569 536) ⊆ mine: theirs-but-not-mine = 0**; 18 738 extra
  conflicts are mine only (exact z / L on 4 base edges). So the group transport in w14_conf is also sound.
- 12:51 Own kissat runs (own DRAT, not the authors' proofs): 15116 `s UNSATISFIABLE` → drat-trim `s VERIFIED` (200 s);
  17917 `s UNSATISFIABLE` → drat-trim `s VERIFIED` (307 s). 14968 running (run_kissat.sh, resumable).

## Re-derivations (the points an adversary would push on)
* **Per-edge rules (S13.1 list).** F1/R.1 (every N_ij is a transversal); Lemma A on each P_q; CAP; L3 = L on {P_i,P_j,P_k,X} when
  X∩T_ijk=∅ (|P_i∪P_j∪P_k| = 48+|T|); D1 at the six base pairs; W7-I at base pairs (A-part intersection = X∩P_k∩P_i∖N_ij, core
  only); derived pair (P_i,X) with |X∩P_i|=5 and N=X∩P_i (contains o_i O_i-points): R.3 for a base single P_j (|P_j∩N|=1 ⇒
  |P_j∩X|=5), D1 (N⊄P_j ⇔ o_i>0 or core part ⊄ P_j; |P_j∩(P_i∪X)| = 5+|b∩P_j∖P_i|+o_j), W7-I (a = |T_ijk∖b|, c = |b∩P_j∩P_k∖P_i|;
  only a,c ≠ 1 is used — weaker than S(a)'s a,c ≥ 1, still sound), S(a) (P_j∩P_k∖(P_i∪X) = ∅). Single-edge L on {P_i,P_j,X}
  is F1, and on all four base edges is vacuous (61+u ≥ 61). Nothing else is assumed (no uniformity, no Case N-noK4 facts).
* **Pairwise rules.** A; F1 ({P_q,F,F'}); SAME for cross-type singles of one base pair (S(a): no common point outside P_i∪P_j,
  i.e. core, O_q (q≠i,j) and U; W7-I: a,c ≥ 2; S(b)); L on {X ∪ F,F'} for every set X of ≥2 base edges with ∩X∩F∩F' = ∅
  (∩X ⊆ core, exact union count); D1 at the derived 5-pair (P_k,F) unless F∩P_k ⊆ F' (core part ⊆ b' and z_k = o_k).
  Overlaps: z_q ∈ [max(0,o_q+o'_q−|O_q|), min], z_U ∈ [0, min(u,u')] (U has no size bound, so no lower bound) — this is the
  complete set of integer possibilities; "conflict" = no state pair and no z satisfies all rules.
* **G14.1 logic.** x_t := ∃ non-base edge with core trace t. COV(B) for a core 4-set B meeting every P_q: τ ≥ 5 gives an edge
  avoiding B, not a base edge, with trace in the universe and avoiding B. CONF(t,t'), t≠t': two such edges are distinct, so some
  state pair and the true overlaps satisfy every rule — contradiction with "no compatible state pair". Several edges per trace
  or a trace equal to a base trace cause no issue (no clause relates a trace to itself; base traces never avoid a needed B).
* **Symmetry.** H (288 core permutations inside α, γ, m3, a3, a4, identity elsewhere) fixes every P_q setwise, so g⁻¹(G) is again
  a counterexample on the same labelled base; it has an edge of trace r. Only invariance of the hypothesis is used, not of any
  computed matrix. σ (P2↔P3) is not needed for the root step (it moves w to v, so it is not in Stab(B*)).

## Files (referee; all in sat/t21/w14ref/)
ref_states.py (+ ref_states_*.json chunks, ref_universe.py → ref_states.npz, ref_feas.json), pairref.py (numba; pairref.c is the
same algorithm in C, unused: no compiler on the box), ref_cov.py, ref_orbit.py, ref_real.py, ref_density.py, ref_dep.py,
ref_fullconf.py (+ fc_*.npz, fc.log), logs pair_*.log, cov_*.log, dep_*.log, drat_*.log/.core, ks_*.log. Restart scripts:
run_states.sh, run_pair.sh, run_cov.sh, run_dep.sh, run_drat.sh, run_kissat.sh, run_fc.sh (all resumable). PYTHONPATH=w14ref/pylib (numba).

## Minor remarks (not gaps)
* G14.4 says L3' is in the trust base; it is not needed at all (table above). Same for pairwise F1.
* w13_enum's W7d uses only a,c ≠ 1 at derived pairs and the W7b/NT rules never use S(b); stronger sound rules exist but adding
  them would only shrink the universe, so the certificate does not depend on omitting them.
* The authors' clause re-check w14_indep.py reads the state lists from w14_states.json; my pairref uses my own regenerated states,
  so clause soundness no longer depends on either single implementation.
