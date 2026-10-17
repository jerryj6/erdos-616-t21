
## Wave 8 N-K4 (2026-10-15, started ~09:15 EDT)
**Result: N-K4 is NOT closed.** I found no contradiction, so this wave has **no UNSAT claim, no DRAT certificate and no
controls** (controls only make sense for an UNSAT model). Below: two new proved lemmas (each checked exhaustively), a
completeness remark on (2,2,2,1), a new sound point-level CNF model, and computed results that are all SAT.
Notation of N.0 (iii): P0=E1, P1=E2, P2=G, P3=H; v=T012, w=T013, α=T023 (2), γ=T123 (3), m3=p01 (3), a3=p02 (2),
a4=p03 (2), c3=p12, c4=p13; O_i = private part of P_i (10, 11, 12, 12 points); U = points outside P0∪…∪P3.

### NK4.0 Which K4 patterns the branch actually has to kill (PROVED, a remark)
N.4 defines the split as N-K4 := "some **(3,2,1,1)**-K4 exists" and N-noK4 := "no witness meets the other edge in 5".
A (2,2,2,1)-K4 is not produced by N.4. Its 1-point triple, say P1∩P2∩P3 = {z}, makes P3 a type-z single of (P1,P2), and
likewise P2 of (P1,P3) and P1 of (P2,P3). P0 is a multi (k=2) of every base pair. No two cross-type singles of one base
pair lie in the K4, so the K4 does not by itself give a 5-pair with a+c = 5. **So the case split stays complete with
N-K4 = (3,2,1,1) only. (2,2,2,1) is extra.** I modelled it anyway (NK4.4). Σ-triples ≥ 8 K4s (Σt ≤ 10 is the only upper
bound) are allowed by N.0(i)'s inequality. They are not needed for the split either.

### NK4.1 Lemma VW (PROVED; checked)
In a (3,2,1,1)-K4, every edge Z with v, w ∉ Z satisfies, with m=|Z∩m3|, o_k=|Z∩O_k|, al=|Z∩α|, ga=|Z∩γ|:
  (i) m ≥ 1 + max(o2, o3), so **every edge avoiding v and w meets m3**;  (ii) al + ga ≥ m + 1 + o0 + o1 − min(o2, o3).
*Proof.* Put X := |Z∩P0| ≥ 5 and Y := |Z∩(γ∪c3∪c4∪O1)|. L3 for T012 = {v} (N.0(ii): |Z∩(P0∪P1∪P2)| ≤ 9) reads
X + Y + o2 ≤ 9, and L3 for T013 gives X + Y + o3 ≤ 9. Lemma A for P1 is m + Y ≥ 5. Together these give (i). Adding Lemma A
for P2 and P3: 2al + 2ga + |Z∩(a3∪a4)| + |Z∩(c3∪c4)| + o2 + o3 ≥ 10. Subtract X + Y ≤ 9 − max(o2,o3) to get (ii). ∎
Check: w8lemmaVW.py (region-count CP-SAT, searches for a violation of (i) resp. (ii) under exactly these constraints):
INFEASIBLE / INFEASIBLE.

### NK4.2 Lemma G (PROVED; checked)
Let F be a (P2,P3)-single of type y ∈ γ. If v ∉ F, then F ⊇ {w} ∪ a3 ∪ c3, |F∩a4| = 1, |F∩m3| = 1, F∩O0 = ∅, |F∩O2| = 1
and |F∩(c4∪O1)| = 1. The statement with v↔w, a3↔a4, c3↔c4, O2↔O3 also holds.
*Proof.* Write a3', a4', c3', c4', m, o_k for the intersection sizes. A_F = F∩(P2∖N23) ⊂ {v}∪a3∪c3∪O2 has 4 points, so
a3' + c3' + o2 = 4. N.1 (= L3 for T023 = α, which F avoids) gives [w] + a3' + a4' ≥ 4 and m + o0 ≤ 1. L3 for T012 = {v}:
5 + [w] + m + a4' + o0 + c4' + o1 ≤ 9. Lemma A for P0: a3' + [w] + m + a4' + o0 ≥ 5, so a3' ≥ 1 + c4' + o1. Lemma A for P1:
[w] + m + 1 + c3' + c4' + o1 ≥ 5, so c3' ≥ a4' + o0. If c3' = 0, then a4' = 0 and [w] + a3' ≤ 3 < 4, a contradiction. So
c3' = 1, a4' + o0 ≤ 1, and [w] + a3' + a4' ≥ 4 forces w ∈ F, a3' = 2, a4' = 1, o0 = 0, o2 = 1. Then Lemma A for P0 gives
m ≥ 1, so m = 1, and the two remaining inequalities give c4' + o1 = 1. ∎
Check: w8lemmaG.py enumerates every core trace plus O-count vector allowed by Lemma A, F1 and L3 for this class: 72/72
instances satisfy the lemma.
(Consequence: two type-γ singles of (P2,P3) that avoid v have the same A-part on {v}∪a3∪c3 and different m3 points.)

### NK4.3 New model: point-level CNF with every point of P0∪…∪P3 named (work/e616/t21/w8sat.py)
The 16 core points and all 45 points of O0…O3 are named. Each new edge is a 0/1 vector over these 61 points. The
constraints are exactly the proved facts used so far, each kept in a form that stays TRUE when the U-part is ignored:
(S) singles: F∩N_ij = {x}, |F∩P_i| = |F∩P_j| = 5 (R.3), |F∩P_k| ≥ 5;
(F1) three edges share a point (base+base+new, base+new+new);
(D1); (L3) = N.0(ii); (L4) = OO (L on {P_k,P_l,F,G});
(NT) no triangle (W7-I) for same-pair cross-type singles;
(TT) no trace triangle on any P_i among base and new edges (W7-1 + W7-I).
Optional **(U)** adds unary lower-bound variables for |F∩G∩U| (1..5) with these sound rules:
- Lemma A for every new pair (|F∩G| ≥ 5);
- the U-overlaps enter L4;
- U-capacity: the U-parts of cross-type singles of one base pair are pairwise disjoint, so Σ_G |F∩G∩U| ≤ 21 − |F∩named|;
- F1 for every triple of new edges (a common named point, or a common U-point; the second is impossible inside one
  same-pair group).
Cardinalities use a truncated totalizer. Plain CaDiCaL (pysat) is used, so a DRAT proof would be available on UNSAT.
General-r forms of L3, OO/L4 and R.3, checked literally on the examples (w8K4_check_examples.py):
`r=16: L3 checks=5377 violations=0; OO/L4 checks=1428 violations=0; R3 checks=900 violations=0`;
`r=22: L3 checks=5481 violations=0; OO/L4 checks=789 violations=0; R3 checks=1500 violations=0`.
(The examples contain no K4 at all, see N.2, so Lemmas VW and G are vacuous there.)

### NK4.4 Computations: all SAT, so there is no contradiction at this level
All 24 first-generation witnesses of the (3,2,1,1)-K4 were used: the singles S^{ij}_x for every base pair and every
type not realised by a base edge (3+4+4+4+4+5).
* CP-SAT count model (w8k4.py; O_i and U as counts): FEASIBLE (132 s). Named O-points: FEASIBLE (106 s).
* CNF model, +TT: **SAT** (8 s solve; 3.38 M clauses).
* CNF model, +TT +U: **SAT** (396 s; 5.05 M clauses, 656 k vars).
* Apex-P0 subset (the analogue of the triangle proof's W^i_q and Y^{ab}_c sets, 18 edges): SAT.
* CEGAR adding τ-edges (w8cegar.py / w8cegar2.py): each round adds edges that avoid a core 4-set B which no further
  edge could avoid given the current solution. 3 + 3 rounds, up to 8 such edges (e.g. edges avoiding {v,w}∪α,
  {v,w,y,m}, {v,α_1,a3_1,a4_1}): SAT every round. Solve time grew 20 s → 438 s. Both runs were killed by sandbox
  restarts, so this is not a stall proof.
* (2,2,2,1)-K4, all 27 first-generation witnesses, +TT +U: **UNKNOWN**. Still running when this was written (background, timeout 2400 s from 14:43 EDT). The result will land in w8sat_2221_all_tt_U.log. Not a result.
* **Caution on the U-relaxed model.** Filling each edge of the +TT solution with fresh private U-points
  (w8realize.py, exact DFS over subfamilies) breaks L: 108 subfamilies with empty intersection and union ≤ 60, many of
  them three new edges with no common named point. So SAT of the relaxation does not show local consistency. It shows
  only that these constraints cannot close the case. The (U) option removes exactly that defect (triple F1, Lemma A,
  capacity) and is still SAT.

### NK4.5 Why the triangle machinery does not transfer (assessment)
In the triangle, CP' at (Q,P_i,W^i_q) left the Y's a slack of [c∈K_W] + [o_W∈Y] − 1. All the play sat in the four
points of C0 and in a single pinned private point o_W, and Lemma S(a) made that point usable by at most one Y. That
gave the finite trace system of 7.3/7.4. In the (3,2,1,1)-K4 the two 1-point triples (v and w) share the pair (P0,P1).
The analogous CP' bounds are all satisfied with equality by solutions that copy existing parts. The solver's typical
solution is "nearly uniform":
- the (P0,P1)-singles of types m3 take A = α∪a3 and C = γ∪c3 (the parts of P2), and P3 is the only deviant type;
- the (P0,P2)-singles are uniform with S = {v,w}∪m3∪α∪a3∪γ∪c3 (13 points);
- the new edges put their 11–12 remaining points into U.
So the obstruction, if any, is a W6-U-type closure around this 13-set with P3 as the single deviant. It is not a
first-generation counting argument. This is the same picture N8.6 reports for N-noK4 ("one deviant type").

### NK4.6 Status: N-K4 OPEN. No triangle-style finite contradiction exists among first-generation witnesses (SAT
even with the U-overlap rules). Suggested next targets:
(1) a "one-deviant" propagation lemma: in a (3,2,1,1)-K4, show that the 5-pairs reached from (P0,P2) by propagation G
are uniform, then run W6-U's closure on S. S is a 13-set, as in W6-U. P3 (P3∩S = {w}∪α∪γ, 6 points) is what the closure
must absorb.
(2) CEGAR on the +U model with second-generation singles (singles of (P_i,F) for first-generation F) instead of generic
τ-edges.
Scripts (work/e616/t21/): w8sat.py (CNF model), w8k4.py (CP-SAT count/named model), w8sub.py, w8enum.py (per-class
trace enumeration), w8cegar.py, w8cegar2.py, w8backbone.py, w8avoid.py, w8realize.py, w8lemmaG.py, w8lemmaVW.py,
w8K4_check_examples.py. Logs: w8k4_3211_full.log, w8k4_3211_named.log, w8sat_apex0_tt.log, w8sat_all_tt.log,
w8sat_all_tt_U.log, w8cegar_3211_all.log, w8cegar2_3211.log, w8realize_3211.log, w8sat_2221_all_tt_U.log.
pysat was missing from work/e616/pylib after a sandbox restart; I reinstalled it (python-sat 1.9.dev16).
