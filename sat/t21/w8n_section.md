
## Wave 8 N-noK4 (2026-10-15, started ~09:20 EDT)
**Result: N-noK4 is NOT closed.** What follows: an exact reformulation, four new proved lemmas, and computer
results that are all FEASIBLE (no contradiction). Since no UNSAT claim was reached, there is **no DRAT certificate in
this wave** (and so no controls for one). Notation as in §1 and N.0–N.4.

### N8.0 Reformulation (PROVED)
**NK:** for every 5-pair (X,Y), any two singles of different types meet in ≥ 6 points.
**Claim: N-noK4 ⟺ NK + some 5-pair is non-uniform.** (⇐) By R.3, cross-type singles Z,Z' of (X,Y) have outside parts
that do not meet, so |Z∩Z'| = a+c. NK gives a+c ≥ 6, and a Lemma-T witness W is a cross-type single of (E1,G) against
the type-v single E2, so k+c' ≥ 6. (⇒) A pair of cross-type singles with |Z∩Z'| = 5 is, with X,Y, a (3,2,1,1)-K4 when
(a,c) ∈ {(2,3),(3,2)}, and a triangle when a=1 or c=1 (W7-I rules triangles out). So the N-noK4 hypotheses are NK
restricted to (E1,E2) and (E1,G). But N.4's branch is "no K4 anywhere", and that is NK at every 5-pair. NK also implies NT.
Under NK the cross-type classes are (a,c) ∈ {(2,4),(4,2),(3,3),(3,4),(4,3),(4,4)}. If every cross-type pair is (4,4), the 5-pair is uniform
(same-type parts agree through a third type), so with W6-U a counterexample in N-noK4 has a 5-pair with a class in
{(2,4),(3,3),(3,4)} (up to swapping E1, E2).

### N8.1 Lemma TU (triple unions; PROVED, every (a,c))
For cross-type singles G (type v) and H (type w) at (E1,E2), put α = A_G∩A_H and γ = C_G∩C_H. Then E1∩G∩H = α,
|E1∪G∪H| = 63−10−(a+c)+a = **53−c**, E2∩G∩H = γ, and |E2∪G∪H| = **53−a**. By L, an edge X with X∩γ = ∅ has
|X∩(E2∪G∪H)| ≤ 21−(61−(53−a)) = 13−a, and symmetrically an edge with X∩α = ∅ has |X∩(E1∪G∪H)| ≤ 13−c.

### N8.2 Lemma ZF (PROVED) and its corollary for "C-uniform" pairs
**ZF.** If c = 4 (C_G = C_H =: C*), then every edge X avoiding C* contains v, w and α, and |X∩E2| = |X∩G| = |X∩H| = 5.
(This is the §6.5 hand fact, re-proved for every a. Inclusion–exclusion gives |X∩(E2∪G∪H)| = Σ|X∩·| − [v∈X] − [w∈X] − |X∩α| ≥ 15−2−a,
and TU gives ≤ 13−a, so every inequality is tight.) Consequently X is a type-v single of (E2,G) and a type-w single of (E2,H).
(E2,X) is a 5-pair (X∩E2 ∋ v,w) in which G and H are cross-type singles of class **(4,a)**: the class is transposed.
**Corollary ZF-T*.** Let T*(C*) be the set of types y that have a single with C-part C*. Every edge avoiding C*
contains T*(C*) and every A_y∩A_z for cross-type C*-singles. **If the 5-pair is C-uniform** (every single has C-part
C*, which is exactly what the solver produces, see N8.5), then every C*-avoider X contains M and has X∩E2 = M. So (E2,X)
is a 5-pair with the same intersection M, and it has the same singles as (E1,E2), with parts (C*, X∩(A_F∪O_F)).
Hand counts in this configuration: {Z,F_y,F_z,F_u} with A_y∩A_z∩A_u = ∅ has union exactly 61 (Z a C*-avoider), and
{Z,Y,F_y,F_z} (Y an A_0-avoider, when A_0 is a shared A-part) is only bounded by ≤ 61. So no unit of loss shows up locally.

### N8.3 P-inequalities (PROVED; CP' = W7-5 at the 49-triple (E1,E2,F))
For a single F of type y and an edge Z ∌ y (Z ∉ {E1,E2,F}):
 |Z∩(A∖A_F)| ≤ |Z∩C_F| − 1,  |Z∩(C∖C_F)| ≤ |Z∩A_F| − 1,  |Z∩O_F| ≤ |Z∩(M∖y)| − 1.
(Each is CP' with apex E1, E2 or F respectively. Lemma S(b), a+c ≥ 5, is the case where Z is a single.)

### N8.4 Witness lemmas (PROVED)
**(W-c4)** Let c = 4, a ≤ 3, p ∈ A_G∖A_H, and W a Lemma-T witness of (E1,G) at p, with k = |W∩M|, c' = |W∩C_G| and
A'_W = W∩(A∖A_G) (|A'_W| = 4−k). Then W∩α = ∅, so TU gives |W∩(E1∪G∪H)| ≤ 9, hence W∩O_H = ∅ and
[w∈W] + |A'_W∩A_H| + c' ≥ 5 (Lemma A against H). If w ∉ W, then k ≤ 3, and k = 3 ⟹ c' = 4 and A'_W ⊂ A_H, while
k = 2 ⟹ c' = 4 and |A'_W∩A_H| ≥ 1.
**(W'-Cu)** In a C-uniform 5-pair, let W' be an edge avoiding (C*∖{c})∪{y} (τ ≥ 5), D := M∖W' (so y ∈ D) and m1 := |W'∩M|.
Then W'∩C* = {c}, and W' is a type-c single of (E2,F_z) for every z ∈ D. R.3, Lemma T (E1 is a type-z single there) and
NK give: |W'∩(C∖C*)| = 4−m1, W'∩A ⊆ ∩_{z∈D} A_z, and m1 + |W'∩A_z| ≥ 6 for all z ∈ D. Hence m1 ≥ 2 and |D| ≤ 3.

### N8.5 Computation (all FEASIBLE; sound relaxations, so they show only that these local arguments cannot close the branch)
Model work/e616/t21/w8n_model.py (CP-SAT). Points: M, A, C, and O_0..O_4 named (97 points). Edges: E1, E2, and five
singles F_y with variable parts and fixed disjoint outsides (pair (F0,F1) forced to the class). Optional: the Lemma-T
witnesses of F0 (A- and C-side, 8 edges), the witnesses of F1, and τ-edges J_B avoiding chosen 4-sets B. Every other edge
has a "rest" outside the model. Constraints: Lemma A with rest overlaps; L on every ≤4-family that contains an edge with
no rest, with the Hunter (spanning-tree) upper bound on the union; NK, fully reified, on the 5-pairs (E1,E2), (E1,F_y),
(E2,F_y) and optionally the witness pairs.
* 5 singles + 8 witnesses of G, classes (2,4) and (3,3): **FEASIBLE** (12–15 s). Typical solution: one deviant type, the other
  four types uniform with G, and all of G's witnesses uniform with E2 (k = 4, c' = 4).
* singles only, NK, all ≤5-families: three or more distinct (A,C) parts are possible in each of (2,4), (3,3), (3,4)
  (w8n_singles.py). So there is no "at most one deviant type" lemma at this level.
* + witnesses of F1 (16 witnesses): UNKNOWN (90 s per CEGAR iteration on a CPU shared with other jobs; w8n_lazy.py,
  w8n_lazy_24.log). Not a result.
* **Explicit local configuration (verified independently).** Class (2,4), 5 singles + J avoiding {v,w}∪α, C*, A_0 and
  {v,w,c1,c2}: realised as an explicit 11-edge partial hypergraph (fresh points for rests): work/e616/t21/w8n_realized_24J.json.
  It was checked by w8n_realize.py with plain set arithmetic: all sizes are 21, pairwise intersections ≥ 5, **L holds for every one of the 2^11
  subfamilies, and NK holds at every 5-pair inside the family**. Non-uniform classes (2,4), (3,4) and (4,3) occur at 8 different 5-pairs, among
  them (E2,J_{C*}), which shows the transposition of ZF. Log: w8n_real24J.keep.log. C*-avoider: M ∪ {a0,a1,a2,a4}, with
  no C points, as ZF-T* predicts.
* A 17-edge realisation (+ 8 witnesses of G) was still solving at write-up (w8n_real24.log).
**Checks against the examples** (w8n_check_examples.py, 150 K-pairs each): `r=16 K=4: NK holds=True, ZF instances=900
failures=0`; `r=22 K=5: NK holds=True, ZF instances=1500 failures=0`. Both examples are uniform, so ZF holds there
trivially. ZF's derivation is tight at r=16 and has one unit of slack at r=22.

### N8.6 Status and assessment
N-noK4 is **OPEN**. Why the local approaches fail: every 4-family that the lemmas produce sits at exactly 61 (EHT tightness),
and NK only removes the 5-intersections that W7/K4 used. Locally, non-uniformity looks like one or a few types with a
deviant part, and this is realisable (N8.5). The one-sided trace obstruction (N.2) is not removed by CP' either: on the 10-point
126-set system, σ∖(τ∪τ1) has ≤ 1 point, so CP' is vacuous there.
The most promising targets:
(1) **C-uniform subcase** (every single at (E1,E2) has the same C-part; every class-(2,4) solver solution seen had this form,
but singles-only models show it is not forced). By ZF-T*, all C*-avoiders X give 5-pairs (E2,X) with the same intersection M and transposed classes. A proof would have to
show that the resulting family of "M-partners" {E1} ∪ {X} forces a W6-U-type 4-family with union 60.
(2) **Propagation lemma (P):** under NK, (X,Y) uniform ⟹ (X,F) uniform for every single F. Together with one uniform 5-pair this
would give a contradiction via W6-U, because W6-U only uses pairs reached by propagation G. (P) is not implied by uniformity of
(X,Y): the singles of (X,F) are multis of (X,Y).
Scripts: w8n_model.py, w8n_lazy.py, w8n_J.py, w8n_realize.py, w8n_singles.py, w8n_check_examples.py (all in work/e616/t21/).
