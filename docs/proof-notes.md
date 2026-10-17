> **Internal working note.** This file is a raw report written while the proof was being developed and checked. It is kept for provenance. Run names and timings refer to the original working environment. The curated statements are in `paper/` and `README.md`.

> **Paths.** File paths in this report have been rewritten to their location in this repository wherever the file is
> included (`lean/`, `sat/`, `docs/`, `data/`). Paths still beginning with `work/`, `candidates/` or `/tmp/` name exploratory
> scripts, build directories or logs from the original working environment that are not part of the proof and were not
> published; nothing the final theorem or the certificate checks depends on is among them.

# Erdős #616, r = 21: toward t(21) = 4. Working file (2026-10-14)
> Referee report (2026-10-15): docs/referee/t21-referee.md — §1, D1, W6-U, W7-I all SOUND; machine checks re-verified.

Wave 10 (end of file, "Wave 10 outside-H"): the non-uniform Lemma H is OO at derived pairs. Full outside-disjointness is FALSE in Case N (a witness and a single overlap in exactly 4−c points). New 3-way lemmas SQ and SF refute the W9 stall cores by hand. Case N is still OPEN.
Status: **OPEN.** t(21) ∈ {4,5} is not settled. **Wave 7 (2026-10-15): Case I (triangle) PROVED impossible (§7.4, hand proof + DRAT cross-check); only Case N remains.** Wave 6 (§6.3): the uniform case — which contains both known
example types — is PROVED impossible; t(21)=4 now ⟺ every 5-pair is uniform (§6.6). This file keeps what is PROVED, what is COMPUTED (with
certificate), and what is CONJECTURED, kept apart. The companion file is candidates/erdos-616-loop.md
(core reformulation, L1, L2, and the certified claim "core ≥ 15").

Setting: G is 21-uniform with property L = every subfamily of edges whose union has ≤ 60 vertices has a common
vertex, and τ(G) ≥ 5. We seek a contradiction. "Window" means 60 = 3r − 3.

## 0. Sources
* EHT91 = Erdős–Hajnal–Tuza, JCTA 58 (1991) 78–84. The PDF is still not fetched (Elsevier). I used the faithful
  transcription in the SciNet repo https://github.com/scinet-ai/math-number-theory, file
  erdos-616-landscape/proof_t8_t11.md §1 (commit 54b7272). It transcribes:
  - Thm 3: (3r−3,1) →_r ⌈r/5⌉.
  - Thm 6(I): (max{3r−3, p(r,t)}, 1) →_r t, where p(r,t,m) = ⌈m/t⌉(r−m−t) + 2r − m and p(r,t) = max_{1≤m≤r−1} p(r,t,m).
  - The repo notes that Thm 6(I) "splits on a minimum pairwise intersection".
* At r = 21, t = 4, p(21,4,m) for m = 1..20 is
  57 55 53 51 **61** 58 55 52 57 53 49 45 45 40 35 30 25 19 13 7.
  **Only m = 5 exceeds the window 60, and only by 1.** I reconstructed the argument in §1 and checked it independently.

## 1. PROVED: reduction to the "5-pair rigid" case (EHT argument, reconstructed and sharpened)

Facts used: (F1) G is intersecting and 3-wise intersecting. Three edges with no common vertex have union
≤ 63 − Σ|pairwise ∩| ≤ 60 (or are not pairwise intersecting, union ≤ 42). (F2) For every 4-set B there is an edge
disjoint from B (τ ≥ 5).

**Lemma A (min intersection is exactly 5).** Every two distinct edges meet in ≥ 5 vertices, and some pair meets
in exactly 5.
*Proof.* ≥ 5 is L1 (the pairwise intersection E∩E' is a transversal by F1, so it has size ≥ 5 by F2). Let m be the
minimum of |E1∩E2| and M = E1∩E2. Suppose m ≥ 6. Cover M by k = ⌈m/4⌉ four-subsets B_1..B_k (overlaps are
allowed). By F2 pick F_j disjoint from B_j. Then the family {E1, E2, F_1..F_k} has empty intersection (that
intersection lies inside M minus the union of the B_j). Also
|F_j ∩ (E1∪E2)| = |F_j∩E1| + |F_j∩E2| − |F_j∩M| ≥ 2m − (m−4) = m+4,
so |F_j \ (E1∪E2)| ≤ 17 − m and the union is at most 42 − m + ⌈m/4⌉(17 − m). The values for m = 6..17 are
58,55,52,57,53,49,45,45,40,35,30,25, all ≤ 60, and m ≥ 18 is impossible since it would need 17 − m ≥ 0. That
contradicts L. ∎

**Lemma R (rigidity at a 5-pair).** Let |E∩E'| = 5 and M = E∩E'. Then:
1. M is a transversal of G: every edge meets M. (If F∩M = ∅, then {E,E',F} has union ≤ 37 + 21 − 10 = 48.)
2. For every x ∈ M some edge F has F∩M = {x}. (Apply F2 to M\{x}, then use (1).)
3. If F∩M = {x}, F'∩M = {y} and x ≠ y, then |F∩E| = |F∩E'| = |F'∩E| = |F'∩E'| = 5, and the outside parts
   F\(E∪E') and F'\(E∪E') are disjoint, of size exactly 12 each.
*Proof of 3.* {E,E',F,F'} has empty intersection. Since |F∩(E∪E')| = |F∩E| + |F∩E'| − 1 ≥ 9, we get
|F\(E∪E')| ≤ 12, and the same for F'. So the union is ≤ 37 + 12 + 12 − |overlap of outside parts| ≤ 61. L forces
≥ 61, so every inequality is tight. ∎

**Corollary R1.** If F∩M = {x}, then (E,F) is again a 5-pair, so {x} ∪ (F∩E \ {x}) is a 5-transversal, and
the same holds for E'.

Notation for a fixed 5-pair: E1 = M ∪ A, E2 = M ∪ C, |A| = |C| = 16. An edge G with G∩M = {v} is
**single of type v**. Write A_G = G∩A, C_G = G∩C (both of size exactly 4 by R.3) and O_G = G \ (E1∪E2) (size 12).
An edge with |G∩M| = k ≥ 2 is **multi**.

**Lemma S (cross-type relations).** Let G be single of type v and H single of type w, with v ≠ w. Then:
* (a) A_G∩A_H ≠ ∅, C_G∩C_H ≠ ∅, and O_G∩O_H = ∅.
* (b) |A_G∩A_H| + |C_G∩C_H| ≥ 5.
* (c) |A_G∩A_H| = 1 ⟹ C_G = C_H, and |C_G∩C_H| = 1 ⟹ A_G = A_H.

*Proof.*
* (a) The first two follow from Cor R1, since {v}∪A_G is a transversal and v ∉ H. The third is R.3.
* (b) G∩H ⊆ A∪C, and Lemma A gives |G∩H| ≥ 5.
* (c) (E1,G) is a 5-pair with M' = {v} ∪ A_G. Then E2∩M' = {v} and H∩M' = A_G∩A_H = {p}, which are different
  points. By R.3 applied to (E1,G), the sets E2\(E1∪G) = C\C_G and H\(E1∪G) ⊇ C_H\C_G are disjoint. So
  C_H ⊆ C_G, and since both have size 4 they are equal. ∎

**Lemma K (multi edges).** Let K be an edge with K∩M = Q, |Q| = k ≥ 2. Then:
* |K∩A| ≥ 5 − k and |K∩C| ≥ 5 − k.
* If some x ∈ M \ Q exists, then for every single edge F of type x: K meets A_F and C_F, and
  |K∩A| + |K∩C| ≤ 9 − k − |K∩O_F|.

*Proof.* The first line is Lemma A applied to (K,E1) and (K,E2). For the second, the A_F and C_F part comes from
Cor R1. The {E1,E2,K,F} part: this family has empty intersection, its union is 37 + |K\(E1∪E2)| + 12 − |K∩O_F|,
which must be ≥ 61, and |K\(E1∪E2)| = 21 − k − |K∩A| − |K∩C|. ∎

**Lemma T (witnesses at a 5-pair).** In the setting of Lemma S, for every single G of type v and every p ∈ A_G
there is an edge H with H∩({v}∪A_G) = {p}. Every such H satisfies H∩C ⊆ C_G. If H is single, then H has type
≠ v, C_H = C_G and A_H∩A_G = {p}. The symmetric statement holds with A and C swapped.
*Proof.* Apply R.2 and R.3 to the 5-pair (E1,G); E2 is the witness at the point v. ∎

So any counterexample is forced into a tight configuration: one 5-pair, five single edges (one per type) with
pairwise disjoint 12-sets outside E1∪E2, and the equality cascades of Lemmas S and T. The EHT counting shows that
4-edge families {E1,E2,F_x,F_y} are exactly at span 61. **To prove t(21) = 4 it suffices to find one more unit
of loss anywhere in this rigid configuration.**

## Wave 6 case split (2026-10-14, started 17:05 UTC)
**Rollback note:** when Wave 6 started, this file contained only §0–§1 (Lemmas A, R, S, K, T). The triangle lemma,
W1, W2 and §4 mentioned in the brief were NOT in the file (lost in a rollback). Everything below is re-derived.

### 6.0 New derived constraint D1 (proved)
**D1.** Let (E,E') be a 5-pair, M = E∩E', and L an edge with M ⊄ L. Then |L∩(E∪E')| ≤ 9.
*Proof.* Pick x ∈ M∖L and a single F of type x (R.2). By R.3 (singles of ≥2 types exist) |F∖(E∪E')| = 12.
{E,E',L,F} has empty intersection (⊆ M∩F∩L = {x}∩L). Union = 37 + 12 + |L∖(E∪E'∪F)| ≥ 61, so
|L∖(E∪E')| ≥ 12. ∎  (r=16 analogue: |L∩(E∪E')| ≤ 7 for a 4-pair; holds in H(16,10,7): core part of L is 7.)
D1 is used as a reified constraint inside the region model work/e616/t21/w6model.py (source at end of section).

### 6.1 Case I = some Lemma-T witness is a single = "triangle" (re-derived, proved)
Case I: singles G (type v), H (type w≠v) with |A_G∩A_H| = 1, say A_G∩A_H = {p} (or the C-side version). By S(c),
C_G = C_H =: C0. Equivalently: for some single G and p∈A_G (or C_G) the Lemma-T witness is itself single.
**Lemma Tri-0 (exact Venn structure).** Rename Q = E1, P1 = E2, P2 = G, P3 = H, x12 = v, x13 = w, x23 = p.
All six pairs among Q,P1,P2,P3 meet in exactly 5. Triple intersections: Q∩Pi∩Pj = {x_ij} (1 point each),
P1∩P2∩P3 = C0 (4 points), quadruple ∅. Q∩Pi = {x_ij, x_ik} ∪ Q_i with |Q_i| = 3; Q_* = Q∖∪Pi has 9 points;
O_i = Pi∖(Q∪Pj∪Pk) has 12 points. e = 7·2 + 9 = 23: the 4-family is exactly at span 61.
(Check: |G∩H| = |{p}∪C0| = 5, |E2∩G| = |{v}∪C_G| = 5 by R.3.) The structure is S3-symmetric in P1,P2,P3.
Every 5-set Pi∩Pj = C0∪{x_ij} and Q∩Pi is a transversal (R.1).
**Lemma Tri-1 (J).** An edge J with J∩C0 = ∅ (exists, τ≥5) contains x12,x13,x23, has |J∩Pi| = 5 and
J∩Pi∩Pj = {x_ij}; {P1,P2,P3,J} is exactly at 61.
*Proof.* J meets each transversal C0∪{x_ij}, so contains all x_ij. {P1,P2,P3,J} has empty intersection, |∪Pi| = 52, so
|J∩∪Pi| ≤ 12; inclusion–exclusion gives |J∩∪Pi| = Σ|J∩Pi| − 3 ≥ 12. ∎
**Lemma Tri-2 (Y).** Fix {i,j,k} = {1,2,3} and c ∈ C0. An edge Y with Y∩(C0∪{x_ij}) = {c} exists (R.2 for the
5-pair (Pi,Pj)). Every such Y: avoids Q_k ∪ Q_* (R.3, Q is a (Pi,Pj)-single of type x_ij with outside part
Q_k∪Q_*), has |Y∩Pi| = |Y∩Pj| = 5, **contains x_ik and x_jk**, |Y∩Pk| ∈ {5,6}, and |Y∩Q_i| + |Y∩Q_j| ∈ {3,4}.
*Proof of x_ik ∈ Y.* Otherwise {Q,Pi,Pk,Y} has empty intersection (Q∩Pi∩Pk = {x_ik}); |Q∪Pi∪Pk| = 49 so
|Y∩(Q∪Pi∪Pk)| ≤ 9; |Y∩(Pi∪Pk)| ≥ 5+5−|Y∩(C0∪{x_ik})| = 9, so Y∩Q ⊆ Pi∪Pk, i.e. Y∩Q ⊆ Q_i ∪ {x_jk}: < 5
points, contradicting Lemma A. Same for x_jk with {Q,Pj,Pk,Y}. The bounds: D1 for (Pi,Pk) gives |Y∩Pk| ≤ 6;
D1 for (Q,Pk) (Y misses Q_k) gives |Y∩Q| + |Y∩Pk| − 2 ≤ 9; |Y∩Q| = 2 + |Y∩Q_i| + |Y∩Q_j| ≥ 5. ∎
If |Y∩Q_i| = 0 then (Q,Pi,Pj,Y) is again a triangle (Y is a (Q,Pi)-single of type x_ik whose C-part meets Pj's in
the single point c) — triangles propagate.
**Lemma Tri-3 (D).** An edge D avoiding {x12,x13,x23,c} (c∈C0) has D∩C0 = C0∖{c}, D∩Q_* = ∅, |D∩Pi| = 5 for all
i, |D∩Q_i| ∈ {1,2} with Σ|D∩Q_i| ≥ 5.
*Proof.* D meets every Q∩Pk, so D∩Q_k ≠ ∅. {Q,Pi,Pj,D} has empty intersection, so
|D∩Pi| + |D∩Pj| − z + |D∩(Q_k∪Q_*)| ≤ 9 with z = |D∩C0| (D∩Pi∩Pj = D∩C0). If z = 2 all three inequalities are
tight with |D∩(Q_k∪Q_*)| = 1, so |D∩Q| ≤ 3, contradiction. So z = 3, |D∩(Q_k∪Q_*)| ≤ 2 for each k, forcing
D∩Q_* = ∅ and the rest. ∎
**Lemma Tri-4 (Z).** An edge Z avoiding {x_ij, x_ik, c, c'} has Z∩C0 = C0∖{c,c'} (else Z is a (Pi,Pj)-single
of type c'' avoiding x_ik, contradicting Tri-2).
Status: Tri-0..4 are consistent so far; no contradiction by hand yet. CP-SAT runs below.

### 6.2 Refined case split (supersedes §4's (I)/(II))
For a 5-pair (X,Y), N = X∩Y, call it **uniform** if all its singles (all types) have the same A-part α ⊂ X∖N and the
same C-part γ ⊂ Y∖N. For cross-type singles (a,c) := (|A∩A'|,|C∩C'|) has a,c ≥ 1, a+c ≥ 5 (Lemma S); uniform ⟺ a=c=4
for every cross-type pair (same-type parts then agree through a third type).
* **Case U:** every 5-pair of G is uniform.  → **CLOSED (6.3, human proof + machine check of two finite facts).**
* **Case I (triangle):** some 5-pair has cross-type singles with a = 1 or c = 1. → open, see 6.1 / 6.5.
* **Case N:** no triangle, some 5-pair has cross-type singles with {a,c} ∩ {2,3} ≠ ∅. → open, see 6.4.
Both known examples (r=16 H(16,10,7); r=22 H(22,13,9)) are in Case U with no triangle (literal check
w6_check_examples.py: 150 K-pairs each; D1-analogue holds at r=16 with cap 7). So Case U is exactly "the EHT
example type", and its closure below uses the r=21 tightness essentially (it fails at r=22 by one unit, see end).

### 6.3 Theorem W6-U (PROVED): Case U is impossible at r = 21.
Fix a 5-pair (E1,E2), M, with singles' parts A0 ⊂ A, C0 ⊂ C; S := M ∪ A0 ∪ C0 (13 points). Call a 5-pair (X,Y)
**good** if N = X∩Y ⊂ S, X∩S = N∪α(X,Y), Y∩S = N∪γ(X,Y) (so S = N ⊔ α ⊔ γ). (E1,E2) is good. For an edge X in a
good pair put B_X = X∩S (9 points) and O(X) = X∖S (12 points).
**G (propagation).** If (X,Y) is good and F is a single of type y ∈ N, then F∩(X∪Y) = {y}∪α∪γ, so B_F = S∖(N∖{y})
and O(F) = F∖(X∪Y) is disjoint from O(X) and O(Y); and (X,F) is good with N' = {y}∪α, α' = N∖{y}, γ' = γ.
*Proof.* F∩N = {y}, F∩(X∖N) = α, F∩(Y∖N) = γ by uniformity and R.3. X∩F = {y}∪α ⊂ S. Y is a single of (X,F) of
type y (Y∩α = ∅) with A-part Y∩(X∖N') = N∖{y} and C-part Y∩(F∖N') = γ; uniformity of (X,F) gives α', γ'. ∎
**Relatives.** Fix X in a good pair (X,Y). Iterating G with X fixed moves N to {t}∪(B_X∖N) (t ∈ N); the complements
B_X∖N walk on the Kneser graph K(9,4), which is connected, so EVERY 5-subset N ⊂ B_X is X∩Z for a good pair (X,Z)
(machine check: 126/126 reached). Taking the type-t single of (X,Z) with N = C∪{t}: **for every 4-set C ⊂ B_X there is
an edge U in a good pair with B_U = S∖C and O(U) ∩ O(X) = ∅.**
**H (outside parts are disjoint).** If X is in a good pair and X' is any edge with B_X ⊄ X', then
|X'∩S| + |X'∩O(X)| ≤ 9.  *Proof.* Pick t ∈ B_X∖X' and split B_X∖{t} into 4-sets C_U, C_V; take relatives U, V. Then
X∩U∩V = {t} (S-part B_X∖(C_U∪C_V) = {t}; outside part ⊆ O(X)∩O(U) = ∅), so {X,X',U,V} has empty intersection,
and its union is ≤ 13 + 12·3 + (21 − |X'∩S|) − |X'∩O(X)|. L forces this ≥ 61. ∎
In particular two edges in good pairs with different B's have disjoint outside parts.
**Closure.** Starting from B_E1 = M∪A0, the rule B ↦ S∖C (C ⊂ B, |C| = 4) reaches all 715 9-subsets of S (same
computation as closure9.py; re-run in w6_uclosure.py), each realised by an edge in a good pair. Take the four
edges with B_i = S∖({s0}∪R_i), R_1..R_4 a partition of S∖{s0} into triples. Their B's have empty intersection and
union 12; by H their outside parts are pairwise disjoint. So the 4 edges have empty intersection and union
12 + 4·12 = 60 ≤ 60, contradicting L. ∎
*Sanity vs. examples.* At r = 22 (H(13,9)) the same family has union 12 + 4·13 = 64 > 63 and H's count gives 64:
no contradiction, as it must be. At r = 16 (S has 10 points, B's are 7-sets) a 4-family of 7-sets with empty
intersection and union ≤ 9 would need 4 disjoint pairs covering 9 points — impossible, so no contradiction there either.
Scripts: work/e616/t21/w6_uclosure.py (Kneser reachability, closure, bad family), w6_check_examples.py.
**Consequence:** a counterexample has a non-uniform 5-pair, i.e. lies in Case I or Case N.

### 6.4 Additional triangle facts (proved) and what remains in Case I
**Tri-5 (X).** Every edge avoiding x12, x13, x23 meets C0 in ≥ 3 points (proof of Tri-3, which never used the 4th
avoided point). Hence an edge Z avoiding {x_ij, x_ik, c, c'} (Tri-4) **contains the third point x_jk**.
**Tri-6.** (P1,P2) is never uniform: uniformity would force Y^{12}_c ⊇ Q_1∪Q_2, i.e. |Y∩Q_1|+|Y∩Q_2| = 6 > 4.
**Tri-7 ((Q,Pk)-singles).** For q ∈ Q_k an edge W with W∩({x_ik,x_jk}∪Q_k) = {q} exists; it avoids O_i∪O_j
(R.3 against P_i, P_j, which are (Q,Pk)-singles of types x_ik, x_jk), has |W∩Q| = |W∩Pk| = 5, |W∩C0| ≥ 1, and if
x_ij ∉ W then |W∩C0| ≥ 3 (Tri-5).
CP-SAT (pruned region model w6fast.py, triangle fixed, D1 on, L on all ≤4-subfamilies): guided witness sets
{J,Y12,D}, {Y12,Y13,Y23}, {J,Z1,D} (k=7), {J,Y12,Y13,D}, {Y12,Y13,Y23,D}, {Y12,Y13,Z1,D} (k=8) and
{J,Y12,Y13,Y23,D} (k=9, 943 s) are all **FEASIBLE** (k=9 solution in work/e616/t21/w6_tri_b.log satisfies
Tri-2 by inspection). k=11 {J,Y12,Y13,Y23,Z1,Z2,Z3} did not finish (killed; CPU contention). So no
bounded-witness contradiction for the triangle is in reach of this model; the triangle is locally consistent
with ≥ 9 edges.

### 6.5 Case N (no triangle, non-uniform) — open
Probe w6caseN.py (E1,E2,G,H with fixed (a,c), naive min-cover CEGAR): (2,3) and (3,2) feasible up to k=8,
k=9 timeouts (120 s). Other (a,c) were queued (log w6_caseN.log). Inconclusive, as expected for naive CEGAR.
Hand facts for c = 4, a ∈ {2,3} (C_G = C_H = C0): every edge avoiding C0 contains v, w and A_G∩A_H and meets
E2, G, H in exactly 5 ({E2,G,H,X'} is then exactly at 61). Proof: |E2∪G∪H| = 53 − a, and inclusion–exclusion.

### 6.6 PRECISE REMAINING CONFIGURATION (what a counterexample must contain)
By Lemma A, W6-U: a counterexample contains a 5-pair (E1,E2) with two singles G (type v), H (type w ≠ v) such that
(|A_G∩A_H|, |C_G∩C_H|) ∈ {(1,4),(4,1)} [triangle, Tri-0..7 apply] or ∈ {(2,3),(3,2),(2,4),(4,2),(3,3),(3,4),(4,3)}
[Case N]. Equivalently: **t(21) = 4 ⟺ no 5-pair is non-uniform.** Any proof of uniformity of all 5-pairs finishes
the problem via W6-U. Suggested next step: run the U-closure argument "locally" — W6-U only used uniformity of the
5-pairs reached from (E1,E2) by propagation G, so it suffices to show that a non-uniform pair forces a 49-triple
(three pairwise-5 edges with one common point, union 49) plus an edge avoiding that point with ≥10 points in the
union — the mechanism behind D1, Tri-2, Tri-3 and Lemma H.

### 6.7 Checks against the examples (no contradiction)
* r=16 H(16,10,7) and r=22 H(22,13,9): literal check (w6_check_examples.py, 150 K-pairs each): min pair = K,
  D1-analogue (cap 7 at r=16) holds, every K-pair uniform, no triangle. Output:
  `r=16 H(10,7) edges=120 K-pairs tested=150 D1(cap 7) holds=True uniform U holds=True no-triangle=True`
  `r=22 H(13,9) edges=715 K-pairs tested=150 D1(cap 10) holds=True uniform U holds=True no-triangle=True`
* W6-U's final count fails by exactly one unit at r=22 (64 > 63) and is vacuous at r=16 (see 6.3).
* Background construct sweeps (chainA/chainB): checked 17:30 UTC — no FOUND at r=21 (only the r=16/r=22 controls).

### 6.8 Script sources (Wave 6)

#### work/e616/t21/w6model.py
```python
"""Wave 6 region model (generic in r, K=tau target, W=window).  Edges 0..k-1; c[T] = #vertices whose membership
set among the k edges is exactly T.  Constraints (all TRUE consequences in any counterexample G):
  size r; pairs >= K (L1); pair (0,1) == K (Lemma A); L on every subfamily (>=3 edges);
  D1 (needs the tight rigidity, valid at r=21 and the r=16 analogue, NOT at r=22): if |E_i & E_j| == K and
     E_l does not contain M_ij = E_i & E_j, then |E_l & (E_i | E_j)| <= 4r - W - 3K   (=9 at r=21, =7 at r=16).
  witness patterns: pats[e] = list of (inc, exc, mu) over edges < e: IF every group has >= mu vertices THEN edge e
     avoids >= mu vertices of each group (a <=4-set exists; tau>=5 gives an edge avoiding it).
  fixed: list of (inc, exc, op, val) constraints on group sizes over ALL k edges (case hypotheses).
INFEASIBLE => no counterexample containing the hypothesised configuration."""
import itertools, time, sys
sys.path.append("work/e616/pylib")
from ortools.sat.python import cp_model

def grp(k, inc, exc, without=None):
    full = 1 << k
    return [T for T in range(1, full) if (T & inc) == inc and (T & exc) == 0 and (without is None or not (T >> without & 1))]

def build(k, pats, fixed=(), r=21, K=5, W=60, d1=True, five01=True):
    m = cp_model.CpModel(); full = 1 << k
    c = [None] + [m.NewIntVar(0, r, f'c{T}') for T in range(1, full)]
    S = lambda Ts: sum(c[T] for T in Ts)
    for i in range(k):
        m.Add(S(grp(k, 1 << i, 0)) == r)
    pairK = {}
    for i, j in itertools.combinations(range(k), 2):
        I = (1 << i) | (1 << j)
        e = S(grp(k, I, 0)); m.Add(e >= K)
        if five01 and (i, j) == (0, 1): m.Add(e == K)
        f = m.NewBoolVar(f'f{i}{j}')
        m.Add(e == K).OnlyEnforceIf(f); m.Add(e >= K + 1).OnlyEnforceIf(f.Not())
        pairK[(i, j)] = f
    for I in range(1, full):
        if bin(I).count('1') < 3: continue
        b = m.NewBoolVar('')
        m.Add(S(grp(k, I, 0)) >= 1).OnlyEnforceIf(b)
        m.Add(sum(c[T] for T in range(1, full) if T & I) >= W + 1).OnlyEnforceIf(b.Not())
    if d1:
        cap = 4 * r - W - 3 * K
        for (i, j), f in pairK.items():
            I = (1 << i) | (1 << j)
            for l in range(k):
                if l in (i, j): continue
                g = m.NewBoolVar('')  # g <=> M_ij not contained in E_l
                miss = S(grp(k, I, 1 << l))
                m.Add(miss >= 1).OnlyEnforceIf(g); m.Add(miss == 0).OnlyEnforceIf(g.Not())
                m.Add(sum(c[T] for T in range(1, full) if (T >> l & 1) and (T & I)) <= cap).OnlyEnforceIf([f, g])
    for e, pat in pats.items():
        assert sum(it[2] for it in pat) <= 4
        ante = []
        for inc, exc, mu in pat:
            assert (inc | exc) < (1 << e)
            a = m.NewBoolVar('')
            m.Add(S(grp(k, inc, exc)) >= mu).OnlyEnforceIf(a)
            m.Add(S(grp(k, inc, exc)) <= mu - 1).OnlyEnforceIf(a.Not())
            ante.append(a)
        allA = m.NewBoolVar('')
        m.AddBoolAnd(ante).OnlyEnforceIf(allA)
        m.AddBoolOr([x.Not() for x in ante]).OnlyEnforceIf(allA.Not())
        for inc, exc, mu in pat:
            m.Add(S(grp(k, inc, exc, without=e)) >= mu).OnlyEnforceIf(allA)
    for inc, exc, op, val in fixed:
        s = S(grp(k, inc, exc))
        if op == '==': m.Add(s == val)
        elif op == '>=': m.Add(s >= val)
        elif op == '<=': m.Add(s <= val)
    return m, c

def solve(k, pats, fixed=(), tl=100, workers=2, **kw):
    t0 = time.time()
    m, c = build(k, pats, fixed, **kw)
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = tl; s.parameters.num_workers = workers
    st = s.Solve(m)
    name = s.StatusName(st)
    sol = {T: s.Value(c[T]) for T in range(1, 1 << k) if s.Value(c[T])} if st in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None
    return name, sol, time.time() - t0

def show(k, sol):
    return {bin(T)[2:].zfill(k)[::-1]: v for T, v in sorted(sol.items())}

def min_cover(k, sol, maxsize=4):
    regs = sorted(sol, key=lambda T: -bin(T).count('1'))
    allE = (1 << k) - 1
    for size in range(1, maxsize + 1):
        best = None
        for combo in itertools.combinations_with_replacement(regs, size):
            u = 0
            for T in combo: u |= T
            if u != allE: continue
            cnt = {}
            for T in combo: cnt[T] = cnt.get(T, 0) + 1
            if any(cnt[T] > sol[T] for T in cnt): continue
            score = sum(bin(T).count('1') for T in combo)
            if best is None or score > best[0]: best = (score, sorted(cnt.items()))
        if best: return best[1]
    return None

B = lambda *idx: sum(1 << i for i in idx)
```

#### work/e616/t21/w6fast.py
```python
"""Pruned region model: like w6model.build but region variables only for T whose restriction to the first k0 edges
lies in `base` (list of allowed k0-bit regions, 0 allowed = vertex in none of the first k0 edges).  Sound when the
first k0 edges are fully fixed by the case hypothesis (base sizes given in `basesz`)."""
import itertools, time, sys
sys.path.append("work/e616/pylib")
from ortools.sat.python import cp_model

def build(k, k0, basesz, pats, r=21, K=5, W=60, d1=True, maxfam=99):
    m = cp_model.CpModel(); low = (1 << k0) - 1
    regs = [T for T in range(1, 1 << k) if (T & low) in basesz]
    c = {T: m.NewIntVar(0, r, '') for T in regs}
    S = lambda pred: sum(c[T] for T in regs if pred(T))
    for b, sz in basesz.items():
        if b: m.Add(S(lambda T: (T & low) == b) == sz)
    for i in range(k0, k):
        m.Add(S(lambda T: T >> i & 1) == r)
    pairK = {}
    for i, j in itertools.combinations(range(k), 2):
        I = (1 << i) | (1 << j)
        e = S(lambda T: T & I == I); m.Add(e >= K)
        f = m.NewBoolVar(''); m.Add(e == K).OnlyEnforceIf(f); m.Add(e >= K + 1).OnlyEnforceIf(f.Not()); pairK[(i, j)] = f
    for I in range(1, 1 << k):
        if bin(I).count('1') < 3 or bin(I).count('1') > maxfam or (I >> k0) == 0: continue
        b = m.NewBoolVar('')
        m.Add(S(lambda T: T & I == I) >= 1).OnlyEnforceIf(b)
        m.Add(S(lambda T: T & I) >= W + 1).OnlyEnforceIf(b.Not())
    if d1:
        cap = 4 * r - W - 3 * K
        for (i, j), f in pairK.items():
            I = (1 << i) | (1 << j)
            for l in range(k):
                if l in (i, j) or max(i, j, l) < k0: continue
                g = m.NewBoolVar('')
                miss = S(lambda T: T & I == I and not (T >> l & 1))
                m.Add(miss >= 1).OnlyEnforceIf(g); m.Add(miss == 0).OnlyEnforceIf(g.Not())
                m.Add(S(lambda T: (T >> l & 1) and (T & I)) <= cap).OnlyEnforceIf([f, g])
    for e, pat in pats.items():
        ante = []
        for inc, exc, mu in pat:
            a = m.NewBoolVar('')
            s = S(lambda T: (T & inc) == inc and (T & exc) == 0)
            m.Add(s >= mu).OnlyEnforceIf(a); m.Add(s <= mu - 1).OnlyEnforceIf(a.Not()); ante.append(a)
        allA = m.NewBoolVar(''); m.AddBoolAnd(ante).OnlyEnforceIf(allA); m.AddBoolOr([x.Not() for x in ante]).OnlyEnforceIf(allA.Not())
        for inc, exc, mu in pat:
            m.Add(S(lambda T: (T & inc) == inc and (T & exc) == 0 and not (T >> e & 1)) >= mu).OnlyEnforceIf(allA)
    return m, c, regs

def solve(k, k0, basesz, pats, tl=100, workers=2, **kw):
    t0 = time.time(); m, c, regs = build(k, k0, basesz, pats, **kw); tb = time.time() - t0
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = tl; s.parameters.num_workers = workers
    st = s.Solve(m); name = s.StatusName(st)
    sol = {T: s.Value(c[T]) for T in regs if s.Value(c[T])} if st in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None
    return name, sol, time.time() - t0, tb
```

#### work/e616/t21/w6tri2.py
```python
import sys, json
from w6fast import solve
from w6model import B, show, min_cover
r = int(sys.argv[1]); tl = float(sys.argv[2]); guide = sys.argv[3]; kmax = int(sys.argv[4]) if len(sys.argv) > 4 else 0; mf = int(sys.argv[5]) if len(sys.argv) > 5 else 99
P = {21: dict(r=21, K=5, W=60), 16: dict(r=16, K=4, W=45)}[r]; K = P['K']; R = P['r']
# triangle: 0=Q(E1) 1=P1(E2) 2=P2(G) 3=P3(H)
basesz = {B(0): R-3*(K-2)-3, B(1): R-K-1-(K-2)-1+0, B(2): 0, B(3): 0,
          B(0,1): K-2, B(0,2): K-2, B(0,3): K-2, B(0,1,2): 1, B(0,1,3): 1, B(0,2,3): 1, B(1,2,3): K-1, 0: 0}
for i in (1, 2, 3): basesz[B(i)] = R - (K-1) - 2 - (K-2)
x12, x13, x23, C0 = (B(0,1,2), B(3)), (B(0,1,3), B(2)), (B(0,2,3), B(1)), (B(1,2,3), B(0))
Q1, Q2, Q3, Qs = (B(0,1), B(2,3)), (B(0,2), B(1,3)), (B(0,3), B(1,2)), (B(0), B(1,2,3))
G = {'J': [(*C0, 4)],
     'Y12': [(*x12, 1), (*C0, 3)], 'Y13': [(*x13, 1), (*C0, 3)], 'Y23': [(*x23, 1), (*C0, 3)],
     'Z1': [(*x12, 1), (*x13, 1), (*C0, 2)], 'Z2': [(*x12, 1), (*x23, 1), (*C0, 2)], 'Z3': [(*x13, 1), (*x23, 1), (*C0, 2)],
     'D': [(*x12, 1), (*x13, 1), (*x23, 1), (*C0, 1)]}
if K == 4:  # r=16 analogue: C0 has 3 points
    G = {'J': [(*C0, 3)], 'Y12': [(*x12, 1), (*C0, 2)], 'Y13': [(*x13, 1), (*C0, 2)], 'Y23': [(*x23, 1), (*C0, 2)],
         'Z1': [(*x12, 1), (*x13, 1), (*C0, 1)], 'Z2': [(*x12, 1), (*x23, 1), (*C0, 1)], 'Z3': [(*x13, 1), (*x23, 1), (*C0, 1)],
         'D': [(*x12, 1), (*x13, 1), (*x23, 1)]}
pats = {}; k = 4
for name in guide.split(','):
    if name: pats[k] = G[name]; k += 1
while True:
    st, sol, t, tb = solve(k, 4, basesz, pats, tl, maxfam=mf, **P)
    print(f'r={r} k={k} guide={guide} {st} {t:.1f}s (build {tb:.1f}s)', flush=True)
    if sol is None or k >= kmax: 
        if sol: print('  sol:', show(k, sol), flush=True)
        break
    cov = min_cover(k, sol); print('  sol:', show(k, sol), flush=True)
    if cov is None: print('  TAU>=5 model solution'); break
    full = (1 << k) - 1; pats[k] = [(T, full ^ T, mu) for T, mu in cov]
    print('  cover ->', [(bin(T)[2:].zfill(k)[::-1], mu) for T, mu in cov], flush=True); k += 1
```

#### work/e616/t21/w6caseN.py
```python
"""Case N / non-uniform probe: 0=E1 1=E2 (5-pair), 2=G single type v, 3=H single type w, |A_G&A_H|=a, |C_G&C_H|=c.
Then CEGAR witness edges (min 4-covers).  Usage: python w6caseN.py a c kmax tl"""
import sys
from w6model import *
a, c, kmax, tl = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
fixed = [(B(0,1,2), B(3), '==', 1), (B(0,1,3), B(2), '==', 1), (B(0,1,2,3), 0, '==', 0),
         (B(0,2,3), B(1), '==', a), (B(1,2,3), B(0), '==', c),
         (B(0,2), B(1), '==', 4), (B(0,3), B(1), '==', 4), (B(1,2), B(0), '==', 4), (B(1,3), B(0), '==', 4),
         (B(2,3), B(0,1), '==', 0)]
pats = {}; k = 4
while k <= kmax:
    st, sol, t = solve(k, pats, fixed, tl)
    print(f'a={a} c={c} k={k} {st} {t:.1f}s', flush=True)
    if sol is None: break
    cov = min_cover(k, sol)
    if cov is None: print('  TAU>=5 model sol', show(k, sol)); break
    full = (1 << k) - 1; pats[k] = [(T, full ^ T, mu) for T, mu in cov]; k += 1
if sol is not None: print('  last sol:', show(k if k <= kmax else kmax, sol))
```

#### work/e616/t21/w6_uclosure.py
```python
r"""Checks for Lemma W6-U (Case II-U): (1) moves N -> {t} u (B\N), t in N, on 5-subsets of a 9-set B are connected
(complements walk on Kneser K(9,4)); (2) the relative rule B -> S13 \ C (C a 4-subset of B) closes from one 9-set to
all 715 9-subsets of a 13-set (= closure9.py); (3) a bad family S13 \ ({0} u R_i) exists in it (4 sets, empty
intersection, union 12)."""
from itertools import combinations
B = frozenset(range(9)); N0 = frozenset(range(5))
seen = {N0}; fr = [N0]
while fr:
    nf = []
    for N in fr:
        for t in N:
            N2 = frozenset({t}) | (B - N)
            if N2 not in seen: seen.add(N2); nf.append(N2)
    fr = nf
print('reachable 5-subsets of B:', len(seen), 'of 126')
S13 = frozenset(range(13)); start = frozenset(range(9)); F = {start}; fr = [start]
while fr:
    nf = []
    for X in fr:
        for C in combinations(sorted(X), 4):
            Y = S13 - frozenset(C)
            if Y not in F: F.add(Y); nf.append(Y)
    fr = nf
print('closure size:', len(F))
R = [frozenset({1,2,3}), frozenset({4,5,6}), frozenset({7,8,9}), frozenset({10,11,12})]
fam = [S13 - ({0} | r) for r in R]
print('bad family in closure:', all(s in F for s in fam), 'intersection:', set.intersection(*map(set, fam)),
      'union size:', len(frozenset().union(*fam)), '-> span with disjoint 12-point outsides =', len(frozenset().union(*fam)) + 48)
```

#### work/e616/t21/w6_check_examples.py
```python
"""Literal checks of Wave-6 lemmas on the known examples: r=16 H(16,10,7) (tau=4, window 45, tight analogue)
and r=22 H(22,13,9) (tau=5, window 63, slack analogue).  Checks: min pair = K; D1 analogue (cap 4r-W-3K) at r=16;
uniformity U (all singles of a K-pair have equal A- and C-parts); no triangle (cross-type a=1 never happens)."""
import itertools, random
def H(r, k, q):
    E = []; nxt = k
    for Y in itertools.combinations(range(k), q):
        E.append(frozenset(Y) | frozenset(range(nxt, nxt + r - q))); nxt += r - q
    return E
for (r, k, q, K, W) in [(16, 10, 7, 4, 45), (22, 13, 9, 5, 63)]:
    E = H(r, k, q); random.seed(1)
    pairs = [(a, b) for a, b in itertools.combinations(range(len(E)), 2) if len(E[a] & E[b]) == K]
    random.shuffle(pairs); pairs = pairs[:150]
    d1ok = Uok = tri = True; cap = 4 * r - W - 3 * K
    for a, b in pairs:
        X, Y = E[a], E[b]; N = X & Y
        for L in E:
            if L in (X, Y): continue
            if not N <= L and len(L & (X | Y)) > cap: d1ok = False
        sing = [F for F in E if len(F & N) == 1]
        Ap = {frozenset(F & (X - N)) for F in sing}; Cp = {frozenset(F & (Y - N)) for F in sing}
        if len(Ap) != 1 or len(Cp) != 1: Uok = False
        for F, G in itertools.combinations(sing, 2):
            if F & N != G & N and (len(F & G & (X - N)) == 1 or len(F & G & (Y - N)) == 1): tri = False
    print(f'r={r} H({k},{q}) edges={len(E)} K-pairs tested={len(pairs)} D1(cap {cap}) holds={d1ok} '
          f'uniform U holds={Uok} no-triangle={tri}')
```

## 2026-10-15 05:14 EDT run: five-singles feasibility (Case N), NEGATIVE
Sweep A16 finished: n=19 cycmult:7, 23 cycmult:2, 25 cycmult:2, 21 cycmult:4 UNSAT; 24 cycmult:5 TIMEOUT. No r=21 FOUND.
Unit: SAT model of the (A,C)-parts of 5 singles of distinct types (|A_i|=|C_i|=4 in a 16-point set; Lemma S a,c>=1, a+c>=5, a=1=>C equal, c=1=>A equal; every 3 share a point; every 4 share a point or |∪A|+|∪C|>=9) with pair (0,1) forced to each Case-N (a,c) in {(2,3),(3,2),(2,4),(4,2),(3,3),(3,4),(4,3)}: ALL SAT. So five singles alone give no contradiction; a contradiction in Case N must use extra edges (Lemma T witnesses, multi edges, D1 for the pair (G,H)=5-pair with M'=(A_G∩A_H)∪(C_G∩C_H)). Script: work/e616/t21/five_singles.py (pysat Cadical, ~60 lines; regenerate from this description). Stall 17.

```
# Case N feasibility of the 5 singles' (A,C)-parts at r=21 (necessary conditions only)
import itertools, sys
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
NP=16
def run(a0,c0):
    pool=IDPool(); cl=[]
    A=[[pool.id(('A',i,p)) for p in range(NP)] for i in range(5)]
    C=[[pool.id(('C',i,p)) for p in range(NP)] for i in range(5)]
    def card_eq(lits,k):
        e=CardEnc.equals(lits=lits,bound=k,vpool=pool,encoding=EncType.seqcounter); cl.extend(e.clauses)
    for i in range(5): card_eq(A[i],4); card_eq(C[i],4)
    def inter(X,i,j):
        v=[]
        for p in range(NP):
            t=pool.id(('t',id(X),i,j,p)); cl.append([-t,X[i][p]]); cl.append([-t,X[j][p]]); cl.append([t,-X[i][p],-X[j][p]]); v.append(t)
        return v
    def atleast(l,k):
        e=CardEnc.atleast(lits=l,bound=k,vpool=pool,encoding=EncType.seqcounter); cl.extend(e.clauses)
    ia={};ic={}
    for i,j in itertools.combinations(range(5),2):
        ia[i,j]=inter(A,i,j); ic[i,j]=inter(C,i,j)
        cl.append(list(ia[i,j])); cl.append(list(ic[i,j]))
        atleast(ia[i,j]+ic[i,j],5)
        # a=1 => C equal ; c=1 => A equal
        # a<=1 means: not (at least 2) ; encode: at least2(ia) or C_i==C_j
        a2=pool.id(('a2',i,j)); c2=pool.id(('c2',i,j))
        e=CardEnc.atleast(lits=ia[i,j],bound=2,vpool=pool,encoding=EncType.seqcounter)
        # a2 <-> atleast2 : only need a2 -> atleast2 direction and (not a2 -> C equal)
        for c in e.clauses: cl.append([-a2]+c)
        e=CardEnc.atleast(lits=ic[i,j],bound=2,vpool=pool,encoding=EncType.seqcounter)
        for c in e.clauses: cl.append([-c2]+c)
        for p in range(NP):
            cl.append([a2,-C[i][p],C[j][p]]); cl.append([a2,C[i][p],-C[j][p]])
            cl.append([c2,-A[i][p],A[j][p]]); cl.append([c2,A[i][p],-A[j][p]])
    for k in (3,4):
        for S in itertools.combinations(range(5),k):
            common=[]
            for X in (A,C):
                for p in range(NP):
                    t=pool.id(('cm',id(X),S,p)); cl.append([-t]+[X[i][p] for i in S][:1]); 
                    for i in S: cl.append([-t,X[i][p]])
                    common.append(t)
            if k==3: cl.append(common)
            else:
                # common OR |unionA|+|unionC|>=9
                g=pool.id(('g',S)); 
                cl.append(common+[g])
                un=[]
                for X in (A,C):
                    for p in range(NP):
                        u=pool.id(('u',id(X),S,p)); 
                        for i in S: cl.append([-X[i][p],u])
                        cl.append([-u]+[X[i][p] for i in S]); un.append(u)
                e=CardEnc.atleast(lits=un,bound=9,vpool=pool,encoding=EncType.seqcounter)
                for c in e.clauses: cl.append([-g]+c)
    # pair (0,1) exactly (a0,c0)
    for lits,k in ((ia[0,1],a0),(ic[0,1],c0)): card_eq(lits,k)
    # symmetry: A_0 = {0..3}, C_0={0..3}
    for p in range(NP):
        cl.append([A[0][p] if p<4 else -A[0][p]]); cl.append([C[0][p] if p<4 else -C[0][p]])
    s=Cadical153(bootstrap_with=cl); r=s.solve()
    print(a0,c0,'SAT' if r else 'UNSAT',flush=True)
    if r:
        m=set(x for x in s.get_model() if x>0)
        for i in range(5): print(i,[p for p in range(NP) if A[i][p] in m],[p for p in range(NP) if C[i][p] in m])
for a0,c0 in [(2,3),(3,2),(2,4),(4,2),(3,3),(3,4),(4,3)]: run(a0,c0)
```

## 2026-10-15 06:14 EDT run: Case N with a+c=5 is a "K4 configuration" (derived by hand, not machine-checked)
For singles G (type v), H (type w), v≠w, O_G∩O_H=∅ (Lemma S): G∩H = (A_G∩A_H)∪(C_G∩C_H), size a+c. When (a,c)∈{(2,3),(3,2)}, |G∩H|=5, so (G,H) is itself a 5-pair with M''=G∩H. Then E1,E2,G,H have ALL six pairwise intersections of size exactly 5 (E1E2=M, E1G={v}∪A_G, E1H={w}∪A_H, E2G={v}∪C_G, E2H={w}∪C_H, GH=M''), no common point, union = 4·21 − 30 + (triple terms 1+1+a+c=7) = 61 (tight, consistent). Triple intersections: E1E2G={v}, E1E2H={w}, E1GH=A_G∩A_H (size a), E2GH=C_G∩C_H (size c). Uniform case is a=1,c=4 (triangle). So Lemmas R,S,K,T,D1 apply symmetrically to all six pairs; Lemma K at pair (G,H) with K=E1 (k=a=2): tight (|E1∩(G∖H)|=3=5−k) and forces |E1∩O_F|≤1 for singles F of type x∈C_G∩C_H; no contradiction found by hand. For a+c≥6 (the other five Case-N classes) (G,H) is not a 5-pair. Next: encode the K4 configuration with all six pairs rigid in w6model-style CEGAR (a=2,c=3), k≥9 was where naive CEGAR timed out. Stall 18.

## Wave 7 triangle (2026-10-15, started 08:05 EDT)
Notation of §6.1 (Tri-0): apex Q, base P1,P2,P3; ℓ_i := Q∩P_i = {x_ij,x_ik}∪Q_i (5 points); K_Q := ℓ1∪ℓ2∪ℓ3 (12 points);
C0 = P1∩P2∩P3; R_i := Q_i∪O_i; U := V∖(Q∪P1∪P2∪P3). "Apex" = any edge avoiding C0.

### 7.1 New proved lemmas
**W7-1 (trace triangles are triangle-K4s).** If X1,X2,X3 are edges with |Q∩X_i| = 5, the three traces Q∩X_i pairwise meet in
exactly one point and have no common point, then {Q,X1,X2,X3} is a triangle K4 (Tri-0) with apex Q: X_i∩X_j = (one point of Q)
∪ T, T := X1∩X2∩X3 a 4-set outside Q.
*Proof.* Let p_ij = |X_i∩X_j∖Q| ≥ 4 (Lemma A), t = |X1∩X2∩X3| (⊂ outside Q, ≥1 by F1). {Q,X1,X2,X3} has empty intersection,
union = 21 + 48 − Σp_ij + t ≥ 61, so Σp_ij − t ≤ 8. With t ≤ min p_ij, Σp_ij − t ≥ (two largest p) ≥ 8: all p_ij = 4 = t. ∎

**W7-2 ((Q,P_i)-singles of type q ∈ Q_i).** Let W be an edge with W∩ℓ_i = {q}, q ∈ Q_i (exists by R.2). Then
W∩O_j = W∩O_k = ∅, |W∩U| = 12, |W∩C0| ≥ 3, |W∩O_i| = 4 − |W∩C0|, W∩Q = {q} ∪ A_W with A_W ⊂ Q∖ℓ_i, |A_W| = 4,
|A_W∩ℓ_j| + |W∩C0| ≥ 5 and |A_W∩ℓ_k| + |W∩C0| ≥ 5.
*Proof.* At the 5-pair (Q,P_i), P_j and P_k are singles of types x_ij, x_ik with outside parts O_j, O_k, A-parts ℓ_j∖{x_ij},
ℓ_k∖{x_ik} (meeting only in x_jk) and C-parts C0. Lemma S(a) gives W∩O_j = W∩O_k = ∅, so the 12-point outside part
W∖(Q∪P_i) lies in U. S(b) gives a_j + c ≥ 5, a_k + c ≥ 5 with c = |W∩C0| ≤ 4; a_j + a_k ≤ |A_W| + 1 = 5, so c ≥ 3.
|W∩P_i| = 5 = 1 + c + |W∩O_i|. ∎  (Tri-7 had only c ≥ 1.)

**W7-3 (type-x_ij singles with one C0 point are case-(b) Y's).** If F∩ℓ_i = {x_ij} and |F∩C0| = 1, F∩C0 = {c}, then F is a
(P_i,P_k)-single of type c with F∩Q_i = ∅ and F∩Q = {x_ij, x_jk} ∪ Q_k. (Every type-x_ij single meets C0: else it is an apex
and contains x_ik by Tri-1.)  *Proof.* S(c) at (Q,P_i) against P_k: c-value 1 forces A_F = A_{P_k} = {x_jk}∪Q_k. ∎

**W7-4 (Lemma CP: "C0-pairs").** Call (X1,X2) a *C0-pair through p* if |Q∩X1| = |Q∩X2| = 5, Q∩X1∩X2 = {p} and
X1∩X2 = C0∪{p} (so |Q∪X1∪X2| = 49). Then every edge F with p ∉ F satisfies
  |F∩Q ∖ (X1∪X2)| ≤ |F∩C0| − 1.
In particular every apex contains p, and every F with |F∩C0| = 1, p ∉ F has F∩Q ⊂ X1∪X2.
*Proof.* {Q,X1,X2,F} has empty intersection, so |F∩(Q∪X1∪X2)| ≤ 9. The sets F∩Q, F∩C0, F∩(X_i∖(Q∪C0)) are disjoint and
|F∩(X_i∖(Q∪C0))| ≥ 5 − z − |F∩Q∩X_i| (z = |F∩C0|, Lemma A). Summing: |F∩Q| − |F∩Q∩X1| − |F∩Q∩X2| ≤ z − 1, and
Q∩X1∩X2 = {p} ∌ F. ∎
Known C0-pairs: (P_i,P_j) through x_ij. **If |W∩C0| = 4 in W7-2, then (P_i,W) is a C0-pair through q** (W∩P_i = {q}∪C0).

### 7.2 The PG(2,4) skeleton (explains why local models are feasible, and what a global proof must do)
Q has 21 points and the traces ℓ_i are 5-sets pairwise meeting in one point: the triangle is the "three lines" part of a
projective plane of order 4. Model: Q = PG(2,4), X_ℓ = ℓ ∪ C0 ∪ O_ℓ (O_ℓ pairwise disjoint 12-sets), one edge per line.
Check: every 3 non-concurrent lines give exactly Tri-0; all Lemma-S/T/W7 relations hold with equality (W's = X_m for lines m
through q, a = 1, C-parts C0). It satisfies L (a subfamily with empty intersection must contain Q and three non-concurrent X's:
union ≥ 21+4+36 = 61) but τ = 2 ({c, q}). **Lemma CP kills every attempt to raise τ:** an edge F with F∩C0 = {c} (needed,
e.g. to avoid (C0∖c)∪{q}) has |F∩Q| ≥ 5, so there is p ∈ Q∖F... every pair of the 5 lines through p is a C0-pair, so
F∩Q ⊂ (ℓ1∪ℓ2)∩(ℓ3∪ℓ4) = {p}: contradiction. (Apexes F, z=0, must contain every point, so F = Q.)
So the triangle is locally a fragment of this plane; a global contradiction should come from generating enough C0-pairs through
one point p ∉ Y for a Y-edge (|Y∩C0| = 1): two C0-pairs through p whose trace-unions meet in ≤ 4 points of Q∖{p} suffice.

## Wave 7 Case N (2026-10-15, started 07:56 EDT)
### N.0 Verification of the 06:14 K4 claim (VERIFIED, general)
For a 5-pair (E1,E2) and singles G (type v), H (type w≠v): G∩H = (A_G∩A_H) ∪ (C_G∩C_H) because G∩M={v}, H∩M={w},
O_G∩O_H = ∅ (S(a)) and O_G,O_H lie outside E1∪E2. Inclusion–exclusion: pairs 5,5,5,5,5,a+c; triples
E1E2G={v}, E1E2H={w}, E1GH=A_G∩A_H (a), E2GH=C_G∩C_H (c); quadruple ∅; union 84−(25+a+c)+(2+a+c) = **61 for every
(a,c)** (the 4-family is always exactly tight). For a+c=5 all six pairs are 5-pairs ("K4 configuration"). Concrete
instance check: work/e616/t21/k4verify.py prints pairs [5,5,5,5,5,a+c], triples [1,1,a,c], union 61 for all 8 classes.
**General K4 facts (proved):** (i) any 4 edges, pairwise meeting in exactly 5, with empty 4-fold intersection have
union 54 + Σ(triples) ≥ 61, so Σ triples ≥ 7; triple sizes are ≥ 1 (F1), so the triple vector is (4,1,1,1)
[= triangle Tri-0], (3,2,1,1) [= Case N (2,3)/(3,2)] or (2,2,2,1) [then some 5-pair has one single and one multi with
k=2 among the other two]. (ii) For X any further edge and a triple T_ijk with X∩T_ijk = ∅:
|X∩(P_i∪P_j∪P_k)| ≤ 8 + |T_ijk| (L on {P_i,P_j,P_k,X}, |P_i∪P_j∪P_k| = 48 + |T_ijk|).
(iii) In (3,2,1,1) every one of the 6 pairs is a 5-pair; regions (P0=E1,P1=E2,P2=G,P3=H): v, w, α=A_G∩A_H (2),
γ=C_G∩C_H (3), m3=M∖{v,w} (3), a3=A_G∖A_H (2), a4=A_H∖A_G (2), c3=C_G∖C_H (1), c4=C_H∖C_G (1), P2∩P3 = α∪γ,
private parts 10/11/12/12, core (union of pairwise intersections) 16 points.
(iv) Propagation of K4s: P0 is a (P1,P2)-single of type v; a (P1,P2)-single Y of type c3 has |Y∩P0| = a'+c' with
a' = |Y∩(w∪m3)| ≥ 2, c' = |Y∩(α∪a3)| ≥ 2 (NT); whenever |Y∩P0| = 5, {P1,P2,P0,Y} is again a (3,2,1,1)-K4.

## Wave 7 triangle (continued; §7.1–7.2 are above, before the 'Wave 7 Case N' section)
### 7.3 Lemma CP' (general form, PROVED) and the trace core model: CASE I CLOSED modulo a certified finite check
**W7-5 (CP').** If Q, X1, X2 pairwise meet in exactly 5 and Q∩X1∩X2 = {p}, then every edge F with p ∉ F satisfies
  |F∩Q ∖ (X1∪X2)| ≤ |F∩(X1∩X2)∖Q| − 1.
*Proof.* As W7-4 with C := (X1∩X2)∖Q (4 points): |Q∪X1∪X2| = 49, {Q,X1,X2,F} has empty intersection so
|F∩(Q∪X1∪X2)| ≤ 9; F∩Q, F∩C, F∩(X_i∖(Q∪C)) are disjoint, |F∩(X_i∖(Q∪C))| ≥ 5 − |F∩C| − |F∩Q∩X_i|. ∎
General-r form: bound (4r − 5K − W) + |F∩C| (r=16: −1+z, r=22: 0+z). Literal check on both examples:
`r=16: triples=488, checks=17568, violations=0`; `r=22: triples=155, checks=34100, violations=0` (w7_check_examples.py).

**The edges used.** (all exist by R.2; their properties are Tri-0, Tri-2, W7-2, R.3)
* W^i_q (i=1,2,3, q∈Q_i): W∩ℓ_i = {q}; trace W∩Q = {q}∪A, A ⊂ Q∖ℓ_i, |A| = 4; K_W := W∩C0, e := |K_W| ∈ {3,4};
  if e = 3, W∩O_i = {o_W} (one point), W misses m_W ∈ C0; |A∩ℓ_j| + e ≥ 5 (j≠i). W∩P_i = {q}∪K_W∪(W∩O_i) (5 points).
* Y^{ab}_c (each base pair (a,b), third index k, each c ∈ C0): Y∩(C0∪{x_ab}) = {c}; x_ak, x_bk ∈ Y; Y∩(Q_k∪Q_*) = ∅;
  3 ≤ |Y∩Q_a|+|Y∩Q_b| ≤ 4; |Y∩P_a| = 5, so |Y∩O_a| = 3 − |Y∩Q_a|.
**Relations used.**
* (CP) CP' for the triple (Q,P_i,W^i_q) [pairwise 5, Q∩P_i∩W = {q}, (P_i∩W)∖Q = K_W ∪ (W∩O_i)] applied to F = Y ∌ q:
  |Y∩Q ∖ (ℓ_i ∪ {q} ∪ A)| ≤ [c ∈ K_W] + [o_W ∈ Y] − 1.
* (A) For W of index k and the complementary pair (a,b): o_W ∈ O_k lies outside P_a∪P_b, and the outside parts of the
  (P_a,P_b)-singles Y^{ab}_c (different types c) are pairwise disjoint (Lemma S(a)), so o_W lies in at most one Y^{ab}_c.
* (O) o_W ∈ Y requires e_W = 3; if W has index a ∈ {a,b} then o_W ∈ Y requires |Y∩O_a| ≥ 1, i.e. |Y∩Q_a| ≤ 2.
**Hand step (I).** For W = W^k_q and Y = Y^{ab}_c (q ∉ Y since Y∩Q_k = ∅): Y∩Q∖(ℓ_k∪{q}∪A) = S_c∖A with
S_c := Y∩(Q_a∪Q_b), |S_c| ≥ 3. If e = 4 the bound is 0. If e = 3, at c = m_W the bound is [o_W∈Y^{ab}_m] − 1, so o_W ∈ Y^{ab}_m
and S_m ⊂ A; by (A) o_W ∉ Y^{ab}_c for c ≠ m, so the bound is 0 again. Hence **S_c ⊂ A^k_q for all c ∈ C0 and q ∈ Q_k**:
the A-part of every W^k_q contains U_k := ∪_c S_c (≥ 3 points of Q_a∪Q_b), leaving at most one free point.
**Hand step (II).** For W = W^a_q and Y = Y^{ab}_c ∌ q: |({x_bk} ∪ (Y∩Q_b)) ∖ A^a_q| ≤ [c∈K_W] + [o_W∈Y] − 1 ≤ 1, and since
x_bk ∉ U_a, x_bk ∈ A^a_q forces A^a_q = U_a ∪ {x_bk} with |U_a| = 3.
**COMPUTED (certified) finishing step.** The finite system {W-facts, Y-facts, (CP) for all 9×12 pairs (W,Y), (A), (O)} on the
21 points of Q is UNSATISFIABLE:
* pysat/CaDiCaL encoding work/e616/t21/w7_trace3.py with W7FLAGS=A,c3 (only these constraints are active; the optional
  groups inter/Sd/D/cpW/cpcond/tri are OFF): UNSAT; CNF w7_core_A_c3.cnf (23764 vars, 61564 clauses), DRAT proof
  w7_core_A_c3.drat, **drat-trim: s VERIFIED** (5559-clause core).
* independent CP-SAT re-encoding work/e616/t21/w7_core.py (written separately from the constraint list above): INFEASIBLE.
  Controls (same file): dropping (A) → FEASIBLE; using only 3 of the 4 values of c → FEASIBLE. So the contradiction
  genuinely uses (A) and all four points of C0, and the encodings are not vacuous.
* Under the extra hypothesis H4 (all e = 4) the system is UNSAT even without (A) (w7_trace.py / w7_trace2.py).
**Conclusion (Theorem W7-I, computer-assisted): Case I (triangle) is impossible at r = 21.** Proof = Tri-0, Tri-2, W7-2,
W7-5, Lemma S(a), R.2, R.3 (all by hand) + the certified UNSAT finite check. Hand proof of the finite check: open (§7.4).

### 7.4 HAND PROOF of the finite step — Theorem W7-I is now fully human (2026-10-15 ~09:40 EDT)
Notation of 7.3. For a base pair (a,b) with third index k write Y_a := Y∩Q_a, Y_b := Y∩Q_b for Y = Y^{ab}_c.
U_k := ∪_{c∈C0} Y^{ab}_c ∩ (Q_a∪Q_b) ⊂ Q_a∪Q_b. For q ∈ Q_i put c*(q) := m_q if e(W^i_q) = 3, and c*(q) := any c if e = 4.
Ingredients actually used: Tri-0; Tri-2 (x_ak, x_bk ∈ Y^{ab}_c; Y∩(Q_k∪Q_*) = ∅; x_ab ∉ Y); Lemma A (|Y∩Q| ≥ 5, hence
|Y_a|+|Y_b| ≥ 3); W7-2 (e ∈ {3,4}; e = 3 ⇒ exactly one point o in O_i); CP' (W7-5); Lemma S(a) for (A); R.2, R.3.
(The S(b) inequalities |A∩ℓ_j| + e ≥ 5 and (O) are NOT needed.)

**Step 0 = (I)** (7.3): A^k_q ⊇ U_k for every q ∈ Q_k; so |U_k| ∈ {3,4}. Call k *tight* if |U_k| = 3; then (|S_c| ≥ 3)
Y^{ab}_c ∩ (Q_a∪Q_b) = U_k for EVERY c (constant in c).
**Step 1 (hard hit).** Let q ∈ Q_a with q ∉ Y^{ab}_{c*(q)}. Then a is tight, A^a_q = U_a ∪ {x_bk}, and Y^{ab}_{c*(q)} ∩ Q_b ⊂ U_a.
*Proof.* CP' for (Q,P_a,W^a_q) and F = Y^{ab}_{c*}: F∩Q∖(ℓ_a∪{q}∪A^a_q) = ({x_bk}∪Y_b)∖A^a_q (x_bk ∈ Y by Tri-2), bound
[c*∈K_W] + [o_W∈F] − 1 which is 0 if e = 4 and [o_W ∈ F] − 1 ≤ 0 if e = 3 (c* = m_W ∉ K_W). So {x_bk} ∪ Y_b ⊂ A^a_q.
A^a_q ⊇ U_a (Step 0), U_a ⊂ Q_b∪Q_k ∌ x_bk, |U_a| ≥ 3, |A^a_q| = 4: so |U_a| = 3, A^a_q = U_a∪{x_bk}, Y_b ⊂ U_a. ∎
(Same with the pair (a,k) and Y∩Q_k.)
**Step 2 (non-tight index).** If k is not tight then for every q ∈ Q_k: q ∈ Y^{ka}_{c*(q)} and q ∈ Y^{kb}_{c*(q)}.
*Proof.* A^k_q = U_k (4 points) ∌ x_ab. If q ∉ Y := Y^{kb}_{c*}: CP' gives |({x_ab}∪(Y∩Q_b))∖A^k_q| ≤ 0, but x_ab ∈ Y∖A. ∎
**Step 3 (no index is non-tight).** Suppose k is not tight. U_k ⊂ Q_a∪Q_b has 4 points, so some d ∈ {a,b} has
|U_k∩Q_d| ≤ 2; let d' be the other one. (i) d is tight: a point q ∈ Q_d∖U_k lies in no Y^{dd'}_c, so Step 1 applies.
(ii) U_d = Q_k: d tight ⇒ Y^{d'k}_c ∩ (Q_{d'}∪Q_k) = U_d for all c; by Step 2 every q ∈ Q_k lies in Y^{kd'}_{c*(q)}, so
Q_k ⊂ U_d, and |U_d| = 3. (iii) Step 1 for that q gives Y^{dd'}_{c*}∩Q_{d'} ⊂ U_d∩Q_{d'} = ∅, so |Y^{dd'}_{c*}∩Q_d| ≥ 3; but
Y^{dd'}_{c*}∩Q_d ⊂ U_k∩Q_d has ≤ 2 points. Contradiction. ∎
**Step 4 (not all indices tight).** Suppose all three are tight; put u_{ka} := |U_k∩Q_a|, so u_{ka} + u_{kb} = 3.
(★) u_{ka} ≤ 2 ⇒ U_k∩Q_b ⊂ U_a∩Q_b. [A point q ∈ Q_a∖U_k lies in no Y^{ab}_c (constant traces); Step 1 gives
Y^{ab}_{c*}∩Q_b ⊂ U_a, and Y^{ab}_{c*}∩Q_b = U_k∩Q_b.]
(i) If all six u's are in {1,2}: (★) applied to k and to a gives U_k∩Q_b = U_a∩Q_b for every b and both other indices,
so s_b := |U_·∩Q_b| is well defined and s_a + s_b = 3 for all three pairs: s = 3/2, impossible.
(ii) Else some u_{ka} = 3, u_{kb} = 0. (★) for u_{kb} ≤ 2: Q_a = U_k∩Q_a ⊂ U_b, so u_{ba} = 3, u_{bk} = 0. If u_{ab} ≤ 2,
(★) gives U_a∩Q_k ⊂ U_b∩Q_k = ∅, so u_{ak} = 0, u_{ab} = 3: contradiction. So u_{ab} = 3, u_{ak} = 0, and (★) gives
U_a∩Q_b ⊂ U_k∩Q_b = ∅: contradiction. ∎
Steps 3–4 exhaust all cases. **Theorem W7-I (PROVED, by hand): Case I (triangle) is impossible at r = 21.**
The SAT/DRAT certificate (7.3) and the independent CP-SAT model agree and remain as a cross-check.
**Consequences.** By §6.6 and W6-U: a counterexample must contain a 5-pair with two singles of different types whose
(|A∩A'|, |C∩C'|) ∈ {(2,3),(3,2),(2,4),(4,2),(3,3),(3,4),(4,3)}, and NO triangle anywhere (Case N only).
t(21) = 4 ⟺ Case N is impossible.
**Honesty notes.** (1) The proof uses Tri-2 exactly as re-derived in §6.1 (re-checked in this wave: x_ik ∈ Y via
{Q,P_i,P_k,Y}; Y∩(Q_k∪Q_*) = ∅ via R.3 against Q). (2) Lemma A and R.2/R.3 as in §1. (3) No step depends on r = 21 except
through the slack −1 in CP' (r=16 has the same slack; r=22 has slack 0, where Step 1's bound becomes ≤ 1 and the argument
breaks — consistent with H(22,13,9)); the examples contain no triangle, so the theorem does not contradict them.
(4) Not yet independently refereed; a second reader should re-check Step 0 (the only use of (A)).
**Hint for Case N:** the same mechanism (CP' with Q-triples that are pairwise 5 and meet in one point; Lemma S(a)
disjointness to pin o-points; the "tight/non-tight U" dichotomy) should be tried on the K4 configuration of Case N
(a,c) = (2,3) (all six pairs exactly 5, §2026-10-15 06:14 note), where CP' applies to every triple with a 1-point
triple intersection.

#### Script sources (Wave 7)
* work/e616/t21/w7_trace3.py — pysat model M3 (flags; the certificate used W7FLAGS=A,c3). Kept in the workspace;
  constraint list is its docstring (= 7.3 list + optional groups).
* work/e616/t21/w7_core.py — independent CP-SAT core model (source below).
* work/e616/t21/w7_check_examples.py — CP' literal check on H(16,10,7), H(22,13,9).
* certificate: work/e616/t21/w7_core_A_c3.cnf + .drat, checked with work/e616/tools/drat-trim (VERIFIED).
```python
r"""W7 core finite model (independent CP-SAT re-encoding of the part of M3 that is needed).
Points of Q: x12=0, x13=1, x23=2, Q1={3,4,5}, Q2={6,7,8}, Q3={9,10,11}, Q*={12..20}.  C0 = {0,1,2,3} (labels c).
Edges: W[k,q] (k=1..3, q in Q_k): A-part A (4-subset of Q \ l_k), e in {3,4}, m (missing C0 label if e=3), o (exists iff e=3).
       Y[a,b,c]: Q-trace.  oin[Y,W] = (o_W in Y).
Constraints:
 (W)  |A & l_j| >= 1, and >= 2 if e = 3                          [W7-2 / Lemma S(b) vs P_j]
 (Y)  x_ak, x_bk in Y; x_ab, Q_k, Q_* not in Y; 3 <= |Y&(Q_a u Q_b)| <= 4   [Tri-2]
 (CP) for W = W[i,q] and Y with q notin Y:  |Y \ (l_i u {q} u A)| <= [c in K_W] + oin[Y,W] - 1     [W7-5 with (P_i,W)]
 (A)  for W of index k and the complementary pair (a,b): sum_c oin[Y[a,b,c],W] <= 1          [Lemma S(a) at (P_a,P_b)]
 (O)  oin[Y,W] -> e_W = 3;  if W has index a in {a,b} of Y: oin -> |Y & Q_a| <= 2          [|Y&O_a| = 3-|Y&Q_a|]
Usage: python3 w7_core.py [extra-claim-name]
"""
import sys, itertools
sys.path.append("work/e616/pylib")
from ortools.sat.python import cp_model
X = {(1,2): 0, (1,3): 1, (2,3): 2}
Qi = {1: [3,4,5], 2: [6,7,8], 3: [9,10,11]}; Qs = list(range(12, 21)); PTS = range(21)
x = lambda i, j: X[tuple(sorted((i, j)))]
ell = {i: set([x(i, j) for j in (1,2,3) if j != i] + Qi[i]) for i in (1,2,3)}
def build(extra=None, useA=True, ncs=4):
    m = cp_model.CpModel()
    W = {}
    for k in (1,2,3):
        for q in Qi[k]:
            A = {p: m.NewBoolVar('') for p in PTS}
            for p in ell[k]: m.Add(A[p] == 0)
            m.Add(sum(A.values()) == 4)
            e3 = m.NewBoolVar(''); K = [m.NewBoolVar('') for c in range(4)]
            m.Add(sum(K) == 3).OnlyEnforceIf(e3); m.Add(sum(K) == 4).OnlyEnforceIf(e3.Not())
            for j in (1,2,3):
                if j == k: continue
                m.Add(sum(A[p] for p in ell[j]) >= 1); m.Add(sum(A[p] for p in ell[j]) >= 2).OnlyEnforceIf(e3)
            W[k, q] = dict(A=A, e3=e3, K=K, k=k, q=q)
    Y = {}
    for (a, b) in [(1,2), (1,3), (2,3)]:
        k = 6 - a - b
        for c in range(ncs):
            t = {p: m.NewBoolVar('') for p in PTS}
            m.Add(t[x(a, k)] == 1); m.Add(t[x(b, k)] == 1); m.Add(t[x(a, b)] == 0)
            for p in Qi[k] + Qs: m.Add(t[p] == 0)
            s = sum(t[p] for p in Qi[a] + Qi[b]); m.Add(s >= 3); m.Add(s <= 4)
            Y[a, b, c] = dict(t=t, a=a, b=b, k=k, c=c)
    oin = {}
    for yk, y in Y.items():
        for wk, w in W.items():
            o = m.NewBoolVar(''); oin[yk, wk] = o
            m.AddImplication(o, w['e3'])
            if w['k'] in (y['a'], y['b']):
                m.Add(sum(y['t'][p] for p in Qi[w['k']]) <= 2).OnlyEnforceIf(o)
            # (CP)
            i, q = w['k'], w['q']
            outs = []
            for p in PTS:
                if p in ell[i] or p == q: continue
                v = m.NewBoolVar(''); outs.append(v)
                # v = t[p] and not A[p]
                m.AddBoolAnd([y['t'][p], w['A'][p].Not()]).OnlyEnforceIf(v)
                m.AddBoolOr([y['t'][p].Not(), w['A'][p]]).OnlyEnforceIf(v.Not())
            act = y['t'][q].Not()
            m.Add(sum(outs) <= w['K'][y['c']] + o - 1).OnlyEnforceIf(act)
    for wk, w in W.items():
        k = w['k']; a, b = [i for i in (1,2,3) if i != k]
        if useA: m.Add(sum(oin[(a, b, c), wk] for c in range(ncs)) <= 1)
    if extra: extra(m, W, Y, oin)
    return m
def run(extra=None, tl=100, **kw):
    m = build(extra, **kw); s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = tl; s.parameters.num_workers = 2
    return s.StatusName(s.Solve(m))
if __name__ == '__main__':
    print('core model:', run())
    print('control without (A):', run(useA=False))
    print('control with only 3 values of c:', run(ncs=3))
```
Sanity check of Step 4: work/e616/t21/w7_step4_check.py brute-forces all 20³ triples (U1,U2,U3) of 3-sets and finds
**0** satisfying (★) — agrees with the hand argument. Background CP-SAT probe w7_wc3g (|W∩C0| = 3, k=9) was UNKNOWN after
900 s and has been killed; it is superseded by 7.4.

## Wave 7 Case N (continued; N.0 is above, before 'Wave 7 triangle (continued)')
### N.1 Further proved facts (Case N, K4 = (3,2,1,1), notation of N.0 (iii))
* **OO (outside overlap, general, = L on {X,Y,Z,Z'}).** (X,Y) a 5-pair, N = X∩Y, Z,Z' edges with Z∩Z'∩N = ∅. With
  slack(Z) := 9 − |Z∩(X∪Y)| (≥ 0 by D1): |Z∩Z'∖(X∪Y)| ≤ slack(Z) + slack(Z'). (Singles have slack 0, so cross-type
  singles have disjoint outsides = R.3.)
* **49-triple lemma (general).** (X,Y) 5-pair, F a single of type y: for every edge Z ∌ y,
  |Z∩(N∖y)| + |Z∩A_F| + |Z∩C_F| ≥ 6 (L on {X,Y,F,Z}, |X∪Y∪F| = 49, plus Lemma A three times).
* In the K4, pair (G,H) = (P2,P3) has N = α∪γ, E1 multi (Q=α, slack 1), E2 multi (Q=γ, slack 2); OO for (E1,E2) is
  tight: E1∩E2∖(G∪H) = m3, 3 = 1+2. For a (G,H)-single F_y of type y∈γ: |F_y∩{v,a3,w,a4}| ≥ 4 and
  |F_y∩(m3∪O0)| ≤ 1. For a (G,H)-single F_x of type x∈α: |F_x∩{v,c3,w,c4}| ≥ 3 and |F_x∩(m3∪O1)| ≤ 2.
  (49-triple lemma with Z = E1 resp. E2, and OO.)  N.0(iv): Y∩(a4∪O0) = ∅ for the (P1,P2)-single Y of type c3 is S(a).

### N.2 Trace systems: a reformulation, and why a one-sided proof cannot work (PROVED + COMPUTED)
For an edge Q let 𝒯_Q = {Q∩X : |Q∩X| = 5} (traces of the 5-pair partners of Q, 5-subsets of the 21-set Q). Then
**T1** 𝒯_Q is intersecting (F1); **T2** for τ∈𝒯_Q and x∈τ some τ'∈𝒯_Q has τ∩τ' = {x} (R.2: the single F of type x
of (Q,X) has |F∩Q| = 5 by R.3); **T3 (= no triangle)**: no three traces pairwise meeting in one point with empty
common intersection. Moreover a trace τ' with |τ'∩τ| = 1 is exactly a single of the 5-pair (Q,X), and the
A-parts of two singles of (Q,X) of types x≠y are τ1∖{x}, τ2∖{y}; so **a = |τ1∩τ2|** and "(Q,X) has uniform A-parts"
⟺ "tangents to τ at distinct points meet in exactly 4". Case N with a ∈ {2,3} (WLOG, swapping E1,E2 if a = 4)
⟺ some 𝒯_{E1} has two tangents of one trace at distinct points meeting in 2 or 3 points.
*Hoped-for lemma (would finish Case N via W6-U, applied on both sides):* T1+T2+T3 ⟹ tangents at distinct points
meet in 4. **FALSE** as a pure set-system statement: work/e616/t21/tracefam.py (pysat, one boolean per 5-subset of
an n-set; T1, closure T2, all triangles forbidden) finds for n = 10, 11, 12 with seed M={0..4}, τ_G={0,5,6,7,8},
τ_H={1,6,7,8,9} (a = 3) a system of 126 traces; independently re-verified (tracefam_check.py → tf10.out): T1, T2,
T3 hold, one set from each complementary pair of [10], point degrees [73,67,71,71,71,71,67,67,67,5] — it is the
uniform "all 5-subsets of a 9-set" system with 5 members swapped for their complements through point 9. So the
non-uniformity is invisible to any argument that only looks at traces on one edge; a proof must use the C-side
(two edges) or outside parts. (The small-closed-system SAT tracesys.py, k ≤ 10 traces, is UNSAT for a = 2,3,4 alike —
closed systems are just large; uninformative.)
Examples check (w7N_check_examples.py): r=16 H(16,10,7): 35 traces, T1–T3 true, tangents uniform, no K4 through E0;
r=22 H(22,13,9): 126 traces, same. (No K4 can exist there at all: pairwise-K q-subsets of a k-set need pairwise disjoint
complements, 4·3 > 10, 4·4 > 13.)

### N.3 Region model on the K4 base (COMPUTED, all FEASIBLE — no local contradiction)
work/e616/t21/k4model.py (base regions) and k4m2.py (base split into named points), constraints: |E|=21, Lemma A, L on
every subfamily containing a new edge, D1, R3a (a single of a 5-pair meets both edges in exactly 5), NT (no triangle:
cross-type singles of every 5-pair in the model have a,c ≥ 2). Witnesses: singles S{ij}_x = edge avoiding M_ij∖{x}.
* every 1, 2 and 3 region-level single witnesses (k4sweep.py, 17 patterns, all 1140 triples): FEASIBLE;
* CEGAR with 4-point max-degree covers (k4cegar.py): FEASIBLE through k = 9 (554 s), k = 10 not finished (killed);
* named-point sets (k4m2run.py / k4batch.py): all five (G,H)-singles; all five (E2,G)-singles; all five (E1,G)-singles;
  three (E1,E2)-singles of types m + one γ- and one α-single of (G,H); and four mixed 4–5 sets: all FEASIBLE
  (7–97 s). In the five-(G,H)-singles solution all five contain v (k4_gh5.log).
So Case N (2,3) is locally consistent with ≥ 9 edges, exactly like the triangle (§6.4, 7.2).

### N.4 Dichotomy for Case N (PROVED)
Let (E1,E2) be a 5-pair, G a single of type v, p ∈ A_G, and W a Lemma-T witness (W∩({v}∪A_G) = {p}, a single of the
5-pair (E1,G)). In Case N: k := |W∩M| ≥ 2 (else triangle), W∩C ⊆ C_G (Lemma T), c' := |W∩C_G| ≥ 2 (NT at (E1,G),
C-side, against the type-v single E2), so |W∩E2| = k + c' ≥ 5 (and ≤ 9 by D1).
**If |W∩E2| = 5 then {E1,G,E2,W} is a (3,2,1,1)-K4** (all six pairs 5: E1G, E1E2, GE2 (R.3), WE1, WG (R.3), WE2;
E1∩G∩E2 = {v} ∌ W; triples {v}, {p}, W∩M (k), W∩C_G (5−k), k ∈ {2,3}).
Hence Case N = **(N-K4)** some (3,2,1,1)-K4 exists [contains (a,c) ∈ {(2,3),(3,2)}] ∪ **(N-noK4)** no K4: every pair
of cross-type singles of every 5-pair has a+c ≥ 6, and every Lemma-T witness W has k + |W∩C_G| ≥ 6, i.e. meets the
other edge in ≥ 6. Any Case-N class (2,4),(3,3),(3,4) either contains a K4 (via some witness) or lies in N-noK4.
So Case N is closed iff (I) no (3,2,1,1)-K4 exists and (II) N-noK4 is impossible. Neither is proved.

### N.5 Status of Case N after Wave 7: OPEN.
Proved: N.0 (K4 verification + general K4 facts), N.1, N.2 (trace reformulation T1–T3), N.4 (dichotomy).
Negative (computed): N.2 (one-sided trace systems admit non-uniform tangents, 126-set example on 10 points),
N.3 (K4 region model feasible to k = 9; named 5-witness sets feasible). Suggested next step: a TWO-sided trace system
(traces on E1 and on E2 of the same edges, linked by Lemma T's W∩C ⊆ C_G and OO) — the one-sided version is provably
too weak; or a W6-U-style closure for N-noK4 where every witness meets the other edge in ≥ 6.

### N.6 Script sources (Wave 7 Case N)
#### work/e616/t21/k4verify.py
```python
"""Verify the K4 configuration claim (06:14 run) concretely: build E1=M+A, E2=M+C, G (type v), H (type w) with
|A_G&A_H|=a, |C_G&C_H|=c, O_G, O_H disjoint 12-sets (Lemma R.3/S(a)); print pairwise/triple sizes and union."""
import itertools
for a, c in [(2,3),(3,2),(2,4),(4,2),(3,3),(3,4),(4,3),(1,4)]:
    M = list(range(5)); A = list(range(5,21)); C = list(range(21,37))
    E1, E2 = set(M+A), set(M+C)
    G = {0} | set(A[0:4]) | set(C[0:4]) | set(range(100,112))
    H = {1} | set(A[4-a:8-a]) | set(C[4-c:8-c]) | set(range(200,212))
    F = [E1,E2,G,H]; assert all(len(X)==21 for X in F)
    pr = [len(F[i]&F[j]) for i,j in itertools.combinations(range(4),2)]
    tr = [len(F[i]&F[j]&F[k]) for i,j,k in itertools.combinations(range(4),3)]
    print((a,c), 'pairs', pr, 'triples', tr, 'quad', len(E1&E2&G&H), 'union', len(E1|E2|G|H))
```
#### work/e616/t21/k4model.py
```python
"""Wave 7 Case N: region model with a fixed K4 configuration as base.
Base edges P0..P3 (bits 0..3), pairwise |Pi&Pj| = 5, empty 4-fold intersection, triple sizes tt[l] = |cap_{i!=l} Pi|
(sum 7).  Pair-private p_ij = 5 - t_ijk - t_ijl, outside O_i = 21 - sum(triples containing i) - sum_j p_ij.
New edges 4..k-1.  Region c[T] for T (k-bit mask) whose low 4 bits are a nonempty-base region or 0 (outside).
TRUE constraints at r=21 used (all proved in docs/proof-notes.md section 1/6):
  |E|=21; |Ei&Ej|>=5 (Lemma A); L on every subfamily (>=3 edges, containing a new edge);
  D1: (i,j) 5-pair, M_ij not inside E_l  ->  |E_l & (E_i|E_j)| <= 9;
  R3a: (i,j) 5-pair, |E_k & M_ij| = 1  ->  |E_k & E_i| = |E_k & E_j| = 5   (R.2+R.3: singles of >=2 types exist);
  NT (Case N hypothesis, no triangle): (i,j) 5-pair, k,l singles of (i,j) of different types
      -> |E_k&E_l&(E_i\\E_j)| >= 2 and |E_k&E_l&(E_j\\E_i)| >= 2   (this also contains Lemma S(c)).
Witness patterns: pats[e] = list of (pred, mu): pred(T) on regions of earlier edges; if all groups have >= mu
points then edge e avoids >= mu points of each group (sum mu <= 4, tau >= 5).
INFEASIBLE => the hypothesised configuration cannot occur in a counterexample."""
import itertools, time, sys
sys.path.append("work/e616/pylib")
from ortools.sat.python import cp_model

def base_sizes(tt, r=21):
    # tt[l] = size of triple intersection of the three P's other than P_l
    sz = {}
    for l in range(4):
        sz[15 ^ (1 << l)] = tt[l]
    for i, j in itertools.combinations(range(4), 2):
        k, l = [x for x in range(4) if x not in (i, j)]
        sz[(1 << i) | (1 << j)] = 5 - tt[l] - tt[k]
    for i in range(4):
        sz[1 << i] = r - sum(tt[l] for l in range(4) if l != i) - sum(5 - tt[l] - tt[k]
                     for j in range(4) if j != i for k, l in [tuple(x for x in range(4) if x not in (i, j))])
    sz[15] = 0
    assert all(v >= 0 for v in sz.values()), sz
    return sz

def build(k, tt, pats, r=21, K=5, W=60, nt=True, r3a=True, d1=True, extra=None):
    bs = base_sizes(tt, r)
    allowed = [b for b, v in bs.items() if v > 0] + [0]
    m = cp_model.CpModel()
    regs = [T for T in range(1, 1 << k) if (T & 15) in allowed]
    c = {T: m.NewIntVar(0, r, '') for T in regs}
    S = lambda pred: sum(c[T] for T in regs if pred(T))
    for b in allowed:
        if b: m.Add(S(lambda T: (T & 15) == b) == bs[b])
    for i in range(4, k):
        m.Add(S(lambda T: T >> i & 1) == r)
    pairK = {}
    for i, j in itertools.combinations(range(k), 2):
        I = (1 << i) | (1 << j)
        e = S(lambda T: T & I == I)
        if j < 4:
            pairK[(i, j)] = True; continue
        m.Add(e >= K)
        f = m.NewBoolVar(''); m.Add(e == K).OnlyEnforceIf(f); m.Add(e >= K + 1).OnlyEnforceIf(f.Not()); pairK[(i, j)] = f
    for I in range(1, 1 << k):
        if bin(I).count('1') < 3 or (I >> 4) == 0: continue
        b = m.NewBoolVar('')
        m.Add(S(lambda T: T & I == I) >= 1).OnlyEnforceIf(b)
        m.Add(S(lambda T: T & I) >= W + 1).OnlyEnforceIf(b.Not())
    lit = lambda f: [] if f is True else [f]
    # singles indicator s[(i,j,l)] : |E_l & M_ij| == 1
    sing = {}
    for (i, j), f in pairK.items():
        I = (1 << i) | (1 << j)
        for l in range(k):
            if l in (i, j): continue
            inter = S(lambda T: T & I == I and T >> l & 1)
            if max(i, j, l) < 4:
                sing[(i, j, l)] = (bs[I | (1 << l)] == 1); continue
            s = m.NewBoolVar(''); m.Add(inter == 1).OnlyEnforceIf(s); m.Add(inter != 1).OnlyEnforceIf(s.Not())
            sing[(i, j, l)] = s
            if d1:
                g = m.NewBoolVar('')
                miss = S(lambda T: T & I == I and not (T >> l & 1))
                m.Add(miss >= 1).OnlyEnforceIf(g); m.Add(miss == 0).OnlyEnforceIf(g.Not())
                m.Add(S(lambda T: (T >> l & 1) and (T & I)) <= 4 * r - W - 3 * K).OnlyEnforceIf(lit(f) + [g])
            if r3a:
                for q in (i, j):
                    Q = (1 << q) | (1 << l)
                    m.Add(S(lambda T: T & Q == Q) == K).OnlyEnforceIf(lit(f) + [s])
    if nt:
        for (i, j), f in pairK.items():
            I = (1 << i) | (1 << j)
            for l1, l2 in itertools.combinations([x for x in range(k) if x not in (i, j)], 2):
                if max(i, j, l1, l2) < 4: continue
                s1, s2 = sing[(i, j, l1)], sing[(i, j, l2)]
                if s1 is False or s2 is False: continue
                L = (1 << l1) | (1 << l2)
                d = m.NewBoolVar('')  # different types: E_l1 & E_l2 & M_ij empty
                x = S(lambda T: T & (I | L) == (I | L))
                m.Add(x == 0).OnlyEnforceIf(d); m.Add(x >= 1).OnlyEnforceIf(d.Not())
                cond = lit(f) + [z for z in (s1, s2) if z is not True] + [d]
                for q, o in ((i, j), (j, i)):
                    m.Add(S(lambda T: T & (L | (1 << q)) == (L | (1 << q)) and not (T >> o & 1)) >= 2).OnlyEnforceIf(cond)
    for e, pat in pats.items():
        ante = []
        for pred, mu in pat:
            a = m.NewBoolVar('')
            s_ = S(lambda T: pred(T & ((1 << e) - 1)))
            m.Add(s_ >= mu).OnlyEnforceIf(a); m.Add(s_ <= mu - 1).OnlyEnforceIf(a.Not()); ante.append(a)
        allA = m.NewBoolVar(''); m.AddBoolAnd(ante).OnlyEnforceIf(allA); m.AddBoolOr([x.Not() for x in ante]).OnlyEnforceIf(allA.Not())
        for pred, mu in pat:
            m.Add(S(lambda T: pred(T & ((1 << e) - 1)) and not (T >> e & 1)) >= mu).OnlyEnforceIf(allA)
    if extra: extra(m, c, regs, S)
    return m, c, regs

def solve(k, tt, pats, tl=100, workers=2, **kw):
    t0 = time.time(); m, c, regs = build(k, tt, pats, **kw); tb = time.time() - t0
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = tl; s.parameters.num_workers = workers
    st = s.Solve(m); name = s.StatusName(st)
    sol = {T: s.Value(c[T]) for T in regs if s.Value(c[T])} if st in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None
    return name, sol, time.time() - t0, tb

def show(k, sol):
    return {bin(T)[2:].zfill(k)[::-1]: v for T, v in sorted(sol.items())}

def reg(b):  # predicate: vertex lies in base region b (any membership in earlier new edges)
    return lambda T: (T & 15) == b
```
#### work/e616/t21/k4m2.py
```python
"""Wave 7 Case N, model v2: like k4model.py but the fixed base is a list of ATOMS (refinement of the base regions,
so individual points such as each m3-point can be named).  atoms: list of (name, basemask(4 bits over P0..P3), size).
Region var c[(a, S)] = #vertices in atom a lying in exactly the new edges S (S = bitmask over new edges 0..n-1).
Same TRUE constraints as k4model.py (Lemma A, L on all subfamilies with a new edge, D1, R3a, NT).
pats[e] = list of (atomset, mu): edge e avoids >= mu points of the union of those atoms (unconditional: mu <= size);
sum mu <= 4."""
import itertools, time, sys
sys.path.append("work/e616/pylib")
from ortools.sat.python import cp_model
from k4model import base_sizes

NAMES = {7: 'v', 11: 'w', 13: 'al', 14: 'ga', 3: 'm', 5: 'a3', 9: 'a4', 6: 'c3', 10: 'c4', 12: 'p23',
         1: 'O0', 2: 'O1', 4: 'O2', 8: 'O3', 0: 'out'}

def atoms_from(tt, split=()):
    """split: base masks whose points are made individual atoms (name+index)."""
    bs = base_sizes(tt); at = []
    for b, sz in sorted(bs.items()):
        if sz == 0 or b == 15: continue
        if b in split:
            for i in range(sz): at.append((f'{NAMES[b]}{i}', b, 1))
        else: at.append((NAMES[b], b, sz))
    at.append(('out', 0, None))
    return at

def build(n, atoms, pats, r=21, K=5, W=60, nt=True, r3a=True, d1=True):
    k = 4 + n
    m = cp_model.CpModel()
    # full mask of a region: basemask | (S << 4)
    regs = [(ai, S) for ai in range(len(atoms)) for S in range(1 << n) if not (atoms[ai][1] == 0 and S == 0)]
    c = {R: m.NewIntVar(0, r, '') for R in regs}
    full = {R: atoms[R[0]][1] | (R[1] << 4) for R in regs}
    def S(pred): return sum(c[R] for R in regs if pred(full[R], R))
    for ai, (nm, b, sz) in enumerate(atoms):
        if sz is not None: m.Add(sum(c[(ai, s)] for s in range(1 << n)) == sz)
    for i in range(4, k):
        m.Add(S(lambda T, R: T >> i & 1) == r)
    pairK = {}
    bs = {}
    for nm, b, sz in atoms:
        if sz: bs[b] = bs.get(b, 0) + sz
    for i, j in itertools.combinations(range(k), 2):
        I = (1 << i) | (1 << j)
        if j < 4: pairK[(i, j)] = True; continue
        e = S(lambda T, R: T & I == I); m.Add(e >= K)
        f = m.NewBoolVar(''); m.Add(e == K).OnlyEnforceIf(f); m.Add(e >= K + 1).OnlyEnforceIf(f.Not()); pairK[(i, j)] = f
    for I in range(1, 1 << k):
        if bin(I).count('1') < 3 or (I >> 4) == 0: continue
        b = m.NewBoolVar('')
        m.Add(S(lambda T, R: T & I == I) >= 1).OnlyEnforceIf(b)
        m.Add(S(lambda T, R: T & I) >= W + 1).OnlyEnforceIf(b.Not())
    lit = lambda f: [] if f is True else [f]
    sing = {}
    for (i, j), f in pairK.items():
        I = (1 << i) | (1 << j)
        for l in range(k):
            if l in (i, j): continue
            if max(i, j, l) < 4:
                sing[(i, j, l)] = (bs.get(I | (1 << l), 0) == 1); continue
            inter = S(lambda T, R: T & I == I and T >> l & 1)
            s = m.NewBoolVar(''); m.Add(inter == 1).OnlyEnforceIf(s); m.Add(inter != 1).OnlyEnforceIf(s.Not())
            sing[(i, j, l)] = s
            if d1:
                g = m.NewBoolVar('')
                miss = S(lambda T, R: T & I == I and not (T >> l & 1))
                m.Add(miss >= 1).OnlyEnforceIf(g); m.Add(miss == 0).OnlyEnforceIf(g.Not())
                m.Add(S(lambda T, R: (T >> l & 1) and (T & I)) <= 4 * r - W - 3 * K).OnlyEnforceIf(lit(f) + [g])
            if r3a:
                for q in (i, j):
                    Q = (1 << q) | (1 << l)
                    m.Add(S(lambda T, R: T & Q == Q) == K).OnlyEnforceIf(lit(f) + [s])
    if nt:
        for (i, j), f in pairK.items():
            I = (1 << i) | (1 << j)
            for l1, l2 in itertools.combinations([x for x in range(k) if x not in (i, j)], 2):
                if max(i, j, l1, l2) < 4: continue
                s1, s2 = sing[(i, j, l1)], sing[(i, j, l2)]
                if s1 is False or s2 is False: continue
                L = (1 << l1) | (1 << l2)
                d = m.NewBoolVar('')
                x = S(lambda T, R: T & (I | L) == (I | L))
                m.Add(x == 0).OnlyEnforceIf(d); m.Add(x >= 1).OnlyEnforceIf(d.Not())
                cond = lit(f) + [z for z in (s1, s2) if z is not True] + [d]
                for q, o in ((i, j), (j, i)):
                    m.Add(S(lambda T, R: T & (L | (1 << q)) == (L | (1 << q)) and not (T >> o & 1)) >= 2).OnlyEnforceIf(cond)
    for e, pat in pats.items():
        assert sum(mu for _, mu in pat) <= 4
        for aset, mu in pat:
            m.Add(sum(c[(ai, s)] for ai in aset for s in range(1 << n) if not (s >> (e - 4) & 1)) >= mu)
    return m, c, regs

def solve(n, atoms, pats, tl=100, workers=2, **kw):
    t0 = time.time(); m, c, regs = build(n, atoms, pats, **kw)
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = tl; s.parameters.num_workers = workers
    st = s.Solve(m); name = s.StatusName(st)
    sol = {R: s.Value(c[R]) for R in regs if s.Value(c[R])} if st in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None
    return name, sol, time.time() - t0

def show(n, atoms, sol):
    out = {}
    for (ai, S), v in sol.items():
        out.setdefault(atoms[ai][0], []).append((''.join('1' if S >> e & 1 else '0' for e in range(n)), v))
    return out

def A(atoms, *names):
    return [i for i, a in enumerate(atoms) if a[0] in names]
```
#### work/e616/t21/k4m2run.py
```python
import sys, itertools, json
from k4m2 import *
tt = tuple(int(x) for x in sys.argv[1].split(','))
SPLIT = (7, 11, 13, 14, 3, 5, 9, 6, 10)
atoms = atoms_from(tt, SPLIT)
core = [(i, a) for i, a in enumerate(atoms) if a[1] in SPLIT]
WIT = {}
for i, j in itertools.combinations(range(4), 2):
    I = (1 << i) | (1 << j)
    Mij = [ai for ai, a in core if a[1] & I == I]
    for x in Mij:
        WIT[f'S{i}{j}_{atoms[x][0]}'] = [([y], 1) for y in Mij if y != x]
def run(names, tl=100):
    pats = {4 + e: WIT[nm] for e, nm in enumerate(names)}
    return solve(len(names), atoms, pats, tl=tl)
if __name__ == '__main__':
    names = sys.argv[2].split(','); tl = float(sys.argv[3]) if len(sys.argv) > 3 else 100
    st, sol, t = run(names, tl)
    print(names, st, f'{t:.1f}s', flush=True)
    if sol and '-v' in sys.argv: print(json.dumps(show(len(names), atoms, sol)))
```
#### work/e616/t21/tracefam.py
```python
"""Trace-system SAT over all 5-subsets of an n-set: boolean per 5-subset. T1 intersecting, T2 closure
(every member and every point of it has a tangent member meeting it exactly there), T3 no triangle.
Seed: tau={0..4}, tau1={0,5,6,7,8}, tau2={1}+(4-set meeting {5..8} in a points).  Usage: tracefam.py n a"""
import sys, itertools
sys.path.append("work/e616/pylib")
from pysat.solvers import Cadical153
n, a = int(sys.argv[1]), int(sys.argv[2])
S = [frozenset(c) for c in itertools.combinations(range(n), 5)]
idx = {s: i + 1 for i, s in enumerate(S)}
cl = []
for s, t in itertools.combinations(S, 2):
    if not (s & t): cl.append([-idx[s], -idx[t]])
# T2
by_pt_sets = {}
for s in S:
    for x in s:
        tang = [idx[t] for t in S if s & t == {x}]
        cl.append([-idx[s]] + tang)
# T3: triangles
cnt = 0
single = {}
for s in S:
    single[s] = [t for t in S if len(s & t) == 1]
for s in S:
    for t in single[s]:
        if idx[t] <= idx[s]: continue
        for u in single[t]:
            if idx[u] <= idx[t]: continue
            if len(s & u) == 1 and not (s & t & u):
                cl.append([-idx[s], -idx[t], -idx[u]]); cnt += 1
seed = [frozenset(range(5)), frozenset({0, 5, 6, 7, 8}), frozenset({1} | set(range(9 - a, 13 - a)))]
for s in seed: cl.append([idx[s]])
sol = Cadical153(bootstrap_with=cl); r = sol.solve()
print(f'n={n} a={a} sets={len(S)} triangles={cnt}', 'SAT' if r else 'UNSAT', flush=True)
if r:
    m = set(x for x in sol.get_model() if x > 0)
    fam = [sorted(s) for s in S if idx[s] in m]; print(len(fam), fam[:60])
```
#### work/e616/t21/w7N_check_examples.py
```python
"""Wave 7 Case N: literal checks on H(16,10,7) (r=16,K=4) and H(22,13,9) (r=22,K=5) of the trace-system facts
T1 (traces E1&X of K-pair partners X pairwise intersect), T2 (every trace has a tangent trace at each of its
points), T3 (no triangle of traces), and absence of K4 configurations (4 edges pairwise meeting in exactly K)."""
import itertools
def H(r, k, q):
    E = []; nxt = k
    for Y in itertools.combinations(range(k), q):
        E.append(frozenset(Y) | frozenset(range(nxt, nxt + r - q))); nxt += r - q
    return E
for (r, k, q, K) in [(16, 10, 7, 4), (22, 13, 9, 5)]:
    E = H(r, k, q); E1 = E[0]
    tr = sorted({E1 & X for X in E[1:] if len(E1 & X) == K}, key=sorted)
    T1 = all(a & b for a, b in itertools.combinations(tr, 2))
    T2 = all(any(s & t == {x} for t in tr) for s in tr for x in s)
    T3 = not any(len(a & b) == 1 and len(b & c) == 1 and len(a & c) == 1 and not (a & b & c)
                 for a, b, c in itertools.combinations(tr, 3))
    tang_equal = all((t1 - {x}) == (t2 - {y}) for s in tr for x, y in itertools.permutations(s, 2)
                     for t1 in tr if s & t1 == {x} for t2 in tr if s & t2 == {y})
    # K4: search among edges pairwise meeting in exactly K (cliques of size 4 in the K-graph through E[0])
    nb = [i for i in range(1, len(E)) if len(E[0] & E[i]) == K]
    k4 = any(len(E[i] & E[j]) == K and len(E[i] & E[l]) == K and len(E[j] & E[l]) == K and not (E[0] & E[i] & E[j] & E[l])
             for i, j, l in itertools.combinations(nb, 3))
    print(f'r={r}: traces={len(tr)} T1={T1} T2={T2} T3={T3} tangents-uniform={tang_equal} K4-through-E0={k4}')
```
Other scripts (variants, in work/e616/t21/): k4wit.py (region-level single patterns), k4sweep.py (all combos of size s), k4cegar.py (CEGAR, 4-point max-degree covers), k4batch.py (named sets), k4enum1.py/k4stats.py (enumerate one witness edge, per-region ranges), tracesys.py (closed k-trace SAT), tracefam_check.py. Logs: k4sweep_23_s3.log, k4cegar_23.log, k4batch_23.log, k4_gh5.log, tf10.out.

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
* The 17-edge version (+ 8 witnesses of G, with NKSLIM): **UNKNOWN** after 908 s (w8n_real24.log), on a CPU shared with other jobs. Not a result. (Without the J's the 13-edge version is FEASIBLE, see the first bullet.)
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

## Wave 9 propagation (2026-10-15, started ~15:20 EDT)
**Result: Case N is NOT closed, and the planned route "(P) + W6-U closure" has no local first step.** Below: three
proved lemmas (U1, P-red, OD), a sound S-closure computation showing that one uniform pair forces nothing new, and a
SAT computation showing that (P) is locally FALSE in the (3,2,1,1)-K4. No UNSAT claim was reached, so there is **no
DRAT certificate and no control in this wave** (controls only make sense for UNSAT). Notation for a **uniform** 5-pair
(X,Y): N = X∩Y, A = X∖N, C = Y∖N, every single has parts (A0, C0), F_z = a single of type z with outside O_z,
S = N ⊔ A0 ⊔ C0 (13 points).

### P9.1 Lemma U1 (PROVED; this is ZF-T* specialised to a uniform pair, recorded with a self-contained proof)
Every edge Z with Z∩A0 = ∅ has Z∩S = N∪C0, Z∩X = N (so Z∩A = ∅) and Z∩O_z = ∅ for every z. Symmetrically every
C0-avoider J has J∩S = N∪A0, J∩Y = N, J∩O_z = ∅. Hence (X,Z) and (J,Y) are again uniform 5-pairs with the same N and S.
*Proof.* (i) If z ∉ Z: {X,Y,F_z,Z} has empty intersection and |X∪Y∪F_z| = 49, so |Z∩(X∪Y∪F_z)| ≤ 9; but |Z∩X| ≥ 5,
|Z∩F_z| ≥ 5 and Z∩X∩F_z = Z∩({z}∪A0) = ∅. So N ⊂ Z. (ii) Z is a type-z single of the 5-pair (X,F_z), so by R.3
|Z∩X| = 5 (Z∩X = N) and |Z∩C0| + |Z∩O_z| = 4. (iii) For z ≠ z', {X,F_z,F_z',Z} has empty intersection
(X∩F_z∩F_z' = A0) and |X∪F_z∪F_z'| = 49, so 5 + |Z∩C0| + |Z∩O_z| + |Z∩O_z'| ≤ 9, i.e. |Z∩O_z'| = 0 for all z', and
|Z∩C0| = 4. ∎
Literal check (w9_check_examples.py): `r=16: uniform K-pairs=150/150, A0-avoiders checked=150, U1 violations=0`,
`r=22: … 150/150 …, U1 violations=0` (only Y itself avoids A0 there, so the check is near-trivial). PG(2,4) skeleton
(w9_check_pg.py): 231 5-pairs, **0 uniform**, so U1 is vacuous there.

### P9.2 Lemma P-red (PROVED): exactly what (P) asks, and what a violation looks like
Fix y ∈ N; (X,F_y) is a 5-pair with N' = {y}∪A0.
* (a) Its type-y singles are exactly the A0-avoiders (by U1 every A0-avoider contains y). By U1 they all have parts
  (N∖y, C0), the parts of Y. **So the type-y side of (X,F_y) is automatically uniform.**
* (b) Its type-p singles (p ∈ A0) are exactly the edges W avoiding D_{y,p} := {y}∪(A0∖p). Each such W has:
  Q := W∩N ∌ y, k := |Q| ∈ {2,3,4} (k = 1 would make W an (X,Y)-single whose A-part is not A0; N is a transversal);
  W∩A = {p} ∪ A' with A' ⊂ A∖A0, |A'| = 4−k; W∩C ⊂ C0 (R.3 against Y), c := |W∩C0|; for every z ∈ N∖Q, W is a
  type-p single of (X,F_z), so |W∩O_z| = 4 − c; for z ∈ Q, |W∩O_z| ≤ 4 − c (D1 at (X,F_z)). Against Y (type y) in
  (X,F_y) the class is (k, c), so k + c ≥ 5, c ≥ 2 (W7-I), and k + c ≥ 6 under NK.
* (c) **(X,F_y) is uniform ⟺ every edge avoiding some D_{y,p} has (k,c) = (4,4)**, i.e. W∩S = S∖D_{y,p} and W misses
  A∖A0, C∖C0 and every O_z.
* (d) (k,c) ∈ {(2,3),(3,2)} ⟺ {X,F_y,Y,W} is a (3,2,1,1)-K4 (|W∩Y| = k + c = 5, then N.4). So **in N-K4 the K4
  is itself a (P)-violation** whenever its pair (P0,P2) is uniform: (X,Y,F_y,W) = (P0,P2,P1,P3), (k,c) = (2,3).
  Under NK the possible deviant classes are (k,c) ∈ {(2,4),(3,3),(3,4),(4,2),(4,3)}.
* (e) A deviant with k ≤ 3 is a deviant type-p single of (X,F_z) for every z ∈ N∖Q, so it spoils at least two of the
  five propagated pairs at once.
Literal check of (b)/(c) on the examples (w9_check_examples.py): `r=16: type-p singles checked=480, deviant: 0`,
`r=22: checked=800, deviant: 0` (both examples are uniform, so (P) holds there).

### P9.3 COMPUTED: one uniform pair forces no new rigid 4-set (sound S-closure, work/e616/t21/w9_sclosure.py)
Model: the 7 "good" edges X, Y, F_z (S-parts S∖D for D = C0, A0, N∖z; pairwise disjoint 12-point outsides). For a
4-set D ⊂ S, a generic edge E avoiding D has S-part e ⊂ S∖D and overlaps o_i with the good outsides. Constraints (all
proved): Lemma A, capacity Σo_i ≤ 21 − |e|, F1 for every good pair, L on {P_i,P_j,P_l,E} for every good triple whose
common part e misses, D1 at every good 5-pair, uniformity of (X,Y) (|e∩N| = 1 ⇒ e ⊇ A0∪C0), NT against good singles
of the same pair, and optionally NK. All o_i enter monotonically, so the check is exact for this constraint set.
Output: `iter 1: good=7 newly rigid=0` (with and without NK). w9_probe2.py: for all 708 remaining 4-sets at least
**37** S-patterns survive (with NK), and the rigid pattern S∖D is always among them. For D = D_{y,p} the surviving
classes are exactly the deviant (k,c) of P9.2(b). **Meaning: (P) cannot be proved from one unknown edge against the
uniform pair; any proof needs several unknown edges interacting.**

### P9.4 COMPUTED: (P) is locally FALSE in the (3,2,1,1)-K4 (work/e616/t21/w9_p02u.py on top of w8sat.build)
The Wave-8 point-level CNF (all 24 first-generation K4 witnesses, + TT), with every (0,2)-single **forced to have the
parts of P1** (F∩(P0∖N02) = M∖v, F∩(P2∖N02) = γ∪c3), i.e. "(P0,P2) uniform at first generation":
* `SAT 97 s` (3.38 M clauses), log w9_p02u_tt.log.
* + three τ-edges (avoiding C_G = γ∪c3, avoiding M∖v, avoiding {v}∪α∪a3_1): `SAT 184 s` (4.18 M clauses),
  w9_p02u_tt_gen3.log. The C_G-avoider in the solution is M ∪ A_G ∪ a4 (11 named points), exactly as U1 + TU predict.
* + U-overlap rules (Lemma A on new pairs, U-capacity, triple F1): `SAT 603 s` (5.05 M clauses), w9_p02u_tt_U.log;
  forcing re-checked by parsing (4/4 (0,2)-singles have P1's parts).
Independent check of the forcing (plain parsing of both logs): the four (0,2)-singles have exactly P1's parts; P3 is
the deviant (k,c) = (2,3). So the "(P0,P2) uniform, P3 the single deviant" picture is consistent at this depth, and by
P9.2(d) it is precisely a violation of (P). **Correction to NK4.5:** the solution actually logged in
w8sat_all_tt_U.log does NOT have uniform (P0,P2)-singles ((0,2):T023_0 has A-part {w, m3_0, m3_1, a4_0}). The
forced runs here replace that informal description.

### P9.5 Lemma OD (one deviant type; PROVED) — the "deviant absorbed" version of U1
Let (X,Y) be a 5-pair, M = X∩Y, such that for at least two types z ≠ w there is a single F_z with parts (A0,C0), and
let H be a type-w single with c := |C_H∩C0| ≤ 3. Then every A0-avoider E satisfies E ⊇ M∪C0, E∩A = ∅, E∩O_z = ∅
for each such z, and |E∩(C_H∖C0)| + |E∩O_H| = 4 − c. (Symmetric statement for C0-avoiders when |A_H∩A0| ≤ 3.)
*Proof.* Steps (i)–(iii) of U1 with z, z' ≠ w give E ⊇ M∖w, E∩C0 = C0, E∩O_z = ∅ and |E∩X| = 5. If w ∉ E, then
E∩X = (M∖w)∪{e} with e ∈ A∖A0. {X,Y,H,E} has empty intersection (X∩Y∩H = {w}) and |X∪Y∪H| = 49, so
|E∩(X∪Y∪H)| ≤ 9 = |E∩X| + |E∩C0|; hence E∩H ⊂ {e} ∪ (C_H∩C0), |E∩H| ≤ 1 + c ≤ 4, against Lemma A. So w ∈ E and
E∩X = M. Lemma A for H gives |E∩(C_H∖C0)| + |E∩O_H| ≥ 4 − c; L on {X,F_z,H,E} (empty intersection since
X∩F_z∩H = A0∩A_H; |X∪F_z∪H| = 53 − c, TU) gives ≤ 4 − c. ∎
In the K4 with (P0,P2) uniform this reproduces U1 (consistent, nothing new). Examples: hypothesis never holds
(all K-pairs uniform); PG(2,4) skeleton: 0 one-deviant-type 5-pairs (w9_check_pg.py). So OD is vacuous on all three.

### P9.6 Equal-C-parts subcase via ZF-T* (PROVED tightness; no loss found)
Let (E1,E2) be C-uniform (every single has C-part C*), α_zz' := A_z∩A_z', A** := ∪α_zz'. The C*-avoiders form a
family 𝒳 that **contains E1**; every X ∈ 𝒳 has X ⊇ M ∪ A**, X∩C = ∅, |X∩A_z| + |X∩O_z| = 4, and (E2,X) is a 5-pair
with the same singles and classes (4, a_zz') (since X ⊇ α_zz', the O_z are disjoint). Exact counts for X ∈ 𝒳:
* {E2, X, F_z, F_z'}: empty intersection, union exactly 61;
* {X, F_z, F_z', F_z''} with A_z∩A_z'∩A_z'' = ∅: |F_z∪F_z'∪F_z''| = 55 − Σa, |X∩(∪F)| = 15 − Σa, union exactly 61.
So the second 5-pair (E2,X) is again exactly tight in every 4-family these lemmas produce; class flipping does not give
a unit of loss by itself. (Wave 8's w8n_model already found the C-uniform (2,4) configuration locally FEASIBLE.)

### P9.7 Status and honest assessment
* Case N: **OPEN**. Nothing in this wave is an UNSAT/closure claim.
* The plan "prove (P), then run W6-U on S" cannot start locally: (P) fails at first-generation depth (P9.4), and with
  one unknown edge nothing new is rigid (P9.3). Every 4-family produced by U1/OD/ZF-T*/TU is exactly at 61.
* What a proof must do: use two or more *unknown* edges at once (e.g. the deviant W together with τ-edges avoiding
  sets that meet both D_{y,p} and the deviant's S-part), or a global/counting argument. A concrete next experiment:
  extend w9_sclosure.py to pairs of generic edges (patterns e1, e2 plus a U-overlap variable), restricted to the
  deviant classes of P9.2(b).
Scripts (work/e616/t21/): w9_sclosure.py, w9_probe.py, w9_probe2.py, w9_p02u.py, w9_check_examples.py,
w9_check_pg.py. Logs: w9_p02u_tt.log, w9_p02u_tt_gen3.log, w9_p02u_tt_U.log.

## Wave 9 CEGAR (2026-10-15, ~11:25–12:50 EDT; computational, N-K4 and N-noK4)
**Result: NO UNSAT, so there is no DRAT certificate and no control runs in this wave.** No realized (literally L-checked)
configuration either. What I did get is a negative finding about the method: the U-mode relaxation is far too weak (W9.3).
That explains why every U-mode run so far (NK4.4 included) came out SAT, and it says what a proof has to control.

**W9.0 The (2,2,2,1) run** (w8sat_2221_all_tt_U.log): **SAT** in 797.5 s (6.31 M clauses, all 27 first-generation
witnesses, +TT +U). So there is no first-generation contradiction here either. By NK4.0 the split does not need (2,2,2,1).

**W9.1 Model** (work/e616/t21/w9lazy.py, the SAT/CNF encoding; w9cp.py is the same set of instances in CP-SAT). Base:
4 edges, all 61 points named: K4 = (3,2,1,1), or noK4 = (E1,E2,G,H) with class (a,c). New edges are generic edges
that avoid a 4-set (justified by τ ≥ 5 alone). u[F,G] has the **exact** meaning min(|F∩G∖base|, 6), so "no common
outside point" (u = 0) can be used soundly. Each clause is tagged with the lemma it instantiates:
E21; A (Lemma A); L1:S (L on S∪{F}, which includes R.1 and L3); D1; AV (τ ≥ 5); LA (Lemma A for new pairs, with u);
L2:S (L on S∪{F,G}: |F∩∪S| + |G∩∪S| + |F∩G∖∪S| ≤ |∪S| − 19 when F∩G∩(∩S) = ∅); F1t; TT (W7-1 + W7-I on base edges);
NTC (W7-I C-side at a 5-pair (P,Q) with Q base); NK (the N-noK4 hypothesis, at 5-pairs with a fully named
intersection); CAP (pairwise outside-disjoint G_j ⇒ Σ|F∩G_j∩U| ≤ 21 − |F∩named|); 'def' (aux definitions).
The lazy instances are added when the current solution violates them.
**CEGAR on edges (R.2):** at every 5-pair (X,Y) of the current solution whose intersection N is fully named, with
gen(X), gen(Y) < gmax, each y ∈ N needs an edge that avoids N∖{y}. If no edge in the model does, a new edge is
added with gen = max + 1. Gen 1 = first-generation singles; gen 2 = SECOND generation, here restricted to 5-pairs
(base, gen-1 edge) ('bonly'; these are the propagation-G pairs (P_i,F) and include the ZF-flipped pairs (E2,X)).
Scripts: w9run.py (driver, checkpoint w9_TAG.json), w9cert.py (CNF rebuild + DRAT + drat-trim; not exercised,
since no UNSAT occurred), w9core.py, w9realize.py.

**W9.2 Runs (all SAT; none is a result about the problem)**
* K4 (3,2,1,1), tag cpt: all 24 gen-1 singles, **SAT and violation-free** after 58 lazy rounds (2137 lemma
  instances, 3.2 M clauses). Gen 2 (bonly) needs 192 distinct 4-sets. I added 40 of them (64 edges): still SAT through
  66 rounds (4267 instances, 6.7 M clauses), not converged (≈400 new violations per round). Stopped. Checkpoint w9_cpt.json.
* noK4 (2,4), tag cn24: 19 gen-1 + 5 gen-2 singles (24 edges), **SAT and violation-free** after 109 rounds
  (3835 instances, 8.3 M clauses). Gen 2 needs 145 distinct 4-sets. With 64 edges: SAT, not converged
  (11 M clauses, killed for memory). Classes (3,3) and (3,4) were **not run** (CPU budget).
* CP-SAT version: slower than CaDiCaL on these instances (more than 4 min per solve at 24 edges). Abandoned.

**W9.3 The finding: U-mode SAT does not mean local consistency.** I realized the violation-free gen-1 solutions
literally (w9realize.py: one shared outside point for each F1 triple, pair-private outside points for the rest,
private fill to 21). Results:
* K4 (w9_cpt_gen1_stall.json): 22 of the 24 new edges would need **more than 21 points** (up to 41). The pairwise
  outside overlaps add up to 277 over 194 pairs, the largest per-edge demand is 32, and the capacity is 11–12.
  Literally there are 825 W7-I violations, all with a=1 or c=1 on the side of a NEW edge, i.e. at 5-pairs (B_i,F).
  NT there needs Z1∩Z2∩(F∖B_i), and that set lies partly outside the base.
* noK4 (2,4) (w9_cn24_gen1_stall.json): demand up to 45 against capacity 11–12; 3 W7-I and 27 NK violations.
So the solver makes Lemma A, NK and the L2 bounds tight **by piling overlap of new edges outside the base**. The
sound encoding cannot see this, because only the pairwise lower bounds u are known. The multi-way structure of the outside points
(who shares which outside point) is free. That structure is exactly what W6-U used (Lemma H = L on 4 edges with
disjoint outside parts). Any contradiction therefore has to come from controlling outside parts. Concretely, a
non-uniform analogue of Lemma H is needed: for two edges in 5-pairs reached by propagation, with different
13-set traces, the outside parts are disjoint, or their overlap is bounded. Adding more singles to a model that
leaves the outside points free cannot close the case.
**Exact-pool attempt** (w9pool.py, constructive only: K explicit shared outside points, L checked literally on every
subfamily, W7-I / NK at every 5-pair). This would produce a literal configuration or show the U-relaxation's
looseness is essential. K = 0, gen 1, K4: after 1225 instances (4.3 M clauses) the next solve did not finish in more
than 10 min. **UNKNOWN.** K = 12 and K = 40: aborted (memory, and a solve that stalled at 7.8 M clauses). Not a result.

**W9.4 Recommendation.** Stop growing witness sets in the U-relaxation. Either (a) prove an outside-disjointness lemma
for the non-uniform case (the W6-U Lemma H mechanism) by hand, or (b) give the solver a sound finite abstraction
of the outside points: each new edge has one 12-point "outside block" per 5-pair, and R.3 makes the blocks of
cross-type singles disjoint. Then model block identities instead of point overlaps.

## Wave 10 outside-H (2026-10-15, ~12:45–13:45 EDT)
**Result: Case N is still OPEN.** This wave makes no UNSAT claim about the problem, so it has no DRAT certificate and no
control runs. What is new:
(i) The "non-uniform Lemma H" is exactly OO (N.1) applied at DERIVED 5-pairs. Its explicit forms are in H10.1.
- Cross-type singles: overlap 0. This is just R.3.
- Same-type singles: overlap 0 only under a C-agreement hypothesis.
- Lemma-T witnesses against singles: overlap EXACTLY 4 − c. So it is not 0 in general, and no uniform Lemma H holds.

(ii) A degree count that uses only pairwise information provably cannot even exclude the spurious W9 core (H10.3).
(iii) The missing ingredients are two 3-way lemmas, **SQ (F1 squeeze)** and **SF (L on one base edge plus 3 edges)**.
- Both are proved by hand.
- Each refutes a W9/W10 stall core by hand: 5 edges for the K4 core, 3 edges for the noK4 core.

(iv) A sound exact LP oracle for outside points (w10_ulp.py). It finds the minimal unrealizable sub-configuration of a stall core.

(v) The CEGAR with SQ added stalls again, at gen 1, violation-free. That new core dies to SF. The run with SQ+SF had not finished when this was written.

Notation: §1, N.0(iii). For a 5-pair (X,Y) put s_XY(Z) := 9 − |Z∩(X∪Y)|. This is ≥ 0 by D1 when X∩Y ⊄ Z.

### H10.1 Lemma HN = OO at derived pairs (PROVED)
OO (N.1): if (X,Y) is a 5-pair, N = X∩Y and Z∩Z'∩N = ∅, then |Z∩Z'∖(X∪Y)| ≤ s_XY(Z) + s_XY(Z') (this is L on {X,Y,Z,Z'}).
Let F be a single of (X,Y) of type y. Then (X,F) is a 5-pair with N' = {y}∪A_F.
* **(a) Slack of other singles at (X,F).** For a single Z of type z ≠ y: Z∩(X∪F) = (Z∩X) ⊔ (C_Z∩C_F), because O_Z∩O_F = ∅. Hence
  **s_XF(Z) = 4 − |C_Z∩C_F|**. A Lemma-T witness of (X,F) is a single of (X,F), so its slack there is 0.
* **(b) Same-type outside overlap.** Let Z, Z' be singles of (X,Y) whose types differ from y, with A_Z∩A_Z'∩A_F = ∅. Then Z∩Z'∩N' = ∅,
  and Z∩Z'∖(X∪F) = ((C_Z∩C_Z')∖C_F) ⊔ (O_Z∩O_Z'). So
  **|O_Z∩O_Z'| + |(C_Z∩C_Z')∖C_F| ≤ 8 − |C_Z∩C_F| − |C_Z'∩C_F|.**
  Content: the case where Z and Z' have the SAME type (different types already give O_Z∩O_Z' = ∅). In particular, in a C-uniform pair,
  same-type singles have disjoint outsides as soon as some single F of another type has A_F∩A_Z∩A_Z' = ∅.
* **(c) Witness vs single: no disjointness.** By P9.2(b), a Lemma-T witness W of (X,F) at p has |W∩O_z| = 4 − c for every type
  z ∉ W∩N. Here c = |W∩C_F|. This is an equality, so the outside overlap of a witness with a cross-type single is exactly 4 − c. It is 0 only when
  c = 4, the uniform situation. **This is precisely where the W6-U Lemma H fails to generalise.**
* **(d)** Two witnesses of (X,F) at p ≠ p' are disjoint outside X∪F (R.3). Relative to X∪Y they can share only points of O_F, at most
  min(4−c, 4−c') of them.

### H10.2 Degree lemma (PROVED) and the per-edge count
Let u ∉ X∪Y.
- The (X,Y)-singles through u all have one type.
- More generally, two edges through u with Z∩Z'∩N = ∅ need s(Z) + s(Z') ≥ 1.
- Edges through u with slack 0 have pairwise-intersecting N-traces.

For a modelled family 𝓔 and U = points outside the base, the count is
Σ_{G∈𝓔} |F∩G∩U| = Σ_{u∈F∩U} (d_u − 1) ≤ (ω_F − 1)|F∩U|.
Here ω_F is the largest set of edges, containing F, that can pairwise share a U-point.

### H10.3 COMPUTED: a pairwise degree count is too weak (w10_deg.py)
On the W9 K4 gen-1 stall core (w9_cpt_gen1_stall.json):
- Pairwise U-overlap upper bounds come from L on B'∪{F,G} with |F| = 21.
- The compatibility graph has ω_F = 6 for EVERY one of the 24 edges (one per base pair, the maximum).
- The Lemma-A demand Σ_G (5 − |b_F∩b_G|)^+ is ≤ 26, while (ω−1)·c_F ≥ 55.

So "degrees of outside points versus 12-point outside parts" gives nothing. The obstruction is ≥ 3-way. (W9.3's per-edge "demand
32–45" counted the solver's u-values, not the Lemma-A requirement.)

### H10.4 Two 3-way lemmas (PROVED) and hand refutations of the stall cores
**Lemma SQ (F1 squeeze).**
- Setup: W, V are edges. 𝒢 is a family of edges whose parts outside a set R are pairwise disjoint (for example, cross-type singles of a 5-pair
  (X',Y') with R = X'∪Y', by R.3). R' ⊇ R. 𝒯 := {G∈𝒢 : W∩V∩G∩R' = ∅}.
- Claim: **|𝒯| ≤ |W∩V∖R'|**. If moreover (X,Y) is a 5-pair with X∪Y ⊆ R' and W∩V∩(X∩Y) = ∅, then
  **|𝒯| ≤ s_XY(W) + s_XY(V).**
- Proof: F1 gives u_G ∈ W∩V∩G. Since u_G ∉ R' ⊇ R, u_G lies in G∖R, so the u_G are distinct. The last step is OO. ∎

**Lemma SF (one base edge + three edges).**
- Setup: P∩X1∩X2∩X3 = ∅. m_a := multiplicity of a point a in X1, X2, X3.
- Claim: **Σ_i |Xi∩P| + Σ_{a∉P} ([m_a ≥ 2] + [m_a ≥ 3]) ≤ 23**.
- Proof: this is L on the 4 edges, |X1∪X2∪X3∖P| ≥ 40, written by inclusion–exclusion with |Xi| = 21. ∎
- Used form: the outside points contribute at least the forced pairwise overlaps (Lemma A), minus at most one pair's overlap for the triple term.

Hand refutations, exact integer re-check in w10_handcheck.py:
* **(1) W9 K4 (3,2,1,1) gen-1 stall** (w9_cpt_gen1_stall.json). The deletion filter of H10.5 finds a 5-edge core.
  - W = (P1,P2)-single of type γ1, so s12(W) = 0. V = (P1,P3)-single of type γ0; V∩N12 has 3 points, so s12(V) = 2. W∩V∩N12 = ∅.
  - 𝒢 = the three (P2,P3)-singles of types γ0, γ1, γ2, with R = P2∪P3 and R' = the base union.
  - None of the three triples (W,V,G) has a named common point, so |𝒯| = 3 > 2. **Contradiction.**
  - The W9 U-mode clause F1t ("every pair has a U-point") is satisfied by ONE shared point, so it could not see this.
* **(2) W9 noK4 (2,4) stall** (w9_cn24_gen1_stall.json). The minimal core has 3 edges:
  - Z1, Z2 = (H,E1)-singles of types ah1 and al0. They are cross-type, so they share no U-point.
  - W = the gen-2 single (E1,F4):a09.
  - H∩Z1∩Z2∩W = ∅. The named union of {H,Z1,Z2,W} is 27 and the U-capacity is 35.
  - Lemma A forces |Z1∩W∩U| ≥ 1 and |Z2∩W∩U| ≥ 1, so the union is ≤ 27 + 35 − 2 = 60. **L is violated** (an SF instance).
* **(3) The new K4 stall after adding SQ** (w10_sq_k4g1_stall.json, H10.5). The minimal core has 3 edges:
  - The edges are the (P1,P0)-single m3_0, the (P3,P0)-single α0 and the (P3,P1)-single γ1. Their intersection with P1 is empty.
  - The named union is 26 and the capacity 36. The forced overlaps are 1 + 1, so the union is ≤ 60. **SF/L is violated.**

**Checks against the examples** (w10_check_examples.py, general-r forms with the bound (r+2−K) in place of 18):
`r=16 H(16,10,7): OO checks=3524 viol=0; HN same-type checks=0; SQ checks=8039 (count>0: 0) viol=0`,
`r=22 H(22,13,9): OO 1984/0; HN 0; SQ 3724 (count>0: 0) viol=0`, `PG(2,4) skeleton: OO 1680/0; HN same-type 720/0; SQ 8400 (count>0: 0)/0`.
- HN-same-type is vacuous in the uniform examples (A_F∩A_Z∩A_Z' = A0 ≠ ∅).
- SQ's hypothesis never fires in any of the three (every W∩V∩G meets the core). So SQ is consistent with the examples, but they do not test it.

### H10.5 COMPUTED: exact outside-point LP oracle, minimal cores, and the CEGAR with SQ/SF
* **w10_ulp.py (sound).** For FIXED named traces b_F, a U-point is described by the set S of model edges containing it, and n_S ≥ 0 counts them.
  - Rows: capacity Σ_{S∋F} n_S ≤ 21 − |b_F|; Lemma A; F1 for new triples with no named common point; L for every family B'∪N'
    (B' a nonempty set of base edges, |N'| ≤ 3) with empty named intersection.
  - All rows are linear. Dropping rows only relaxes, so LP-infeasible ⇒ no literal realization.
  - Method: exact column generation (SCIP pricing) with a Lagrangian bound.
  - **K4 W9 stall: INFEASIBLE**:
    - phase-I 12.5 using only families with ≤ 2 new edges + F1 (exact convergence, price 0);
    - 58.1 with ≤ 3-new-edge L and no F1;
    - 83.1 with everything.
  - **noK4 W9 stall: FEASIBLE** with ≤ 2 new edges, **INFEASIBLE** (phase-I 38, exact) with ≤ 3.
* **w10_iis.py**: a deletion filter on the edge set. Its minimal cores are 5 / 3 / 3 edges, given by hand in H10.4 (1)–(3). The LP is floating
  point, but every core it found is re-proved exactly by hand.
* **w10sq.py + w10run.py.** These add lazy instances to w9lazy:
  - [SQ] (W,V,𝒢): pairwise U-disjoint 𝒢 with no named common point ⇒ |W∩V∩U| ≥ |𝒢|;
  - [SF] (P,X1,X2,X3) in the "drop one pair" form above.

  Results:
  - K4 (3,2,1,1), gen 1, SQ only (log w10_sq_k4g1_phase1.log): **SAT and violation-free (STALL) at it 50**, 2264 instances
    (342 SQ). That stall is again unrealizable, by (3).
  - Restart with SF (w10_sqsf_k4g1.log, background, timeout 3000 s): it 0 SAT (563 s, 5.1 M clauses, 315 new violations). Still running
    when written. The SF clauses are large (totalizer over ~180 literals), so it is slow. **Not a result.**
  - noK4 with SQ+SF: not run (CPU budget, shared with the w10x pool runs).

### H10.6 Assessment: what fails, precisely
1. **No uniform outside-disjointness.**
   - Cross-type singles: 0 (R.3).
   - Same-type singles: 0 only under HN(b)'s hypothesis.
   - Witnesses vs singles: exactly 4 − c, which is tight by P9.2.

   So a W6-U-style "all outside parts disjoint" lemma is false in Case N. Every outside overlap is controlled by OO at some derived
   pair, with budget s + s'.
2. **Degree counting with pairwise data is useless** (ω = 6 everywhere, demand ≤ 26 against capacity ≥ 55). The vertex set is unbounded, so a pure
   count over outside points cannot give a contradiction. Any contradiction is a specific L/F1 family. In the cores seen, these are the 3-way
   families SQ and SF, which mix forced outside overlaps (Lemma A, F1) with the OO/L budget.
3. **Each spurious relaxed core so far dies to a 3–5 edge SQ/SF instance.** The solver then moves to a new core.
   - Whether the closure (all SQ/SF/L-with-3-new instances, gen 1 and gen 2) is UNSAT is exactly the open computational question.
   - The w10x exact-pool encoding (other agent) answers the same question exactly, slower. The ULP oracle is the cheap sound filter.
   - Recommended next step: a Benders loop. Core SAT model → w10_ulp on each core → add the Farkas cut, or the minimal core's SQ/SF clause.
     The cut Σ_A y(5−|b∩b|) + Σ_T y[∩=∅] + Σ_L y[∩=∅](61−|∪|) ≤ Σ κ(21−|b_F|) is valid for EVERY core, because the column condition
     does not depend on the core.
4. **No hand global contradiction was found.** The configurations stay locally consistent modulo these 3-way obstructions.

Scripts (work/e616/t21/): w10_ulp.py, w10_iis.py, w10_deg.py, w10_handcheck.py, w10_check_examples.py, w10sq.py, w10run.py.
Logs/data:
- ULP and IIS logs: w10_ulp_cpt_23.log, w10_ulp_cpt_22.log, w10_ulp_cpt_23_nof1.log, w10_ulp_cn33.log, w10_iis_cpt22.log, w10_iis_cn33.log,
  w10_iis_sqk4_33.log.
- CEGAR: w10_sq_k4g1_phase1.log, w10_sqsf_k4g1.log, w10_sq_k4g1.json (checkpoint), w10_sq_k4g1_stall.json.
- Stall copies used as ULP inputs: w10s_*.json.

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

## Wave 11 noK4 (3,3)/(3,4) (2026-10-15, ~14:40–16:36 EDT run crashed without a write-up; reconstructed from its files 16:40 EDT)
Context: Wave 10 exact-outside (X.1–X.9) closed class (2,4)/(4,2) (refereed SOUND, docs/referee/w10-referee.md). By N8.0 + W6-U
an N-noK4 counterexample now needs a 5-pair with a cross-type pair (G,H) of class (3,3) or (3,4)/(4,3). This wave attacks both with
the SAME encoder (w10x_exact.py) through a thin driver work/e616/t21/w11_exact.py. Status at the time of writing is in W11.0;
it is updated after each milestone below.

### W11.0 Status (updated 22:25 UTC = 18:25 EDT; milestone log in W11.5, which sits further down because another agent's
### "Wave 11 N-K4 Benders" section was appended in between)
- **(3,4)/(4,3): CLOSED in N-noK4 (COMPUTED, certificates VERIFIED).** Cite **w11n34min**: base + the 16 first-generation singles
  + ONE τ-edge J31 (avoids {al0,al1,al2,cl0}), K = 104 = KB bound, 637 instances, CaDiCaL UNSAT, drat-trim `s VERIFIED`.
  Every drop-one-kind control (N24, L, D1, SA, W7, R3) SAT, nonk SAT. Also VERIFIED on the larger slot sets x1 (22 slots) and noJ04
  (21 slots), with and without symmetry breaking (W11.3, W11.5).
- **(3,3): CLOSED in N-noK4 (COMPUTED, certificates VERIFIED).** Cite **w11n33z1**: the same 17 slots (16 singles + J31), K = 104.
  The full lazy-loop CNF (6.88 M clauses) is drat-trim `s VERIFIED`, and the extracted 2394-instance core was independently
  rebuilt and is `s VERIFIED` (W11.5). Controls (all done): drop N24/L/D1/SA/W7 SAT, drop R3 UNSAT (R3 redundant),
  nonk SAT, noSB UNSAT `s VERIFIED`. Summary table and caveats: W11.6.
- Neither result is a case split: every slot is an edge that exists in every configuration containing the base (τ ≥ 5), so one
  UNSAT instance kills the whole class (W11.1).
- **Consequence (if the encoder/instances survive refereeing): N-noK4 is closed.** N8.0 + W6-U leave (2,4)/(4,2), (3,3), (3,4)/(4,3);
  Wave 10 kills the first, this wave the other two. Case N then reduces to N-K4. The (3,3) and (3,4) certificates **use** the
  Wave 10 (2,4) theorem (tag N24; drop=N24 is SAT) and NK (nonk is SAT), so they are specific to N-noK4 and depend on Wave 10.
- **Not yet refereed.** New ingredients relative to the refereed Wave 10 certificate: tag N24; a slot that is a generic τ-edge
  (J31, ν = 5 in KB); the eager layers eager3/f1all (instances of refereed lemmas); the drivers w11_exact.py / w11n_*.py. The
  referee's independent encoder (sat/w10ref/) has not been run on these instance lists.

### W11.1 What the instances are, and why they cover the WHOLE class (not a sub-case)
- **Base.** `nok4:a,c` = base_nok4(a,c) (w9lazy.py): E1=B0, E2=B1, G=B2 (type v), H=B3 (type w) with |A_G∩A_H| = a (points al*),
  |C_G∩C_H| = c (points cl*), A/C private parts ag*, ah*, cg*, ch*, and disjoint 12-point outsides og, oh. As for (2,4) (referee §4),
  R.3 + S(a) force exactly this 61-point configuration for any 5-pair whose cross-type singles G,H have class (a,c); it is unique up to
  relabelling. (4,3) is (3,4) with E1↔E2 swapped. Base 5-pairs (checked): E1E2, E1G, E1H, E2G, E2H; for (3,4) E2∩G = E2∩H = {v or w}∪{cl0..cl3}.
- **Edges ("slots").** Every slot is "an edge avoiding a fixed 4-set S of named points". Such an edge exists in EVERY configuration by
  τ ≥ 5. Nothing is assumed about it beyond avoiding S; whether it is a single of a 5-pair is derived (R.1/R.3), never imposed.
  - `gen1auto` + `sel=0..6,10..18`: 16 of the 19 first-generation singles (the three (E1,H)-singles al0..al2 are omitted).
    Omitting slots is a relaxation (fewer edges ⇒ fewer constraints), so UNSAT of the smaller instance is the stronger statement.
  - `extra`: further τ-edges `LABEL@p1+p2+p3+p4` (avoid set). These are NOT case hypotheses. The names 'x1', 'y1', 'noJ04' only
    label which set of extra τ-edges was added: **x1** (3,4) = J04{cl0..cl3}, J13{al0,cl0,cl1,cl2}, J22{al0,al1,cl0,cl1},
    J31{al0,al1,al2,cl0}, two g2-edges avoiding {m0|m1, al0,al1,al2}; **noJ04** = x1 minus J04 (edge-drop, w11_edgedrop.py);
    **y1** (3,3) = J31{al0,al1,al2,cl0}, J13{al0,cl0,cl1,cl2}, Jv{cl0,cl1,cl2,cg0}.
  - Hence: **every N-noK4 configuration containing a class-(a,c) 5-pair contains the base plus a slot list satisfying every encoded
    statement.** UNSAT of one instance therefore kills the whole class. No case split is involved, so no "the sub-cases cover the class"
    argument is needed beyond this.
- **Pool bound K.** setup() applies Lemma KB (X.2): ν = 9 for a slot whose avoid set is N∖{y} for a base 5-pair (then R.3 gives
  |F∩(Bi∪Bj)| = 9), else ν = 5. J04 (3,4) and Jv (3,3) are of the first kind (type-v singles of (E2,G); v is realised by E1, so the
  slot may coincide with E1 — duplicates and slot = base edge are exact under the literal semantics, referee §1a). Every run below has
  K = KB bound (logged `sound=True`): x1 K=142, noJ04 K=136, y1 K=118.
- **Lemmas used** (tags as X.1): A, L/XL, R1, R3, SA, D1, W7, NK, TT, and new tag **N24** = the Wave 10 theorem "no 5-pair of an N-noK4
  configuration has cross-type singles of class (2,4)/(4,2)" (option `no24`). It is applied (eager at base pairs, lazily anywhere) as:
  at a 5-pair (X,Y) two cross-type singles may not have class (2,4)/(4,2). **So (3,3)/(3,4) depend on the (2,4) closure** (control
  drop=N24 is SAT, W11.3). Eager layers eager2/eager3/f1all (w11_exact.py docstring) are instances of the same lemmas, stored as
  instances (they go through add_inst), so they are subject to core extraction.

### W11.2 Runs that did NOT decide anything (recorded for honesty)
- w10x_n33g1 (19 singles, K=114): killed, RSS 2.1 GB > budget (w10x_queue.log).
- w11n33m / w11n34m (16 singles, no extra τ-edges): **VIOLATION-FREE literal configurations** (w10x_w11n33m_real.json,
  w10x_w11n34m_real.json; also w11n33mN with no24). Independently checked by w10x_verify.py (logs w11n3?m*_verify.log): L on all
  subfamilies, all 5-pair lemmas, NK hold — but **τ = 2** (e.g. {al0,cl0} is a transversal). So the 16 singles alone are consistent;
  τ-edges are required. These are not counterexamples.
- w11n33fN, w11n34f (all 19 singles, warm-started): not converged within one chunk (time limit). w11n33x1 (22 edges, full eager3):
  killed for memory; w11n33x2/x3 (22 edges): not converged after 5 iterations. UNKNOWN, not results.

### W11.3 Class (3,4)/(4,3): UNSAT, VERIFIED, controls (logs w11n34x1.log, w11n34x1_core*.log, w11n34x1_core_noJ04_cert.log)
- Lazy loop w11n34x1 (22 edges, K=142): it 0 SAT (2109 violations, 600 added), **it 1 UNSAT** (8.7 M clauses).
- Core (w10x_core.py, stable over 3 rounds): **659 instances** {SA 233, D1 129, W7 127, R3 100, N24 50, L 20}; no TT.
  Extra τ-edges referenced by core instances: only J04 and J31 (J13, J22, both g2-edges appear in no core instance; they remain in the
  hard eager layer).
- Certificate (C1) w10x_w11n34x1_core.cnf (474206 vars, 2149092 clauses) + .drat: CaDiCaL UNSAT 28.4 s, **drat-trim `s VERIFIED`**.
  No-SB rebuild: UNSAT, **`s VERIFIED`**. SHA-256 in w10x_w11n34x1_core_cert.sha256 (cnf 64914e41…, drat 380b33ad…), re-checked OK.
- Controls on the 659 core instances (each removes one kind): drop N24 SAT, L SAT, D1 SAT, SA SAT, W7 SAT, R3 SAT, **nonk SAT**;
  drop TT UNSAT+VERIFIED (vacuous: the core has no TT instance). So every kind used is needed, and the result is specific to N-noK4.
- Edge-drop controls: **without J04 still UNSAT, `s VERIFIED`** (21 edges, K=136, 637 instances); without J31 **SAT**. So J31 (an edge
  avoiding {al0,al1,al2,cl0}) is essential, and the possible coincidence J04 = E1 plays no role.
- Certificate (C2) on noJ04: w10x_w11n34x1_core_noJ04.cnf (435308 vars, 1991491 clauses): UNSAT 48.1 s, **`s VERIFIED`**; SHA-256 in
  w10x_w11n34x1_core_noJ04_cert.sha256 (cnf 6f8e9c66…, drat be6b13f7…), re-checked OK. Its controls: drop N24/L/D1/SA/W7/R3 all SAT,
  TT UNSAT+VERIFIED (vacuous), nonk SAT; noSB result: see W11.5 (was running at reconstruction).

### W11.4 Class (3,3): state at the crash (log w11n33y1.log)
- w11n33y1 (19 edges = 16 singles + J31, J13, Jv; K=118): it 0..7 SAT with violations 620 → 261 → 126 → 76 → 58 → 36 → 69 → 59,
  **it 8 UNSAT** (150 s, 9.18 M clauses, 18445 instances). Marker file w10x_w11n33y1.UNSAT.
- Core extraction (w10x_core.py rounds=3, RSS ≈1.5 GB) was still running when this was written; NO certificate yet. **Until W11.5
  reports a VERIFIED certificate, (3,3) is "solver UNSAT, unverified".**

## Wave 11 N-K4 Benders (2026-10-15, ~14:40–16:45 EDT; reconstructed 16:40 EDT from files, the first agent was cancelled before writing up)
**Result so far: N-K4 (3,2,1,1) is NOT decided. No UNSAT claim, no DRAT certificate yet, no realized configuration.**
What exists is a sound Benders pipeline, 2204 exactly re-checked Farkas cuts, and a running sub-instance. Details below.

### B11.1 Method (work/e616/t21/w11_benders.py, w11_sub.py)
* **Master** = the Wave 8 point-level CNF (w8sat.build('3211'), NK4.3): traces b_F ⊆ the 61 named points of P0..P3 for the
  24 first-generation singles S^{ij}_x, +TT, +SB (lex order of columns inside each O_i; the O_i points are fully symmetric,
  every constraint and every cut is invariant). Variant `2` (w11_base2.cnf, 6.03 M clauses) adds eager **L4A** = L on
  {P_k,P_l,F,G} + Lemma A (proof in the docstring of l4a_extra).
* **Sub-problem** = exact outside-point LP of w10_ulp.py for a subset E of slots with traces fixed: n_S ≥ 0 counts the
  points outside P0∪…∪P3 lying in exactly the slots S. Columns: S contains no two singles of one base pair (R.3/S(a); in the
  (3,2,1,1)-K4 all singles of one base pair have distinct types). Rows: cap_F Σ_{S∋F} n_S ≤ 21−|b_F|; Lemma A for pairs;
  F1 for triples with empty named intersection; L for B'∪N' (B' ≠ ∅ base edges, N' ⊆ E) with empty named intersection,
  rhs 61 − |∪B' ∪ ∪b_N'| (base edges have no outside points, so the union is exact).
* **Cut.** A dual solution (y, κ) ≥ 0 that is column-feasible and has Σ y·rhs(b*) > Σ κ_F(21−|b*_F|) refutes b*. Column
  feasibility does not depend on b; each rhs is antitone in the trace data it reads. So the clause "some supported row got
  weaker, or some κ>0 edge shrank" ([|b_F∩b_G| ≥ k*+1] ∨ [b_F∩b_G∩b_H ≠ ∅] ∨ [∩ ≠ ∅] ∨ [|∪| ≥ u*+1] ∨ [|b_F| ≤ |b*_F|−1])
  is valid for EVERY realizable trace vector. Aux literals are exact totalizers/AND/OR.
* **Generic cuts** GEN2/GEN3 (trace-free Farkas combinations y=1 on A rows and one L row, κ=1): GEN2 = L4A for any B';
  GEN3: guard ∨ |(b_F∪b_G∪b_H)∩B| + |(b_F∩b_H)∖b_G| ≤ |B| − 8. They are checked first; the LP scan (all subsets of size
  ≤ 4, smallest first) runs only when no generic instance is violated.
* Floating LP (GLOP) → rationals (limit_denominator 1000) → κ repaired upward until every column holds exactly → gap > 0
  checked in Fractions. Every certificate is stored (w11b_certs/c*.json: E, traces b*, pair labels, rows with y, κ, gap,
  the cut clause) in FULL slot indexing 0..23, so every sub-instance re-uses every applicable certificate.

### B11.2 Runs
* **Full 24 slots** (w11b.log): its 0–16 on the plain master (all cuts |E| = 2; 64–125 per iteration), its 17–18 on master
  `2` (|E| = 3). 19 iterations, 1845 certificates, master never UNSAT. The cold solve of it 19 (7.15 M clauses) exceeded
  10 CPU-min and was killed twice (sandbox restarts). Abandoned in favour of sub-instances.
* **Sub-instance A** = the 13 singles of the base pairs (1,2), (1,3), (2,3) (full slots 11–23), master `2` restricted to
  them (w11s_A_base.cnf). **UNSAT of A implies UNSAT of the 24-slot instance** (dropping edges relaxes). Log w11s_A.log:
  its 0–15 all SAT; 285 GEN3 cuts and 74 LP cuts (all |E| = 4; no LP-infeasible subset of size ≤ 3 remains once the
  full-run cuts on slots 11–23 are loaded). Cuts per iteration 70 → 51 → 41 → … → 13 → 2; master time 4–295 s.
  Queue w11s_queue.sh 'A 4' (4 chunks × ≤ 1120 s) still running at 16:40 EDT (it 16); w11s_finish.sh A waits for it
  and, on UNSAT, dumps cuts, builds certificate + drat-trim, runs the nocuts control, the recheck and the encoding test.

### B11.3 Checks done (16:40 EDT)
* `w11b_recheck.py` (independent: rebuilds the base from w8k4.base_named, does not import w11_benders; re-validates every row
  as an instance at b*, y, κ ≥ 0, EVERY allowed column, and the gap exactly in Fractions; generic cuts: column feasibility,
  200 random identity tests of the compact form, violation at the stored traces):
  `certificates re-checked exactly: 2204/2204 OK (285 generic, 1919 trace-specific); |E| distribution {2: 1535, 3: 595, 4: 74}`.
* `w11b_enctest1.py 80 11` (per-certificate encoder control: CNF of one encoded cut with all edge bits fixed ⇔ independent
  set semantics `holds`): `80 certificates x 8 trace vectors, all agree (460 SAT/holds, 180 UNSAT/violated)`.
* Not yet: whole-file encoding test on A (w11s_enctest.py), DRAT, controls. They only make sense after an UNSAT.

### B11.4 Honest assessment
The loop is sound but has not converged. Its cuts are local (≤ 4 edges, exact LP on outside points). Whether the closure
under ≤4-edge LP cuts is UNSAT is exactly the open question; a STALL (master SAT with no infeasible ≤4 subset) would be
passed to a larger-subset or whole-instance LP, not reported as a configuration (a literal realization would still have to
be built and checked with w10x_verify-style DFS).

### W11.5 Milestone log (appended as results arrive; times UTC)
- 20:43 noJ04 controls finished: nonk SAT (75.9 s); **no-SB UNSAT (100.5 s), `s VERIFIED`**. So C2 needs neither SB nor J04.
- 20:46 **(3,4) minimal instance w11n34min: 17 slots = the 16 first-generation singles + J31 only (K = 104 = KB bound), same 637
  core instances (none mentions a dropped edge; built by work/e616/t21/w11n_mindrop.py from w10x_w11n34x1_core_noJ04.json).
  CaDiCaL UNSAT 88.7 s, drat-trim `s VERIFIED`** (313256 vars, 1544863 clauses). SHA-256 w10x_w11n34min_cert.sha256:
  cnf 75536e33…, drat 6c7fc519…. This is the certificate to cite for (3,4)/(4,3): base + 16 singles + ONE τ-edge avoiding
  {al0,al1,al2,cl0} (3 points of A_G∩A_H, 1 point of C_G∩C_H). Controls: log w11n34min_cert.log (script w11n_ctrl.sh).
- 20:50 (3,3): assumption-based core extraction on w11n33y1 (18445 instances, 9.18 M clauses) **timed out** in round 0 (1150 s cap;
  no core written). Switched to a DRAT-based core (work/e616/t21/w11n_dratcore.py, chain w11n_dc_chain.sh / w11n_dc_resume.sh,
  log w11n33y1_dcore.log): fresh CaDiCaL solve of the full CNF with binary DRAT → `drat-trim -c` → instances owning a core clause.
  That list is only a candidate; it is then certified from scratch by w10x_cert.py.
- (3,4) min controls (w11n34min_cert.log): drop N24 SAT, L SAT, D1 SAT, SA SAT, W7 SAT, R3 SAT; TT absent (vacuous).
- 21:03 **sandbox restart** (all processes killed, /tmp and ~/.local wiped; python libs now from work/e616/pylib via PYTHONPATH).
  Lost: the first DRAT-core solve of w11n33y1 (it had loaded the CNF, RSS ≈1.5 GB, no result), and the drat-trim step of the
  (3,4)-min no-SB control (its CaDiCaL solve had finished: **UNSAT 109.0 s**; drat-trim not run). The (3,4)-min nonk control
  finished first: **SAT** (202 s). So (3,4)-min: certificate VERIFIED, every drop-one-kind control SAT, nonk SAT, noSB UNSAT
  (unverified, but C2 noSB on the 21-slot set is VERIFIED). Scratch now goes to work/e616/t21/w11dc_tmp/, not RAM-backed /tmp.
- 21:24 **(3,3) lean instance w11n33z1: 17 slots = the 16 first-generation singles + J31{al0,al1,al2,cl0} only (K = 104 = KB bound;
  the (3,3) analogue of the (3,4) certificate). Lazy loop (fresh, same options as y1): it 0..16 SAT (violations 939 → 193 → … → 34),
  it 17 UNSAT** (6.88 M clauses, 15626 instances; log w11n33z1.log, checkpoint w10x_w11n33z1.json, marker w10x_w11n33z1.UNSAT).
  Solver result only; core + certificate pending.

### B11.5 Continuation (16:40–17:40 EDT): extended oracle, and a REALIZED 7-single sub-configuration
**Events.** Sandbox restart ~17:03 EDT killed the old-oracle A queue during its it-16 master solve (third time it 16 was
lost: >18 min per solve on a CPU shared with the noK4 agent). The old-oracle A/C queues were not relaunched.
**New code** (work/e616/t21/):
* `w11_big.py`: whole-slot-set LP with lazy L rows + deletion filter (fallback when no ≤4 subset is infeasible).
* `w11e_oracle.py` (EXTENDED oracle) = the B11.1 LP plus rows for the proved 5-pair lemmas at the DERIVED 5-pairs
  (P_k,F) (F a slot with |b_F∩P_k| = 5; named-only condition since base edges have no outside points):
  D1 (Σ_{S⊇{F,L}} n_S ≤ 9 − |b_L∩(P_k∪b_F)| when N'⊄b_L), R.3 (|L∩F| ≤ 5 for singles L of (P_k,F), + named
  |L∩P_k| = 5, |P_m∩F| = 5), S(a) (cross-type singles of (P_k,F) have no common point outside P_k∪F), W7-I on both sides,
  D1 with a base third edge; and **L0** = L on a set N' of ≥ 3 slots containing two singles of ONE base pair (S(a): no
  outside point lies in all of N') with empty named intersection: Σ_{S meets N'} n_S ≥ 61 − |∪b_N'|.
  All coefficients are trace-independent, so the Farkas/monotone-cut argument of B11.1 is unchanged; each row's cut
  literals are "its validity condition changed (b_F∩P_k ≠ N'*, single point changed, N'* ⊆ b_L, …) or its rhs weakened".
* `w11e_sub.py` / `w11e_queue.sh`: the Benders driver with this oracle; new certificates in `w11e_certs/`; each is
  re-checked by the independent `w11e_recheck.check` BEFORE its cut is added; the old pool `w11b_certs/` is re-used.
* `w11e_recheck.py` (independent of both oracles; re-derives every row instance from the stored traces with frozensets,
  every allowed column, gap, exactly): `108/108 OK (23 generic); |E| {2: 67, 3: 24, 4: 17}; row kinds {L 82, D1 342,
  A 46, W7F 4, SA 3, T 5, R3 2, L0 8}`.  `w11e_enctest.py 60 9`: `60 certificates x 10 trace vectors, all agree
  (372 SAT/holds, 228 UNSAT/violated)` (perturbations half inside base edges, to exercise the 5-pair condition literals).
* `w11_realize.py`: from a STALL, integer n_S (|F| = 21 exactly, Lemma A) + lazy literal L on every subfamily (exact DFS).

**Sub-instance B** = the 7 γ-type singles (1,2):T123_0,1; (1,3):T123_0,1; (2,3):T123_0,1,2 (full slots 11,12,15,16,21,22,23).
* Old oracle: STALL at it 5. Extended oracle (no L0): STALL at it 39. With L0: STALL at it 58 (w11e_B_stall.json).
* **COMPUTED, literally checked: B is realizable.** w11_realize.py on the last stall gave an 11-edge hypergraph
  (P0..P3 + the 7 singles, 128 points, all edges of size 21; file w11_B_real.json, sha256 0c5ce2d3…; copy
  w11_B_real_keep.json). Independent checker w10x_verify.py:
  `LemmaA min pair 5; L: subfamilies with union <= 60 examined 235 violations 0; 5-pairs 50 violations {R3 0, SA 0, D1 0,
  W7 0, NK 0, TT 0}`; no triple without a common point; each single meets its N_ij in exactly its type and each side in 5.
  **Meaning:** no argument that uses only these 11 edges (with L, Lemma A, F1, R.3, S(a), D1, W7-I, TT at every 5-pair)
  can refute N-K4. A refutation must involve more singles (other types / the pairs through P0) or further edges (τ-edges,
  second generation). This is not a counterexample to anything (τ = 2 for this partial family).
* Running at 17:40 EDT: w11e queue on **C** = all 9 γ-type singles (slots 11–13, 15–17, 21–23).
- 21:22 y1 DRAT-core route: fresh CaDiCaL solve of the full y1 CNF **UNSAT in 857 s** (binary DRAT 693 MB). drat-trim -c was
  killed by me at 21:28 (RSS 1.76 GB and growing, over the 2 GB per-job budget with the box at ~5.7 GB); no core. y1 is superseded
  by z1 (z1's slots ⊂ y1's slots, so a certificate for z1 also covers y1). Assumption-core on z1 running (w11n33z1_core.log).
- 21:40 assumption-core on z1 also **timed out** (1150 s, round 0). 21:45 DRAT route on z1: fresh CaDiCaL solve of the full z1 CNF
  (1105528 vars, 6878256 clauses) **UNSAT in 896 s**, binary DRAT 539 MB; drat-trim -c started (RSS ≈1.3 GB, stable).
  (An incremental-replay variant, w11n_replay.py, was started as a hedge and killed when the fresh solve finished.)

### B11.6 Loop improvements (17:40–18:30 EDT)
* **Sparse certificates**: after the dual LP proves infeasibility, a phase-2 LP minimises Σy + Σκ subject to gap ≥ 1;
  typical certificates shrank from ~9 rows to 2–5 rows (e.g. L0 + two Lemma-A rows, κ = 1). Fewer rows = fewer literals =
  stronger cuts.
* **Generic GD1 cuts (trace-free; PROVED)**: for a slot F with |b_F∩P_k| = 5 (so (P_k,F) is a 5-pair, N = P_k∩b_F) and
  another slot L with N ⊄ b_L: **GD1a** |b_L∩P_k∖b_F| ≤ 4 and **GD1b** |b_L∩(P_k∪b_F)| ≤ 9.
  *Proof.* D1 at (P_k,F): |L∩(P_k∪F)| = |b_L∩(P_k∪b_F)| + |L∩F∩U| ≤ 9 (b): drop the U-term. (a): Lemma A gives
  |L∩F∩U| ≥ 5 − |b_L∩b_F|, so |b_L∩P_k∖b_F| + max(5, |b_L∩b_F|) ≤ 9. ∎  Clause: [|b_F∩P_k| ≥ 6] ∨ [P_k∩b_F ⊆ b_L] ∨ ineq.
  Checked: `w11e_gd1test.py`: violations detected on stored master solutions, 80/80 encoder-vs-semantics agreements;
  each GD1 record is re-checked (violated at its stored traces) by w11e_recheck.check_gd1.
* **Symmetric images** (w11e_sym.py): group of order 24 generated by S3 on γ = T123, the swap of the two α = T023 points,
  and σ = (P2 P3) (T012↔T013, p02↔p03, p12↔p13, O2↔O3). Soundness does not rest on the group: every image is a
  stand-alone certificate re-checked by the independent checker before use (test: 1380/1380 images of 60 certificates
  re-check). New certificates get their images immediately; `w11e_symclose.py C` added 13170 re-checked images of the
  1056 older certificates applicable to C (w11e_symclose.jsonl).
* Sub-instance C (9 γ singles): 136 iterations so far, master never UNSAT, no stall; restarted 18:27 EDT with the closure.
- (Wave 11 noK4, continued) 21:57 **(3,3) z1: drat-trim on the FULL z1 CNF (6878256 clauses) + the 539 MB CaDiCaL proof:
  `s VERIFIED`** (715 s; 405437 clauses and 401390 lemmas in the core, 0 RAT lemmas). This certifies the whole z1 instance
  (scratch CNF/proof deleted by the chain after the map step; reproducible with w11n_dratcore.py build/solve/trim, ~30 min; log
  w11n33z1_dcore.log). Core mapped back: **2394 instances** {D1 786, SA 511, L 398, R3 319, W7 285, N24 95}, no TT →
  w10x_w11n33z1_dcore.json. ~22:00 second sandbox restart (killed the first rebuild/certificate run of that core; its log was lost).
- (Wave 11 noK4) 22:21 **(3,3) certificate C3: independent deterministic rebuild (w10x_cert.py) of the 2394-instance core,
  w10x_w11n33z1_dcore.cnf (799243 vars, 4641833 clauses; 17 slots = 16 first-generation singles + J31, K = 104 = KB bound):
  CaDiCaL UNSAT 297.8 s, drat-trim `s VERIFIED`** (669 s; DRAT 785 MB). SHA-256 in w10x_w11n33z1_dcore_cert.sha256:
  w10x_w11n33z1_dcore.cnf 69911893…; w10x_w11n33z1_dcore.cnf.drat 3efdd06d…; 
  Controls (drop-one-kind, nonk, noSB) running: w11n33z1_dcore_cert.log. Core refinement (w10x_core.py on 2394) running.

### B11.7 Soundness control against a literal configuration; status at 18:55 EDT
* **Control (w11e_realtest.py B w11_B_real_keep.json):** the literally verified 11-edge configuration of B satisfies the B
  master built WITHOUT symmetry breaking plus every applicable cut (8230 certificates: both pools + symmetric images;
  1.15 M cut clauses): `realized configuration vs base(noSB)+all cuts: SAT (consistent)`. So neither the w8sat master
  encoding nor any of these cuts excludes this real configuration (a direct test of soundness, stronger than the
  per-certificate checks).
* **C** (9 γ singles): it 138 done (master 517 s with 14262 applicable certificates incl. the closure), no stall, no UNSAT.
  A second sandbox restart (~18:00 EDT) cost one iteration. Master solves are now 2–9 min, so a 19-min chunk gives 2–6
  iterations. Chunks that end without a completed iteration rotate the solver (CaDiCaL+phases → CaDiCaL → Glucose 4).
* Loading: certificates are packed into w11_pack.jsonl (w11_pack.py); load time 421 s → 10 s.
* **Orchestrator running:** `w11e_chain.sh` (C up to 8 chunks; if C is realized → A up to 8 chunks; if A realized → F).
  On UNSAT, w11e_queue.sh runs w11e_finish.sh (dump, CaDiCaL DRAT + drat-trim, nocuts control, w11e_recheck, w11e_enctest),
  log w11e_TAG_cert.log. On STALL it runs w11_realize.py + w10x_verify.py, log w11e_TAG_realize.log.
  A sandbox restart kills it; resume with `cd work/e616/t21 && setsid nohup ./w11e_chain.sh &`.
- (Wave 11 noK4) ~22:48 (3,3) C3 controls so far (w11n33z1_dcore_cert.log): drop N24 **SAT** (170 s), L **SAT** (218 s), D1 **SAT**
  (137 s), SA **SAT** (212 s), W7(+NK) **SAT** (219 s); **drop R3: UNSAT** (318 s; drat-trim of it running). So the lazy R3 instances
  are redundant here (the drat-trim core is not minimal: assumption-based minimisation of the 2394 instances timed out at 1150 s,
  log w11n33z1_dcore_core.log). This does not affect soundness; it only means R3 (R.3 at non-base 5-pairs) is not needed for (3,3).

### B11.8 Status when this agent handed off (18:50 EDT / 22:50 UTC)
* **N-K4 (3,2,1,1) is still NOT decided.** No UNSAT, no DRAT certificate, no realized 24-single configuration.
* Proved/verified this wave: GD1a/GD1b (B11.6); the B realization (B11.5, literally checked); the soundness control
  (B11.7). Checks: `w11e_recheck.py`: 1310/1310 w11e certificate files OK (117 generic); `w11b_recheck.py`: 2204/2204;
  every symmetric image re-checked at creation; `w11e_enctest.py 120 13`: 120×10 agree.
* C at it 143 (18 LP cuts + 270 images in the last iteration), orchestrator w11e_chain.sh running in the background.
* Honest outlook: a 7-of-9 sub-family is realizable. If C, then A, then F also stall and realize, the conclusion is that
  the 24 first-generation singles are jointly consistent under every lemma used here. N-K4 would then need edges beyond
  first generation (τ-edges / second-generation singles), as NK4.6 already suggested. Untested gap in the oracle:
  lemmas at NEW–NEW 5-pairs (|F∩G| = 5 including outside points) are not modelled in the LP (they are disjunctive).
  w11_realize checks them literally on the candidate configurations.
- (Wave 11 noK4) ~22:50 third sandbox restart: killed the drat-trim of the drop-R3 control (its solve was UNSAT) and the remaining
  controls. Resumed 22:53 with w11n_ctrl_resume2.sh: nonk, then noSB.
- (Wave 11 noK4) 23:00 (3,3) C3 control **nonk: SAT** (238 s). So (3,3), like (3,4) and (2,4), is specific to N-noK4. Both kept
  certificates re-hashed after the restarts: `sha256sum -c` OK for w10x_w11n33z1_dcore.* and w10x_w11n34min.*.
- (Wave 11 noK4) 23:13 (3,3) C3 control **noSB: UNSAT (552 s), drat-trim `s VERIFIED`** (401 s). **All (3,3) controls done.**

### W11.6 Final summary, caveats and files (Wave 11 noK4; 23:15 UTC = 19:15 EDT)
| class | certificate to cite | slots / K | instances | result | controls |
|---|---|---|---|---|---|
| (3,4)/(4,3) | w10x_w11n34min.cnf + .drat | 16 g1-singles + J31 / 104 | 637 | UNSAT, `s VERIFIED` | drop N24/L/D1/SA/W7/R3 all SAT; TT absent; nonk SAT; noSB UNSAT (verified on the 21-slot set) |
| (3,3) | w10x_w11n33z1_dcore.cnf + .drat | 16 g1-singles + J31 / 104 | 2394 | UNSAT, `s VERIFIED` (also the full 15626-instance lazy CNF verified) | drop N24/L/D1/SA/W7 SAT; **drop R3 UNSAT** (R3 redundant); TT absent; nonk SAT; noSB UNSAT `s VERIFIED` |
- **Coverage.** No sub-cases: each class is one instance whose slots all exist in every N-noK4 configuration containing a
  class-(a,c) 5-pair (W11.1). (4,3) = (3,4) with E1↔E2 swapped. With Wave 10 ((2,4)/(4,2)), N8.0 and W6-U, **N-noK4 is closed
  (computer-assisted), so Case N reduces to N-K4.**
- **Caveats (honest).** (i) Not refereed. The Wave 10 referee re-encoded only the (2,4) core. Still to check independently: the N24
  tag, the generic τ-edge slot J31 (ν = 5 in KB), and the 637 + 2394 instance lists (e.g. with sat/w10ref/ref_enc.py extended by
  N24). (ii) The (3,3) and (3,4) results depend on the Wave 10 theorem (drop N24 SAT) and on NK (nonk SAT). (iii) The (3,3) core is not
  minimal (assumption-based minimisation timed out twice at the 20-min cap). (iv) Solver: CaDiCaL 1.5.3 via pysat (work/e616/pylib
  after the restarts, python-sat 1.9.dev16); checker work/e616/tools/drat-trim.
- **Files (work/e616/t21/).** Drivers: w11_exact.py (lazy loop), w11n_go.sh, w11n_mindrop.py (multi-edge drop), w11n_ctrl.sh /
  w11n_ctrl_resume2.sh (certificate + controls), w11n_core.sh, w11n_dratcore.py + w11n_dc_chain.sh (DRAT-based core),
  w11n_replay.py (incremental replay with proof; not needed in the end). Checkpoints: w10x_w11n34x1.json, w10x_w11n34x1_core.json,
  w10x_w11n34x1_core_noJ04.json, w10x_w11n34min.json, w10x_w11n33y1.json, w10x_w11n33z1.json, w10x_w11n33z1_dcore.json.
  Certificates: w10x_w11n34min.cnf/.drat (+ _cert.sha256), w10x_w11n34x1_core(.cnf/.drat), w10x_w11n34x1_core_noJ04(.cnf/.drat),
  w10x_w11n33z1_dcore.cnf/.drat (+ _cert.sha256). Logs: w11n34x1*.log, w11n34min_cert.log, w11n33y1*.log, w11n33z1.log,
  w11n33z1_dcore.log, w11n33z1_dcore_cert.log, w11n33z1_core.log, w11n33z1_dcore_core.log.

## Wave 12 N-K4 tau-edges (2026-10-15, started 19:15 EDT; computational)
**Status: in progress, UNDECIDED — see W12.6 for the current result line. Nothing below is an UNSAT claim unless it says VERIFIED.**
Hypotheses. Base = the (3,2,1,1)-K4 P0..P3 (w10x `k4:3211`, nk=False). **NK is never used** (no `nonk`/`no24` options): the
Wave 10–11 noK4 theorems assume "no K4 anywhere" and are NOT available here. Encoded lemmas = the refereed/proved set of X.1
minus NK/N24: A, L/XL, R1, R3, SA, D1, W7 (= W7-I, a global theorem), TT. Every slot is "an edge avoiding a fixed 4-set of
named points" (exists by τ ≥ 5), so one UNSAT instance kills N-K4 outright (same coverage argument as W11.1); K = KB bound.

### W12.1 Method: exact-encoding τ-CEGAR (work/e616/t21/w12_cegar.py, w12_ext.py, w12_scan.py, w12_go.sh, w12_run.sh)
* Lesson from Wave 11 noK4 (3,3)/(3,4): the 16 first-generation singles alone were REALIZED (violation-free, τ = 2,
  transversal {al0,cl0}); J31 avoids {al0,al1,al2,cl0} ⊇ that transversal, i.e. 4 of the 6 points of G∩H. So J31 is "an edge
  avoiding a small transversal of the realized partial family, completed inside the shared core".
* Wave 12 automates exactly this: run the w11_exact lazy loop on a slot list; if it REALIZES, enumerate the 4-sets B of named
  points that are transversals of the literal realized family, and add one slot "edge avoiding B"; warm-start (instances
  remapped by label) and repeat; stop at UNSAT.
* Selection (heuristic; soundness never depends on it): prefer B ⊆ S10 = {v,w}∪m3∪α∪γ, then B ⊆ core; and prefer B that is
  **non-extendable**: w12_ext.py (CP-SAT) shows that NO 21-set avoiding B can be added to the fixed realized family under
  Lemma A + L(all subfamilies with union ≤ 60) + D1/R3 at every 5-pair + SA/W7 against existing singles. A non-extendable B is a
  genuine cut of that realization (J1/JB1/JB2, chosen before this filter existed, were extendable).

### W12.2 COMPUTED (literal, independently checked): 10 first-generation singles of the K4 are jointly REALIZABLE
* Slots: the 7 γ-singles of sub-instance B (B11.5) + the three (P0,P1)-singles of types m3 (gen1auto indices 0,1,2,11,12,15,16,
  21,22,23), K = 60 = KB bound, eager2+eager3(g1)+f1all. w11_exact lazy loop (log w12m1.log, 2 chunks, ~45 it): violation-free.
* Literal configuration w12_M10_real_keep.json (14 edges, 159 points; sha256 0eccfb19…). Independent checker w10x_verify.py:
  `LemmaA min pair 5; L: subfamilies with union <= 60 examined 500 violations 0; 5-pairs 75 violations {R3 0, SA 0, D1 0, W7 0,
  NK 0, TT 0}; cross-type classes {(2,3):8, (3,2):14, (3,3):21, (4,4):6}; tau = 2 e.g. {T012_0, T023_0}`.
* Meaning: extends B11.5 (7 singles). No refutation can use only these 14 edges. Not a counterexample (τ = 2).
* Side chain B (7 γ-singles + τ-edges J1{v,w,α0,α1}, JB1{w,α0,m0,m2}, JB2{v,α0,α1,γ1}, JB3{w,γ0,γ1,m0}): realized at rounds
  0–2 (w10x_w12b1/Br1/Br2_real.json), round 3 undecided when paused (superseded by chain M, whose slots contain B's singles).

### W12.3 State at the crash (reconstructed 00:30 UTC = 20:30 EDT by the resuming agent, from the files only)
* Chain M (w12_M_state.json, w12_M_cegar.log): round 0 = w12m1 (10 singles) **REALIZED** (= W12.2). ext-scan found the first tried
  transversal non-extendable; τ-edge added: **JM1 = edge avoiding {v, α0, α1, m0}** (T012_0, T023_0, T023_1, p01_0), K = 68.
  Round 1 = w12Mr1 (11 slots): one full chunk, its 0–7 all SAT, violations 71 → 33 → 40 → 6 → 6 → 10 → 30 → 63 (not converging
  monotonically), checkpoint w10x_w12Mr1.json = 5088 instances; the second chunk had just rebuilt the model when the box restarted.
  **UNDECIDED** (neither realized nor UNSAT).
* Chain B (w12_B_state.json): 7 γ-singles + J1{v,w,α0,α1} + JB1{w,α0,m0,m2} + JB2{v,α0,α1,γ1} + JB3{w,γ0,γ1,m0}, K = 74:
  rounds 0–2 realized (W12.2); round 3 = w12Br3: 1 chunk (its 0–6, violations 45→43→12→16→41→36→21) + 1 iteration of a second
  (viol 5), checkpoint 3575 instances. **UNDECIDED.**
* No UNSAT, no certificate, no realization beyond W12.2 existed at the crash. Nothing was running after the restart.
* Observation (heuristic, selection only): of the 1012 named transversal 4-sets of the M10 realization, the ext filter (w12_ext.py)
  marks the large majority non-extendable (everything scanned containing v and an α point was), so "non-extendable" barely
  discriminates. Intersection over the four available realizations (M10, w12b1, w12Br1, w12Br2): 530 common transversal core
  4-sets; of the first 81 tested, 35 are non-extendable in all four (w12_commonext.py → w12_commonext.json).

### W12.4 Resume plan (00:35 UTC): chain N = chain M round 1 + three more τ-edges at once
* Several τ-edges per round are as sound as one (each slot exists in every counterexample by τ ≥ 5); this trades per-iteration cost
  for fewer rounds. Chain N (w12_N_state.json): the 10 singles + JM1 + **JN2{v,w,γ0,γ2}, JN3{v,α1,γ0,c3}, JN4{v,w,m0,a3_0}**
  (each non-extendable in all four known realizations), warm-started from w10x_w12Mr1.json (839 of its instances re-mapped),
  14 slots, **K = 92 = KB bound** (10·(21−9) + 4·(21−5) = 184, /2). Later rounds add up to 3 non-extendable τ-edges each (per=3).
  NK not used. Log w12Nr0.log / w12_N_cegar.log.

### W12.5 Milestone log (resume; times UTC)
- 00:45 w12Nr0 it 0: SAT (630 s; 6511 instances, 4.81 M clauses), 624 violations {L 239, D1 148, SA 124, W7 53, R3 48, TT 12};
  600 added. The 4 new τ-edges invalidate the old realizations as expected; nothing decided.
- CPU 0 is shared with the Wave 11 referee's glucose jobs (2–3 processes pinned to CPU 0), so this chain gets ≈ ⅓ of a core;
  one lazy iteration ≈ 10 min wall. The second solve of chunk 1 was cut by the 1150 s timeout (exit 124; the it-0 checkpoint was
  already saved). Driver-only patch (no effect on any clause): `w11_exact.py` option `hard=` stops a chunk after an iteration if
  elapsed + 1.15·(last solve time) would pass it; `w12_cegar.py` passes hard=1110. Chain restarted 00:58 with the patch.
- Background helpers left running: `w12_run.sh N` (driver, ≤12 rounds; state w12_N_state.json) and `w12_after.sh N` (waits for the
  driver; if it ends UNSAT runs w10x_core.py then w11n_ctrl.sh = certificate + drat-trim + drop-one-kind + noSB; log
  w12_N_after.log). Resume after a restart: `cd work/e616/t21 && setsid nohup ./w12_run.sh N sel=0,1,2,11,12,15,16,21,22,23 per=3
  maxrounds=12 & setsid nohup ./w12_after.sh N &`.
- ~01:14 **sandbox restart** killed chunk 2 during its it-1 solve (already > 15 min wall). Nothing lost from the checkpoint (6511
  instances). Second driver-only patch: `w11_exact.py` option `phase=1` saves each SAT model (w10x_TAG_phase.npy) and seeds the
  next chunk's CaDiCaL phases with it (`set_phases`; affects search order only, never the clause set). Relaunched 01:25 with
  `w12_launchN.sh`. **Risk noted:** if a single solve needs more than ≈ 1100 s wall (it-1 did, under CPU-0 contention), every chunk
  dies inside the solve and the chain makes no progress; the remedy is a less contended core or fewer slots, not a longer timeout.
- 01:30 chunk 3 (first with the hard limit): it SAT (554 s; 6919 instances, 5.53 M clauses), **408 violations** {L 124, SA 113,
  W7 67, D1 65, TT 21, R3 18}; 408 added; checkpoint 6919 instances. Chunk 4 (phase-seeded) started 01:30; its solve was still
  running at 01:43 (no visible speed-up from the phase hint yet).

### W12.6 Status at hand-off of the resuming agent (01:45 UTC = 21:45 EDT)
**N-K4 (3,2,1,1) is NOT decided. No UNSAT, no certificate, no new realization.** Exactly what is established in Wave 12:
1. COMPUTED + independently checked: base + 10 first-generation singles (7 γ-singles + 3 m3-singles) is REALIZABLE (W12.2,
   w12_M10_real_keep.json, τ = 2). Also realizable: 7 γ-singles + J1, JB1, JB2 (w10x_w12Br2_real.json; W12.2 side chain).
2. τ-edges tried so far (each = "an edge avoiding the 4-set", sound slot by τ ≥ 5): J1{v,w,α0,α1}, JB1{w,α0,m0,m2},
   JB2{v,α0,α1,γ1}, JB3{w,γ0,γ1,m0} (chain B, 7 singles; undecided with all four), JM1{v,α0,α1,m0} (chain M, 10 singles; undecided),
   and chain N = 10 singles + JM1 + JN2{v,w,γ0,γ2} + JN3{v,α1,γ0,c3} + JN4{v,w,m0,a3_0} (K = 92; undecided, 2 lazy iterations
   completed: 624 → 408 violations).
3. Nothing about N-noK4 (NK, N24) is used anywhere in Wave 12.
Honest outlook: at ≈ 10 min per lazy iteration on a shared core, and with the first chain-M round having needed ~30 iterations
just to realize 10 singles, an UNSAT (if it exists at this slot set) is several hours of wall time away, and further rounds
may be needed. The ext filter does not discriminate between τ-edges (most transversal 4-sets are "non-extendable"), so the
choice of τ-edges is still essentially blind; a structural lemma (NK4.6 (1), "one-deviant" propagation) would be a better guide.
**Left running:** chain N driver (w12_run.sh N, ≤ 12 rounds) and w12_after.sh N (core + certificate + controls on UNSAT).
Read w12_N_cegar.log, w12Nr*.log, w12_N_after.log; restart with work/e616/t21/w12_launchN.sh after a sandbox restart.

## Wave 13 N-K4 compute (2026-10-16, started 00:18 EDT = 04:18 UTC; computational; nothing here is UNSAT unless marked VERIFIED)
### W13.0 State found at start
* The box had just restarted (uptime 0); chain N was dead. Its record since W12.6: chunk 3 (01:30 UTC) was the LAST completed
  lazy iteration (408 violations). Chunks 4–6 (01:30, 01:49, 03:35 UTC) never finished a single solve inside the 1150 s chunk
  (exactly the W12.5 risk: one solve > ~1100 s wall under CPU-0 contention). So chain N made **no progress for ~3 h**; still
  undecided, checkpoint w10x_w12Nr0.json = 6919 instances.
### W13.1 Relaunch (04:19 UTC; w13_launchNP.sh)
* Driver-only change: w12_go.sh now pins to `taskset -c ${W12CPU:-0}` (default unchanged).
* **Chain N** relaunched on CPU 0 (now an uncontended core at launch), same slots, same checkpoint.
* **Chain P (new, sub-instance)** on CPU 1: only the 3 m3-singles (sel 0,1,2) + the same four τ-edges JM1, JN2, JN3, JN4;
  K = (3·12 + 4·16)/2 = 50 = KB bound; warm-started from w10x_w12Nr0.json (instances whose edges all occur in P). Rationale:
  an UNSAT needs only some slots, and P's model is far smaller. Sound for the same reason as N: every slot is "an edge avoiding
  a fixed 4-set of named points" (exists by τ ≥ 5), NK not used. If P realizes, the CEGAR adds ≤3 τ-edges per round (per=3).
* w12_after.sh N and w12_after.sh P wait for their drivers and on UNSAT run core → certificate + drat-trim + drop-one controls.
### W13.2 Milestone log (times UTC)
- 04:21 **Chain P round 0 REALIZED** (12 lazy its, < 2 min): literal configuration w10x_w12Pr0_real.json (11 edges = base 4 +
  3 m3-singles + JM1, JN2, JN3, JN4; 132 points; sha256 d79f55231f054d6b…). Independent check w10x_verify.py: LemmaA min pair 5;
  L: 245 subfamilies with union ≤ 60, 0 violations; 40 5-pairs, violations {R3 0, SA 0, D1 0, W7 0, NK 0, TT 0}; **τ = 2**
  (27 minimum transversals, 21 of them through T123_1; w13_mintrans.py). Meaning: the four W12 τ-edges are jointly consistent with
  the m3-singles; no refutation uses only these 11 edges.
- 04:21 CEGAR added JP1a{T012_0,T123_0,T123_1,T123_2}, JP1b{T023_0,T123_1,T123_2,p01_2}, JP1c{T023_0,T123_1,T123_2,p01_1}
  (transversal 4-sets, ext-non-extendable; JP1b/c each contain 2 of the 27 minimum 2-transversals, the max any 4-set reaches is 4).
  Round 1 (w12Pr1, K = 74): it 0 SAT in 8 s, 192 violations.
- 04:21 CPU 0 is again shared with the referee (drat-trim + kissat cube jobs), so chain N gets ≈ ⅓ core again (stall risk of W12.5).
- 04:25 **Chain P round 1 REALIZED** (21 its): w10x_w12Pr1_real.json (14 edges = base + 3 m3-singles + JM1, JN2–4, JP1a–c;
  143 points; sha256 64784ec7c1ca239d…). w10x_verify.py: LemmaA min 5; L 569 subfamilies, 0 viol; 70 5-pairs, all lemma counts 0;
  **τ = 2** ({T013_0, T023_0}). Added JP2a{T013_0,T023_0,T023_1,p01_0}, JP2b{T013_0,T023_0,T123_0,p01_2},
  JP2c{T023_1,T123_0,T123_1,p01_0}; round 2 (w12Pr2, K = 98) started.
- 04:38 Chain N: 4th consecutive chunk without a completed solve (CPU 0 ≈ 40 % share with the referee). **Chain N paused** (killed;
  checkpoint w10x_w12Nr0.json kept, resumable with w12_launchN.sh). Its slots are dominated in usefulness by P's for now.
- 04:39 **Chain Q (new)** on CPU 0: τ-edges ONLY — the 10 τ-edges of P round 2 (JM1, JN2–4, JP1a–c, JP2a–c), no first-generation
  singles; warm from w10x_w12Pr2.json; per=3. Encoder-side change, selection only: w10x_exact.py line 432 now accepts `sel=none`
  (empty single list); for any numeric sel the clause set is unchanged. Sound for the same reason (every slot = an edge avoiding a
  fixed named 4-set). P round 2 meanwhile: its 0–5 SAT, violations 434 → 142 → 301 → 27 → 72 → 24 (≈ 1–3 min per solve).
- 04:43 **Chain P round 2 REALIZED**: w10x_w12Pr2_real.json (17 edges = base + 3 m3-singles + 10 τ-edges; sha256 f44d6d34f4a99f40…).
  w10x_verify.py: LemmaA min 5; L 949 subfamilies, 0 viol; 113 5-pairs, all lemma counts 0; **τ = 2** ({T013_0, T123_1}).
  Added JP3a{T013_0,T123_1,p01_1,p01_2}, JP3b{T013_0,T123_0,T123_1,T123_2}, JP3c{T013_0,T123_0,T123_1,p01_2}; round 3 (w12Pr3,
  16 slots, K = 118).
- 04:44 Chain Q stopped: its slot set is a SUBSET of P round 2's, so the P r2 realization already realizes it (redundant; my
  mistake, cost ~6 min). Lesson: a sub-instance is only informative while its super-instance is undecided.
- 04:45 **Chain R (new)** on CPU 0 = chain N minus the 3 m3-singles: 7 γ-singles (sel 11,12,15,16,21,22,23) + JM1, JN2–4;
  K = 74; warm from w10x_w12Nr0.json; per=3. Not dominated by P (different singles).
- 04:45 w13_tau_candidates.json appeared (structural agent; rigidity ranking over the 145 symmetry orbits of core 4-sets). It also
  flags {v,γ0,γ1,γ2} and {w,γ0,γ1,γ2} as "avoider always a first-generation single", i.e. P's JP1a and JP3b are equivalent to
  single slots (sound, just weak).
- 04:48 Chain R stopped (only its build had run; checkpoint kept). **Chain S (new, priority) on CPU 1**: the 3 m3-singles +
  the candidate tiers A1{v,w,α0,α1}, A2{v,w,c3,c4}, A3{α0,α1,c3,c4}, B1 (3 images), B2 (6 images), B4 (2 images) = 14 τ-edges
  (all orbit images, under the unique labels JS*; A1 = J1 of chain B, now for the first time together with the m3-singles).
  Warm from w10x_w12Pr3.json — warm-start maps instances BY LABEL using the checkpoint's own slot definitions, so the JS* labels
  are deliberately new: only base/single instances transfer (no risk of a label meaning a different 4-set). Chain P moved to CPU 0.
- 04:48–04:59 S round 0 (K = 130): its 0–2 SAT in 38/144/276 s, violations 737 → 1194 → 779 (much harder to realize than any P
  round so far — consistent with the candidates being more constraining, but this is NOT evidence of UNSAT).
- 04:59 Chain P paused again (no solve completed in 11 min on shared CPU 0; checkpoint w10x_w12Pr3.json kept). **Chain T (new) on
  CPU 0** = sub-instance of S: 3 m3-singles + A1, A2, A3, B1a–c (6 τ-edges, same JS* labels and sets as S, so S's instances
  transfer); informative while S is undecided.
- 04:59–05:03 T round 0 (K = 82): its 0–6 SAT, violations 45 → 55 → … → 210 → 21. S round 0 chunk 2 was mid-solve.
- ~05:03 **sandbox restart** killed S and T (checkpoints kept: S 4868, T 1718 instances). 05:13 relaunched with
  **w13_launchST.sh** (S on CPU 1, T on CPU 0; the referee's two kissat jobs also sit on CPU 0).
- 05:13 Somebody's automatic `w12_launchN.sh` relaunched chain N on CPU 0; I killed it again (05:14) and added a guard: the file
  w12_N_PAUSED makes w12_launchN.sh exit with a notice. **After a restart, use w13_launchST.sh.**
- 05:18 **Chain T round 0 REALIZED**: w10x_w12Tr0_real.json (13 edges = base + 3 m3-singles + A1{v,w,α0,α1}, A2{v,w,c3,c4},
  A3{α0,α1,c3,c4}, B1 ×3; sha256 1a9f081a9aeb66de…). w10x_verify.py: LemmaA min 5; L 399 subfamilies, 0 viol; 66 5-pairs, all
  lemma counts 0; **τ = 2**, 8 minimum transversals, 5 through p03_0 (= a4_0). So the top-rigidity candidates A1–A3 + B1, even
  together with the m3-singles, do NOT kill N-K4 by themselves (S additionally has B2 ×6, B4 ×2: still undecided).
- 05:21 Driver patch (selection only, no clause changes): w12_cegar.py option `mt=1` ranks transversal 4-sets B by the number of
  minimum transversals of the realization they CONTAIN (the new edge avoiding B then destroys all of them), and `avoidB=` skips
  the 10 4-sets whose avoider is always a first-generation single (orbits of the structural agent's redundant list,
  w13_redundantB.txt). T's default round-1 pick (JT1a–c, chosen before the patch, never solved) was discarded (files renamed
  *_discarded*) and re-selected: JT1a{v,γ0,m0,a4_0}, JT1b{γ0,m0,m2,a4_0}, JT1c{γ0,γ2,m0,a4_0} (each contains 3 of the 8 minimum
  transversals). Round 1 (w12Tr1, K = 106) started 05:21 on CPU 0. w13_launchST.sh now passes mt=1 for both chains.
- 05:13–05:31 S chunk 3 completed no solve (the box's load is ≈ 6.5 on 2 cores from other projects' jobs; S got ≈ 25 % of CPU 1).
  **Chain S paused** (checkpoint w10x_w12Sr0.json, 4868 instances). **Chain U (new) on CPU 1** = the other half of S: 3 m3-singles
  + A1 + B2 ×6 + B4 ×2 (9 τ-edges, same JS* labels/sets), warm from S, mt=1. Together T and U cover all of S's slots; an UNSAT of
  either is an UNSAT of N-K4. Restart script now **w13_launchTU.sh**.
- 05:26 T round 1 it 0: SAT (194 s), 334 violations.
- 05:55 T round 1: chunk 2 its 0–1 SAT, violations 91 → 17 (checkpoint 3014 instances). U round 0: its 0–8 + 0–1, violations
  305 → 136 → … → 1 → 53 → 33 → 18 → 9 (checkpoint 2946 instances).
- ~05:58 **second sandbox restart**; 06:01 relaunched T and U with w13_launchTU.sh (checkpoints intact).
- 06:05 **Chain U round 0 REALIZED**: w10x_w12Ur0_real.json (16 edges = base + 3 m3-singles + A1 + B2 ×6 + B4 ×2; sha256
  be74a0705e917318…). w10x_verify.py: LemmaA min 5; L 765 subfamilies, 0 viol; 90 5-pairs, all lemma counts 0; **τ = 2**, 6 minimum
  transversals ({γ0,a4_1}, {γ1,m0}, {γ1,a3_0}, {γ1,a4_1}, {γ2,m0}, {γ2,a4_1}). So both halves of S (T r0 and U r0) are realizable
  separately; S itself (all 14 candidate τ-edges at once) is undecided. mt=1 added JU1a{γ1,γ2,m0,a4_1} (covers 4 of the 6),
  JU1b{γ0,γ1,γ2,a4_1}, JU1c{γ1,γ2,m0,a3_0}; round 1 (w12Ur1, K = 114) on CPU 1.
- 06:11 **Chain T round 1 REALIZED**: w10x_w12Tr1_real.json (16 edges = base + 3 m3-singles + A1–A3 + B1 ×3 + JT1a–c; sha256
  aa22ab82e17a29c0…). w10x_verify.py: LemmaA min 5; L 762 subfamilies, 0 viol; 86 5-pairs, all lemma counts 0; **τ = 2**
  ({w, a3_0}; 8 minimum transversals again). Added (mt=1) JT2a{w,γ1,γ2,a3_0}, JT2b{α0,γ0,γ2,a3_0}, JT2c{w,γ0,γ2,a3_0}; round 2
  (w12Tr2, K = 114). Observation (not a proof): every realization so far has τ = 2 with all 45 outside points O* used and the
  minimum transversals simply MOVE when they are cut; each realized round needs only 5–25 lazy iterations.
- 06:11–06:29 T round 2 it 0: SAT (590 s on shared CPU 0), 770 violations; U round 1 its 0–1: SAT (300/203 s), 924 → 596
  violations. One lazy iteration now costs ≈ 5–10 min wall per chain, so a round takes 1–3 h.
### W13.3 Status at hand-off (06:30 UTC = 02:30 EDT)
**N-K4 (3,2,1,1) is NOT decided. No UNSAT, no certificate.** Established in Wave 13 (all COMPUTED, each realization re-checked by
the independent literal checker w10x_verify.py: Lemma A, L on every subfamily with union ≤ 60, R3/SA/D1/W7/NK/TT at every 5-pair):
1. Realizable (so no refutation can use only these slots), all with τ = 2:
   P r0 = 3 m3-singles + JM1, JN2, JN3, JN4 (w10x_w12Pr0_real.json); P r1 = + JP1a–c (w10x_w12Pr1_real.json);
   P r2 = + JP2a–c, 13 τ-edges total (w10x_w12Pr2_real.json, 17 edges);
   T r0 = 3 m3-singles + structural candidates A1, A2, A3, B1 ×3 (w10x_w12Tr0_real.json); T r1 = + JT1a–c (w10x_w12Tr1_real.json);
   U r0 = 3 m3-singles + A1 + B2 ×6 + B4 ×2 (w10x_w12Ur0_real.json).
2. Undecided: N (10 singles + 4 τ, paused), P r3 (paused), S (3 m3-singles + all 14 candidate τ-edges, paused: solves > 18 min
   under the box's load), T r2 (running, CPU 0), U r1 (running, CPU 1).
3. Honest reading: with ≤ 1 realized round per ~20 min early and ≥ 1 h per round now, and every realization so far simply moving
   its τ = 2 transversals when they are cut, there is no sign yet that a bounded number of named-point τ-edges forces UNSAT.
   The rigidity-ranked candidates (A1–A3, B1, B2, B4) did NOT decide anything when split into two halves; jointly (S) undecided.
**Left running:** chains T and U (w12_run.sh T/U, mt=1, ≤ 20 rounds) and w12_after.sh T/U (on UNSAT: w10x_core.py, then
w11n_ctrl.sh = certificate + drat-trim + drop-one-kind + noSB; log w12_{T,U}_after.log). After a sandbox restart run
`work/e616/t21/w13_launchTU.sh` (NOT w12_launchN.sh, which is now guarded by w12_N_PAUSED). Coverage, if either ends UNSAT:
every slot is "an edge avoiding a fixed 4-set of named points (or a first-generation single)", which exists in every N-K4
counterexample by τ ≥ 5 / the single lemmas, so one UNSAT instance with K = KB bound refutes N-K4 outright (W11.1/W12 argument).
Patches made this wave (selection/driver only; no clause of any existing instance changed): w12_go.sh `W12CPU`; w10x_exact.py
`sel=none`; w12_cegar.py `mt=1`, `avoidB=`; w12_launchN.sh guard.

## Wave 13 N-K4 structure (2026-10-16, started 00:18 EDT; hand/structural route; a parallel "Wave 13 N-K4 compute" section is above)
Notation N.0(iii)/NK4: P0..P3, v=T012, w=T013, α={al0,al1}=T023, γ={g0,g1,g2}=T123, m3={m0,m1,m2}=p01, a3=p02, a4=p03,
c3=p12, c4=p13 (w8 names in brackets where needed). Core = these 16 points. Scripts in work/e616/t21/w13_*.py (PYTHONPATH=work/e616/pylib).
### S13.1 One-new-edge enumeration (COMPUTED, exhaustive, sound) — w13_enum.py
For one edge X (core trace b ⊆ core, o_i = |X∩O_i|) every proved constraint that involves only X and base edges:
F1/R.1, Lemma A, capacity, L3 (= L on {P_i,P_j,P_k,X}), D1 at the six base 5-pairs, W7-I at base pairs, and at DERIVED
5-pairs (P_i,X) (|X∩P_i| = 5): R.3 for base singles of (P_i,X), D1, W7-I, S(a). (The o-search over o_i ∈ {L_i, L_i+1},
L_i = max(0,5−|b∩P_i|), is complete: every constraint is monotone in o except the derived-pair triggers, which only fire at
|X∩P_i| = 5.) Result: **18217 feasible core traces** (w13_feas.json). Soundness control (w13_selftest.py): all 44 non-base
edges of the five literally verified realizations (w12_M10_real_keep, w11_B_real_keep, w10x_w12b1/Br1/Br2_real) pass:
`edges checked 44 violations 0`.
* Per single type (w13_singles.py): 70–285 feasible traces each; the only forced points are the trivial ones (type in,
  rest of N_ij out) plus the S(a)/R.3 exclusions ((1,2)-singles miss a4, (0,2)-singles miss c4, etc.). **So, one edge at a
  time, the singles are far from rigid** (cf. Lemma G, which needs the extra hypothesis v ∉ F).
* Avoiders (w13_B.py over all 1820 core 4-sets B): every B has ≥ 70 feasible avoider traces (minimum = the (1,2)-single
  of type c3 = avoider of {v}∪γ); the only B that NO single trace can avoid are {v}∪m3 and {w}∪m3 (their avoiders are the
  base-type (0,1)-singles of types w resp. v, i.e. P3/P2 look-alikes). **Consequence: no 4-set of core points is
  "forced-hit" for single-edge reasons; any principled τ-edge list must come from JOINT (≥ 2-edge) constraints among the
  singles.** Next: pairwise arc consistency over the 24 single domains (w13_dom.json: 6 908 (trace, O-vector) states).
### S13.2 The six apex inequalities (PROVED; = CP' W7-5 at the two 1-point triples) and first-gen single structure (PROVED)
(P0,P1,P2) and (P0,P1,P3) are 49-triples through v resp. w. CP' with each of the three edges as apex gives, for every edge F:
* F ∌ v: **(Av0)** |F∩(a4∪O0)| ≤ |F∩(γ∪c3)| − 1; **(Av1)** |F∩(c4∪O1)| ≤ |F∩(α∪a3)| − 1; **(Av2)** |F∩O2| ≤ |F∩({w}∪m3)| − 1.
* F ∌ w: **(Aw0)** |F∩(a3∪O0)| ≤ |F∩(γ∪c4)| − 1; **(Aw1)** |F∩(c3∪O1)| ≤ |F∩(α∪a4)| − 1; **(Aw3)** |F∩O3| ≤ |F∩({v}∪m3)| − 1.
(P_k∖(P_i∪P_j) and (P_i∩P_j)∖P_k read off N.0(iii).) Consequences, all by one or two lines:
* **(VW⁺)** F ∌ v,w: summing Av0+Aw0+Av1+Aw1 gives |F∩α| + |F∩γ| ≥ 2 + |F∩O0| + |F∩O1|; Av2/Aw3 give |F∩m3| ≥ 1 + max(o2,o3)
  (this is VW(i)); L3 at v and at w give |F∖(P0∪P1∪P2)| ≥ 12 and |F∖(P0∪P1∪P3)| ≥ 12.
* **(S01)** every (0,1)-single F (type m ∈ m3; v,w ∉ F): F∩(O2∪O3) = ∅ (Av2, Aw3 with |F∩({w}∪m3)| = 1), hence its 12 outside
  points lie in U; NT (W7-I) against P2 and P3 (types v,w; parts α∪a3 | γ∪c3 and α∪a4 | γ∪c4) gives |F∩(α∪a3)|, |F∩(α∪a4)|,
  |F∩(γ∪c3)|, |F∩(γ∪c4)| ≥ 2, so F∩γ ≠ ∅, and F∩γ = {g} forces c3, c4 ∈ F.
* **(S02)** every (0,2)-single (type x ∈ α∪a3; v ∉ F): F∩(c4∪O1) = ∅ (Av1); NT against P1 (type v of (P0,P2); parts {w}∪m3 | γ∪c3)
  gives |F∩({w}∪m3)| ≥ 2 (so F∩m3 ≠ ∅) and |F∩(γ∪c3)| ≥ 2 (so F∩γ ≠ ∅). Symmetric (S03): F∩(c3∪O1) = ∅, etc.
* **(S12)** every (1,2)-single (type y ∈ γ∪c3; v ∉ F): F∩(a4∪O0) = ∅ (Av0); NT against P0 gives |F∩({w}∪m3)| ≥ 2 and
  |F∩(α∪a3)| ≥ 2. Symmetric (S13).
* **(S23)** every (2,3)-single contains v or w. *Proof.* Suppose v,w ∉ F and F∩N23 = {x}; |F∩P2| = |F∩P3| = 5 (R.3) give
  a3'+c3'+o2 = 4 = a4'+c4'+o3. If x ∈ γ: Aw1 gives c3' ≤ a4' − 1 − o1 and Av0 gives a4' ≤ c3'; contradiction. If x ∈ α: Av0, Aw0
  give a4' ≤ c3' − 1, a3' ≤ c4' − 1, so c3' = c4' = 1, a3' = a4' = 0, and then Av1 gives c4' ≤ 1 + 0 − 1 = 0; contradiction. ∎
  (This contains the v,w-part of Lemma G and extends it to the α-types.)
All of these are reproduced by the exhaustive enumeration (w13_ranges.py prints the region ranges per type).
### S13.3 COMPUTED, NEGATIVE: pairwise information prunes nothing (so every remaining obstruction is ≥ 3-way)
* w13_ac.py: pairwise arc consistency over the 24 single domains with every sound pairwise rule (Lemma A with O/U overlap
  brackets, F1 with each base edge, S(a)+NT+S(b) for same-pair cross types, OO = L on {P_k,P_l,F,F'}, L on {3 base, F, F'},
  D1 at derived pairs (P_k,F)): 6908 → 6890 states (only 3+3+3 (0,1)-states and 6 per a3/a4-type removed), fixpoint at iteration 2.
* w13_tau.py: the avoider J_B of a core 4-set B against all 24 AC-reduced single domains, pairwise: e.g. B={v,w,α}: 109 → 73
  states, {v,w,γ_i,γ_j}: 106 → 106. Pairwise reasoning cannot rank τ-edges.
* w13_newB.py: for EVERY core 4-set B that meets all four P_i, some first-generation single type can locally avoid B (the only
  B no single can avoid are {v}∪m3, {w}∪m3, which P3 resp. P2 avoid). So "B forced-hit by every first-gen single" is FALSE
  for every useful B at the one-edge level; forced-hit can only be a joint (SAT-level) property.
* w13_squeeze.py: the L3 slack of B-avoiders is ≤ 1 per avoided triple for almost all B (≤ 2 for {v,w,α} with 3 triples): the
  configuration is uniformly near-tight, so "squeeze" does not discriminate either.
### S13.4 Lemma JA (PROVED; enumeration-checked): the avoider of {v,w}∪α is a fifth vertex of a 5-pair clique
Let J be any edge with J∩({v,w}∪α) = ∅ (exists by τ ≥ 5; {v,w}∪α = T012∪T013∪T023 = all triple points of P0). Write c = |J∩core|,
g' = |J∩γ| etc. Then:
(i) g' ≥ 2 + o0 + o1 (VW⁺ with α avoided), so o0 + o1 ≤ 1 and g' ∈ {2,3};
(ii) |J∩a3| ≥ 1 + c4' + o1 (Av1), |J∩a4| ≥ 1 + c3' + o1 (Aw1), |J∩m3| ≥ 1 + max(o2,o3) (Av2, Aw3);
(iii) **Σ_i |J∩P_i| ∈ {20,21}, so J meets at least three base edges in exactly 5 and the fourth in ≤ 6.**
*Proof of (iii).* All core points lie in P0∪P1, and J's core points m3,a3,a4,c3,c4 lie in 2 base edges, γ in 3, so
Σ|J∩P_i| = 2c + g' + Σo. L3 at v and at w: c + o0 + o1 + o2 ≤ 9 and c + o0 + o1 + o3 ≤ 9; adding, Σ|J∩P_i| ≤ 18 + g' − o0 − o1 ≤ 21,
and Lemma A gives ≥ 20. ∎ (Σ = 21 forces g' = 3, o0 = o1 = 0 and both L3 tight.)
(iv) Hence, e.g. when |J∩P_i| = 5 for i = 0,1,2, {P0,P1,P2,J} is again a K4 (4-fold intersection ⊆ {v}∖J = ∅) with triple vector
(1, |J∩m3|, |J∩a3|, |J∩(γ∪c3)|), and likewise {P0,P1,P3,J}: (1, m', a4', g'+c4'), {P0,P2,P3,J}: (2, a3', a4', g'). W7-I excludes
(4,1,1,1); N.0(i) requires sum ≥ 7. So J_A *propagates the K4* (new (3,2,1,1)- or (2,2,2,1)-K4s through P0).
Enumeration (w13_canon.py): 109 local states, only **15 region signatures** (the most rigid avoider among all 145 symmetry orbits
of base-transversal core 4-sets, w13_rigid.py); |J∩P_i| = (5,5,5,5) in 72 states, one 6 otherwise — matches (iii). In 106/109 states J
is itself a first-gen single of (0,1), (0,2) or (0,3) in an extreme shape (e.g. a (0,1)-single whose A-part is a3∪a4).
Checks: K4-specific, so vacuous on H(16,10,7), H(22,13,9) (no K4 there, N.2) and on the PG(2,4) skeleton (its empty-intersection K4s
are all (4,1,1,1)). The apex inequalities are instances of the refereed W7-5. Soundness of the enumerator: S13.1 self-test.
### S13.5 Why J31 closed noK4, and why the same move is empty in N-K4 (structural reading; not a proof about the certificate)
J31 avoids all of T_{E1GH} = α (3 points) plus one point of T_{E2GH} = γ. TU (L3 at α) then caps |J∩(E1∪G∪H)| ≤ 13 − c = 9 while
Lemma A on E1, G, H demands |J∩{v,ag}| + |J∩{w,ah}| + |J∩γ∖cl0| ≥ 6 (caps 2,2,3): a 1-unit squeeze on an edge that is NOT a single
of (G,H) (|G∩H| = 7 there), so it is a genuinely new rigid edge. In the (3,2,1,1)-K4 the analogous sets (α plus 2 of γ; γ plus v or w;
α∪{γ_i}…) all have |G∩H| = |P2∩P3| = 5, so their avoiders are **first-generation singles** (Lemma G family) — the J31 move is
already spent at generation 1. The K4 analogue that is not a single is the set of ALL triple points of one base edge,
{v,w}∪α (Lemma JA), whose avoider is squeezed by three L3's and six apex inequalities at once.
### S13.6 Deliverable: τ-edge candidate list (work/e616/t21/w13_tau_candidates.json; generator w13_mkcand.py)
Principle (stated honestly): no core 4-set is forced-hit by the first-gen singles at the 1- or 2-edge level (S13.3), so the list is
ranked by (1) invariance under the base symmetry group (order 576), (2) rigidity of the avoider (number of local region signatures,
w13_rigid.json), (3) not being a disguised first-gen single. Every entry is sound as a slot regardless of ranking (τ ≥ 5).
* **A1 {v,w,al0,al1}** (= J1; G-invariant; nsig 15; Lemma JA). Tried only in chain B (γ-singles only), where it was realized;
  **never with the m3-singles** (chains M/N/P). In the M10 realization every edge contains {v,w} or α; J_A is exactly the edge that
  breaks that dichotomy. Top recommendation for chains N/P.
* **A2 {v,w,c3,c4}**, **A3 {al0,al1,c3,c4}** (the other two G-invariant base-transversal 4-sets; nsig 95, 261). Untried.
* **B1** orbit of {v,w,g0,g1} (nsig 21; JN2 is one image — add the other two), **B2** {v,w,al_i,g_j} (orbit 6, nsig 33),
  **B3** {v|w}∪α∪{g_j} (orbit 6, nsig 46; JB2 one image), **B4** {v,α,c3}/{w,α,c4} (orbit 2, nsig 57), **B5** {v,w,g_i,c3|c4}
  (orbit 6, nsig 58). All images listed in the JSON with "tried_as".
* **Redundant as τ-edges** (avoider is always a first-gen single, so the slot just re-adds that single): {v}∪γ, {w}∪γ, {v,w,m_i,m_j},
  α∪{g_i,g_j}, {al_i}∪γ. (Chain P's JP1a = {v}∪γ and JP3b = {w}∪γ are of this kind: they add the (1,2):c3 / (1,3):c4 singles.)

## Wave 14 three-edge (2026-10-16, started 09:10 EDT; structural; nothing here is an UNSAT claim)
Box restarted at start (uptime 1 min): chains T/U of W13 were dead; NOT relaunched by this wave (light-CPU brief).
### W14.1 Common structure of the 11 literal realizations (COMPUTED; /tmp scripts, re-creatable from the description)
Files: w12_M10_real_keep, w10x_w12{b1,Br1,Br2,m1,Pr0,Pr1,Pr2,Tr0,Tr1,Ur0}_real.json.
* τ: 2 for nine of them, **3 for w12b1 and w12Br2** (7 γ-singles + J1(+JB1,JB2)); no 2-transversal there. Every 2-transversal
  found lies in the 16-point core except in Pr0 ({O0_i, g1} for all ten O0 points, i.e. g1 + "P0's private part").
  So the conjectured dichotomy "every edge ⊇ {v,w} or ⊇ α" (M10: transversals {v|w}×{al0|al1}, plus {v,c4},{w,c3}) is **NOT**
  common: Pr1/Pr2/Tr*/Ur0 have transversals like {g1,x0}, {y0,c3}, {g0,y1}; they move freely through the core.
* Every non-base edge has 9–11 named points (core 6–9, O-part 0–3) and 10–12 points in U, and meets every P_i in 5 (rarely 6–7).
* The realizations are 5-pair-saturated: 64–113 of the C(n,2) pairs are 5-pairs (e.g. 64/66 in b1, 113/136 in Pr2), and
  **K4s are everywhere**: 11–55 (3,2,1,1)/(2,2,2,1) K4s each, plus Σt = 8, 9 K4s ((3,2,2,1), (2,2,2,2), (3,2,2,2)).
  (W7-I: never (4,1,1,1).) So N-K4 is not an "isolated K4": any configuration is a dense web of tight 61-unions.
* Reading: a bounded edge set does not force small τ by itself; the τ = 2/3 is an artefact of having ≤ 17 edges. A refutation must,
  like W6-U, use an UNBOUNDED closure (W6-U used all 715 9-subsets of S). This is the frame for W14.2+.
* K4 cores drift: among the (3,2,1,1)-K4s of M10/Pr2/Ur0/b1, the 16-point K4 core shares only 9–16 points with the base core and
  uses 9–25 different O-points. So there is no fixed "S" (W6-U-style invariant set) visible in any realization.

### W14.2 Meta-lemma (PROVED, elementary): pure-L k-edge lemmas cannot cut a realization
Let R be a literal realization (every subfamily of R with union ≤ 60 has a common point; checked by w10x_verify.py). Any lemma
"every k edges X1..Xk of G (with the base) satisfy P", whose proof applies only L (incl. F1 and the union counts H/SQ/SF/OO/L3/
apex inequalities) to subfamilies of {P0..P3, X1..Xk}, holds for every k-tuple of edges of R, because R itself satisfies L on all
those subfamilies. Hence clauses from such lemmas are already implied by the lazy L of w10x_exact and **never exclude a
realization** (they can only speed a solve). This applies to every "three-edge lemma from union ≤ 60 ⇒ common vertex" the brief
asked for, however the outside points are counted. A clause that cuts a realization must come from a lemma whose proof uses
τ ≥ 5, i.e. the EXISTENCE of edges outside the slot set (Lemma A's transversal argument, R.2/R.3 singles, Lemma T witnesses,
W6-U relatives, D1/SA/W7/TT). Of these, the realizations already satisfy Lemma A, R3, SA, D1, W7, TT literally at every one of
their 5-pairs (W12/W13 checks). The existence facts they violate are exactly "an edge avoiding B exists" for their 2-/3-transversals
(and R.2 at derived 5-pairs) — and each such violation is repaired by the solver moving the transversal (W13.2).
### W14.3 Re-derivations tried this wave (PROVED, but NOT new: each reduces to a known item)
For a 49-triple (X,U,V) with apex t, traces τ_U = X∩U, τ_V = X∩V (τ_U∩τ_V = {t}, |τ_U∪τ_V| = 9), D_UV = U∩V∖{t} (4 points), and any
edge X' ∌ t: L3 + Lemma A on U and V give |X'∩(X∖(τ_U∪τ_V))| ≤ |X'∩D_UV| − 1 ≤ 3 = CP'/W7-5 (S13.2). Existence version: every
point t of every 5-trace X∩Y is such an apex (take the type-t single of (X,Y), R.2+R.3), so the apex inequality holds at EVERY trace
point of every edge; for the base this is S13.2, for derived pairs it is the D1/OO of the w11e oracle. Two t-avoiders Z,Z' against a
49-triple: |Z∩Z'∖(X∪U∪V)| ≤ (9−|Z∩(X∪U∪V)|) + (9−|Z'∩(X∪U∪V)|) = the 49-triple OO, inside lazy L. Avoiders of {v,w}: ≥ 6 of the 11
points m3∪α∪a3∪γ∪c3 and ≥ 6 of m3∪α∪a4∪γ∪c4 (from L3 + Lemma A), = VW⁺. Nothing beyond S13.1's enumeration.
No sanity check vs H(16,10,7)/H(22,13,9)/PG(2,4) was needed: no new lemma was produced (the meta-lemma is a statement about R).
### W14.4 Conjecture and recommended route (CONJECTURE; honest)
* Conjecture W14-C (what all evidence points to): every bounded set of slots (first-gen singles + named-4-set avoiders) is
  realizable; N-K4 has no bounded certificate of the W10–W12 type. Evidence: 11 realizations, τ = 2/3 transversals that move when
  cut, 5-pair saturation and K4 abundance (W14.1), the meta-lemma W14.2.
* The only known mechanism that closed a "tight 61" case without a bounded certificate is W6-U: an UNBOUNDED propagation
  (good pairs, Kneser-connectivity, all 715 9-subsets of S) plus one 4-edge L at the end. Recommended next step: a K4-propagation
  closure. Ingredients already proved: N.0(iv) and Lemma JA(iv) (new K4s through P0); Σt ≥ 7 and union = 54 + Σt for every K4
  (N.0(i)), so a K4 with Σt = 7 is exactly tight. Target lemma: show the set of (Σt = 7)-K4s reachable from one K4 by JA/N.0(iv)
  moves is closed and large enough to contain four edges with empty intersection, pairwise disjoint outsides and named union ≤ 12
  (as in W6-U's final step) — or a K4 with Σt = 6 (union 60), which L forbids. Neither is proved; the drifting K4 cores in W14.1
  are a warning that the closure set, if it exists, is not the base core.
* Compute side: do NOT spend more CPU on bounded τ-edge CEGAR (W12/W13 chains) expecting UNSAT; it is consistent with W14-C.

## Wave 14 global encoding (2026-10-16, started 09:10 EDT = 13:10 UTC; computational; nothing here is UNSAT unless marked VERIFIED)
Box had just restarted (uptime 0); W13 chains T/U were relaunched by someone else ~13:15 UTC (not by this wave). All jobs of this
wave run on CPU 0 with nice 10. Files: sat/t21/w14/ (PYTHONPATH=work/e616/pylib).
### G14.1 The reduction (PROVED; it is a relaxation, so UNSAT of it refutes N-K4)
Let G be an N-K4 counterexample with base P0..P3, core C (16 points). For a non-base edge F put tr(F) = F∩C, o(F) = (|F∩O_i|).
Model Φ: one Boolean x_t per feasible core trace t (the 18217 of w13_feas.json); clauses
 (COV) for every core 4-set B that no base edge avoids (1730 of the 1820): OR_{t∩B=∅} x_t;
 (CONF) ¬x_t ∨ ¬x_t' for every pair t ≠ t' such that NO state pair (t,o),(t',o') is pairwise-compatible (w14_compat.py).
Claim: x_t := [t = tr(F) for some non-base edge F] satisfies Φ. *Proof.* COV: τ ≥ 5 gives an edge avoiding B; it is not a base edge
(B was chosen so), so its trace avoids B. CONF: two distinct edges with traces t ≠ t' have states in the enumerated lists and satisfy
every proved pairwise lemma, so (t,t') is not a conflict pair. ∎  Points outside C are NOT needed: restricting τ ≥ 5 to core 4-sets
is a weakening, so how many edges an outside point lies in never enters (it would only matter for strengthening the cover side).
* States (w14_states.py): every (t,o) passing w13_enum.check, enumerated over a rigorous box (o_i ≥ L_i by Lemma A; o_i ≤ the
  CAP/D1/L3 bounds, each of which check() enforces) — **49967 states**, every feasible trace has ≥1 (consistent with S13.1).
* Pairwise compatibility (w14_compat.py; overlaps z_q = |F∩F'∩O_q| ∈ [pigeonhole lo, min], z_U ∈ [0,min(u,u')]): S(a)+NT+S(b) for
  cross-type singles of one base pair; Lemma A; F1 with each P_q; OO = L on {P_k,P_l,F,F'}; L on {3 base, F, F'}; D1 at derived
  5-pairs (P_k,F). A rule fires only when it fails for EVERY admissible z (lower bounds from F1-forced z, pigeonhole and Lemma A).
  This is w13_ac.compat generalised from the 24 single types to all traces, plus the F1-forced/Lemma-A overlap lower bounds.
* Conflict graph (w14_conf.py): computed for the 762 orbit representatives of traces under the order-576 base group
  (w14_group.py, every element checked to map P_i∩C onto P_π(i)∩C with OSZ preserved) and transported. Result symmetric
  (independent sanity check of the transport): **37 569 536 conflict pairs, density 0.226** (file w14_conf.npz).
* Soundness control (w14_selftest.py): all 12 literally verified K4 realizations (M10, B, b1, Br1, Br2, Pr0–2, Tr0–1, Ur0, m1):
  `edges 117, pairs 532, violations 0` (every edge's state enumerated, every pair declared compatible).
### G14.2 First results (13:20–13:40 UTC)
* Dominance (w14_dom.py; t ⊋ t* with N(t*) ⊆ N(t) ∪ {t} ⇒ drop t): only 361 traces removed. Not useful.
* **Global elimination (w14_gac.py, PROVED rule):** if t meets B' and every alive avoider of B' conflicts with t, then ¬x_t (unit
  propagation on COV(B') + CONF, i.e. a RUP lemma). Two rounds: 3235 + 181 traces eliminated, **fixpoint with 14801 alive traces,
  no wipeout** (sizes: 6:564, 7:3179, 8:5837, 9:5218 — the same 6–9 range as the realizations' core parts). So Φ is not refuted
  by this propagation.
* Lazy SAT on Φ (w14_lazy.py: COV + gac units, CONF added on demand with all 576 images whenever a minimal sub-cover of the
  model contains a conflict): running; at 13:40 UTC ≈ 1.5 M conflict clauses added, minimal covers of 250–300 traces still
  carry 4–5 k conflicts each iteration. Undecided.
### G14.3 Case tree with global elimination (14:00 UTC; w14_sac.py, w14_tree.py) — RUNNING, partial results
* Independent re-check of CONF (w14_indep.py: does NOT import w14_compat/w14_group/check; enumerates every integer overlap
  vector z_0..z_3, z_U and tests the literal rule statements incl. exact L-unions over every ≥2-subset of base edges):
  300 random clauses of the lazy set: `disagreements 0`. Positive control w14_indep_pos.py: all 532 realization pairs feasible.
* Symmetry: C is G-invariant by construction (transport) and spot-checked (6 random g × 40 rows, exact). WLOG step: every solution
  of Φ contains a gac-alive avoider of B* = {w}∪γ (19 alive avoiders, |Stab(B*)| = 288 → 5 orbit representatives); mapping by
  g ∈ Stab(B*) puts the representative in the solution. So Φ is UNSAT iff Φ ∧ x_r is UNSAT for the 5 representatives r.
* One level (w14_sac.py): 1 of the 5 cases closes by elimination alone (r = {al0,al1,m0,m1,m2,c3,c4}: wipeout of {v,w,al0,al1}).
* Full DFS (w14_tree.py: branch on the uncovered needed B with fewest live avoiders, child i forces t_i and excludes t_1..t_{i−1};
  elimination at every node, ≈3.5 s/node): in case r = {v,al0,al1,m0,m1,c3,c4} the first ~80 nodes ALL close at depth 3–4
  (wipeouts of {w,a4_0,c3,c4}, {v,w,m0,m1}, {w,g0,g1,c4}, {al0,al1,m0,a4_0}, …). Undecided overall until all 4 open root cases finish.
* Lazy SAT (w14_lazy.py) paused at 7.5 M added CONF clauses (minimal covers ~80 traces with ~500 conflicts each; solves 2–3 min)
  in favour of the tree. Checkpoint w14_lazy_pairs.npy kept.
* Certificate plan (w14_cert.py, written, not yet run): per root case r, CNF_r = 1730 COV + the CONF clauses actually used + unit
  x_r; DRAT = the global gac lemmas [−t], then for each node every elimination as the RUP lemma (¬cube ∨ ¬x_t) with a logged
  witness B', then ¬cube after its children; end with [−x_r] and the empty clause. Check with work/e616/tools/drat-trim.
- 14:25 UTC: the first full DFS (w14_tree.py) closed root case r = {v,al0,al1,m0,m1,c3,c4} completely: **139 nodes, all leaves
  wipeouts, max depth 4–5** (log w14_tree.log / w14_tree.jsonl). Replaced by w14_tree2.py (same rule and branching; supports
  updated incrementally from the parent, ≈1.5 s/node; emits the DRAT lemmas on the fly; resumable per root child; driver
  run_tree2.sh runs the 5 cases then drat-trim on each).
- 14:27 UTC: **case r = {al0,al1,m0,m1,m2,c3,c4} (15116): CNF w14_cert2_15116.cnf (18217 vars, 668 659 clauses = 1730 COV + 666 928
  CONF + unit x_r), DRAT w14_cert2_15116.drat (5485 lemmas): drat-trim `s VERIFIED`** (2.7 s; 283 736 clauses / 2006 lemmas in core).
  This only certifies Φ ∧ x_r for ONE of the 5 root cases; it is the pipeline test, not the result.
- 14:33 UTC: **case r = {v,al0,al1,m0,m1,c3,c4} (14968): w14_cert2_14968.cnf (1 024 649 clauses: 1730 COV + 1 022 918 CONF + x_r) +
  .drat (109 660 lemmas, 138 tree nodes): drat-trim `s VERIFIED`** (8.5 s; core 494 763 clauses / 11 953 lemmas; core in
  w14_cert2_14968.core).
- 14:36 UTC: **root step (w14_certdead.py): B* = {w,g0,g1,g2}; the Stab(B*)-orbits (|Stab| = 288) of the 5 representatives are exactly
  the 19 gac-alive avoiders of B* (asserted); the 51 gac-dead avoiders are refuted by w14_certdead.cnf (COV + 593 077 CONF + the
  clause "some dead avoider of B* is in") + w14_certdead.drat (the 3416 gac unit lemmas + empty clause): `s VERIFIED`** (3.1 s).
- Cases 15954, 16054, 17917 running (w14_tree2.py; logs w14_tree2_<r>.log). 15954 is larger (root branch 6, first child 15).
- 14:45 UTC soundness controls so far:
  * Universe completeness (w14_univ.py): enumerating EVERY core trace over the rigorous o-box gives exactly the 18217 traces of
    w13_feas.json (S13.1's o ∈ {L, L+1} restriction lost nothing). `missing 0, extra 0`.
  * End-to-end elimination control (w14_realtest.py): for 4 literal realizations (Ur0, M10, Pr2, B) run the elimination rule on
    Φ_R = COV(only the needed B some edge of R avoids) + full CONF from all 18217 traces: R's traces satisfy CONF and are NEVER
    eliminated (`R survives` ×4; 2–3 rounds, 600–800 needed B, ≈1000–2200 other traces eliminated each), no wipeout.
  * Dependency of the 14968 certificate (w14_dep.py on its drat-trim core, 494 409 CONF clauses; all still conflicts under the full
    rules): clauses that stop being conflicts when one family is dropped: SAME 148, Lemma A 240 360, F1 60, OO 133 236,
    L3' 0, D1d 5492. So that case uses every family except L on {3 base, F, F'}.
  * Independent re-check of the 14968 core CONF clauses with w14_indep.py (exhaustive integer overlaps, literal rules, no shared
    code with w14_compat/w14_group): **all 494 409 core CONF clauses of the 14968 certificate re-checked, 0 disagreements** (14:47 UTC).
- ~14:46 UTC sandbox restart (lost the partial 2nd root child of case 15954 only); relaunched 14:48 with w14_resume.sh.
- Restart script for everything of this wave: sat/t21/w14/w14_resume.sh (tree+certs, drop-one controls queued after the
  tree, independent core re-checks of every certificate).
- 15:05 UTC: **case r = {v,al0,al1,m0,a4_0,c3,c4} (15954): 1558 tree nodes; w14_cert2_15954.cnf (3 896 902 clauses: 1730 COV +
  3 895 171 CONF + x_r) + .drat (2 517 837 lemmas incl. the 3416 gac units, 286 MB): drat-trim `s VERIFIED`** (171 s; core
  1 706 359 clauses / 196 384 lemmas, w14_cert2_15954.core). Status: 3 of 5 root cases + the dead-avoider root step verified;
  16054 (root branch 12) and 17917 running.
- 15:42 UTC: **independent state enumeration (w14_indep_states.py; frozensets, written from the lemma statements, imports nothing
  from w13_enum/w14_*; scans every core trace over the CAP/D1 box): exactly the same 18217 traces and 49 967 (trace, o) states as
  w14_states.json — 0 extra, 0 missing.** So the variable universe and the per-edge states do not hinge on one implementation.
- Sandbox restarts at ~15:35 UTC (lost one root child of 16054); resumed. Note: the W13 chains T/U (w11_exact.py, nice 2) were
  relaunched by somebody else's launcher after each restart and share CPU 0; they slow this wave ~2×. Not touched by me.
### G14.4 RESULT (≈15:50 UTC): the global pairwise model Φ is UNSAT — all certificates `s VERIFIED`
| piece | CNF (clauses) | DRAT lemmas | tree nodes | drat-trim | core clauses / lemmas |
|---|---|---|---|---|---|
| root: 51 gac-dead avoiders of B* | w14_certdead.cnf (595 k) | 3 417 | – | `s VERIFIED` 3.1 s | –/1 480 |
| r = {al0,al1,m0,m1,m2,c3,c4} (15116) | w14_cert2_15116.cnf (668 659) | 5 485 | 1 (root wipeout) | `s VERIFIED` 2.7 s | 283 736 / 2 006 |
| r = {v,al0,al1,m0,m1,c3,c4} (14968) | w14_cert2_14968.cnf (1 024 649) | 109 660 | 138 | `s VERIFIED` 8.5 s | 494 763 / 11 953 |
| r = {v,al0,al1,m0,a4_0,c3,c4} (15954) | w14_cert2_15954.cnf (3 896 902) | 2 517 837 | 1 558 | `s VERIFIED` 171 s | 1 706 359 / 196 384 |
| r = {v,al0,al1,m0,m1,a4_0,c3,c4} (16054) | w14_cert2_16054.cnf (4 181 029) | 1 952 921 | ≈1 550 | `s VERIFIED` 198 s | 1 953 320 / 183 695 |
| r = {v,al0,al1,m0,m1,a4_0,a4_1,c3,c4} (17917) | w14_cert2_17917.cnf (759 549) | 11 508 | 7 | `s VERIFIED` 3.1 s | 353 624 / 3 038 |
SHA-256 of every case CNF/DRAT: sat/t21/w14/w14_cert2.sha256 (certdead: recompute; it is regenerated deterministically by
w14_certdead.py). Every case CNF = the 1730 COV clauses (full avoider lists over all 18217 traces) + CONF binary clauses + unit x_r.
**Logical chain (each step PROVED or VERIFIED as marked):**
1. (PROVED, G14.1) An N-K4 counterexample gives a model of Φ (x_t = "some non-base edge has core trace t").
2. (VERIFIED) COV(B*) for B* = {w,g0,g1,g2}: the model contains an avoider t of B*. If t is gac-dead: w14_certdead refutes it.
3. (PROVED + checked) Otherwise t is one of the 19 gac-alive avoiders, = g(r) for some g ∈ Stab(B*) and one of the 5 representatives
   (asserted in w14_certdead.py). g is an automorphism of the labelled base (fixes P0, P1; swaps P2, P3 together with O2, O3 when it
   contains σ), so applying g to the whole counterexample gives a counterexample containing an edge with trace r. (Uses only the
   relabelling invariance of the hypothesis, not of any computed matrix.)
4. (VERIFIED) Φ ∧ x_r is UNSAT for each of the 5 representatives (table). Hence no N-K4 counterexample.
**Trust base / what is independently checked:**
* States: w13_enum.check (S13.1 lemma list) and an independent re-implementation agree exactly (18217 traces, 49 967 states).
* CONF clauses: generated by w14_compat (+ group transport); EVERY core CONF clause re-checked by w14_indep.py (exhaustive
  integer overlaps against literal rule statements, no shared code): 14968: 494 409/494 409 OK; 15954: running (1.3 M/1.7 M OK, 0
  disagreements so far); certdead, 15116, 16054, 17917: queued (run_indep_all.sh).
* COV clauses: built from the trace list by bit tests (B ∩ t = ∅); no lemma involved.
* Lemmas used (all from the refereed/proved list; nothing about N-noK4, NK or N24): Lemma A, F1/R.1, L (3 base + 2 new, 2 base + 2
  new, 3 base + 1 new), R.3, S(a), S(b), W7-I (NT; at base and derived 5-pairs), D1 (base and derived 5-pairs). Dependency of the
  14968 core: Lemma A 240 360 clauses, OO 133 236, D1d 5 492, SAME 148, F1 60, L3' 0.
* Soundness controls: 12 literal K4 realizations satisfy every CONF clause (532 pairs, both checkers); the elimination rule never
  removes a realization's trace on Φ_R (4 realizations).
* Drop-one control A (w14_conf_dropA.npz, w14_lazy_dropA.log): without the Lemma-A family the conflict density falls from 0.226 to
  0.029 and the lazy loop finds a pairwise-conflict-free cover of all 1730 needed 4-sets with 153 traces (w14_lazy_stall_dropA.json):
  **Φ without Lemma A is SAT** — the certificate genuinely needs it. Controls OO, D1d, SAME, F1, L3 running (run_ctrl.sh).
**Status: N-K4 (3,2,1,1) is refuted by a computer-assisted certificate, pending (a) the remaining independent core re-checks and
controls, (b) an outside referee of G14.1 and of the compat rule statements.** Together with W11 (N-noK4 closed, computer-assisted)
this would close Case N, hence t(21) = 4 — but that combination must be refereed before it is claimed anywhere else.
- 15:54 UTC: independent core re-checks (w14_indep.py) DONE with 0 disagreements for: 14968 (494 409), 15954 (1 705 470),
  15116 (283 537), certdead (253 375). 16054 and 17917 pending. Drop-one control **OO: Φ without OO is SAT** (pairwise-conflict-free
  cover of 86 traces, w14_lazy_stall_dropOO.json). Both control models re-checked directly (w14_ctrl_check.py, compat with the
  family dropped, no transport): `drop A: cover 153, covers all 1730: True, conflicts without A: 0, conflicts under full rules: 1619`;
  `drop OO: cover 86, covers all: True, conflicts without OO: 0, under full rules: 530`.
