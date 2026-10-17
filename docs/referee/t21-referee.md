> **Internal working note.** This file is a raw report written while the proof was being developed and checked. It is kept for provenance. File paths, run names and timings refer to the original working directory, not to this repository; see `docs/path-map.md` for the correspondence. The curated statements are in `paper/` and `README.md`.

# Referee report: Erdős #616, r = 21 (candidates/erdos-616-t21-upper.md §1, §6.0, §6.3, §7)
Referee run 2026-10-15 (~09:15–09:45 EDT). Hostile, line-by-line reading. Scope: §1 (F1, F2, Lemma A, R, Cor R1, S, K, T),
§6.0 D1, §6.2 case split, §6.3 Theorem W6-U, §7.1–7.4 Theorem W7-I (Tri-0, Tri-1, Tri-2, W7-2, W7-5/CP', Steps 0–4),
plus the core reformulation and L1 in candidates/erdos-616-loop.md §3. Case N (§6.5, N.*) and L2 / n=14 are **not** refereed here.

## Verdict summary
| Item | Verdict | Note |
| --- | --- | --- |
| Loop §3 reformulation (span, ∩, τ formula, P1, WLOG \|T\|≥4) | SOUND | P1 "if" needs the 5-copies trick, as stated |
| Loop L1 (\|S∩S'\|≥5, 4≤\|T\|≤n−9, n≤12 impossible) | SOUND | |
| F1, F2 | SOUND | |
| Lemma A (min intersection exactly 5) | SOUND | table recomputed |
| Lemma R.1, R.2, R.3; Cor R1 | SOUND | R.3 applies to every single (singles of all 5 types exist by R.2) |
| Lemma S (a), (b), (c) | SOUND | |
| Lemma K | SOUND | |
| Lemma T | SOUND | |
| D1 (§6.0) | SOUND | L ≠ F automatic since x ∈ F∖L |
| §6.2 case split U / I / N | SOUND (complete) | stale cross-refs only |
| Theorem W6-U (§6.3): G, Relatives, H, Closure, final family | SOUND | |
| Tri-0, Tri-1, Tri-2 | SOUND | |
| W7-2 | SOUND | |
| W7-5 (CP') | SOUND | |
| (A) and Step 0 (flagged "most delicate") | SOUND | see detailed check below |
| Steps 1, 2, 3, 4 | SOUND | |
| **Theorem W7-I (Case I impossible at r=21)** | **SOUND** (hand proof complete; machine checks independently confirmed) | |

No FALSE items and no substantive GAP found. Only cosmetic issues are listed at the end.

## 1. Loop-file reformulation and L1
* span = |∪S_i| + Σ(r−|S_i|); for ≥2 edges the intersection is ∩S_i (private vertices have degree 1). ✔
* τ = min_C (|C| + #{i : S_i∩C=∅}): any transversal D gives C = D∩X plus at least one more vertex per edge missed by C,
  and these are distinct (privates have degree 1). Attained by picking any vertex of each missed edge. ✔
* P1: "only if" is immediate. "If" holds with 5 copies of each edge (fresh privates): a C with |C|≤4 misses some S_i and pays 5.
  Copying preserves L: a copied subfamily with empty intersection projects onto distinct originals with empty intersection and
  no larger span. ✔
* span = m·r − e with e = (m−1)n − Σ|T_i| + |∩T_i|, so L ⟺ e ≤ (m−3)r+2. ✔ Recomputed.
* L1: G is intersecting and 3-wise intersecting (F1), so S∩S' is a transversal. If |S∩S'| ≤ 4, a 4-set containing it
  contradicts P1. Taking B a 4-subset of S_i with S_j∩B = ∅ gives |S_i| ≥ 9, hence |T| ≤ n−9. ✔

## 2. §1 lemmas (all re-derived)
* **F1.** Two disjoint edges have union 42. Three pairwise-intersecting edges with no common point have union = 63 − Σ|pairwise| ≤ 60. ✔
* **Lemma A.** A pairwise intersection is a transversal by F1, hence ≥ 5 by F2. For m ≥ 6:
  * F_j is disjoint from B_j ⊂ M, so F_j ∉ {E1,E2} and |F_j∩E_i| ≥ m.
  * |F_j∩M| ≤ m−4, so |F_j∖(E1∪E2)| ≤ 17−m.
  * Union ≤ 42−m+⌈m/4⌉(17−m). Recomputed for m = 5..17 (ref_numeric.py): 61, 58, 55, 52, 57, 53, 49, 45, 45, 40, 35, 30, 25.
    Every m ≥ 6 is ≤ 60. m ≥ 18 would force |F∩(E1∪E2)| ≥ 22. ✔
  * The F_j may coincide; that only lowers the union. ✔
* **R.1.** F∩M = ∅ ⇒ F meets E∖M and E'∖M (disjoint) in ≥ 5 each ⇒ union ≤ 37+11 = 48. ✔
* **R.2.** Apply F2 to M∖{x}, then R.1. ✔
* **R.3.** The family has empty intersection. |F∩(E∪E')| ≥ 9 ⇒ outside ≤ 12, so the union is ≤ 61 − overlap. Tightness forces
  |F∩E| = |F∩E'| = 5, both outsides exactly 12, and disjoint outsides. ✔
  * Because R.2 gives singles of all five types, **every** single has |A_G| = |C_G| = 4 and |O_G| = 12. The notation paragraph
    silently uses this, and it is correct.
* **Cor R1.** ✔
* **S(a).** {v}∪A_G is a transversal (R.1 at the 5-pair (E1,G)) and v ∉ H. O-disjointness is R.3. ✔
* **S(b).** G∩H ⊆ A∪C, since the O-parts are disjoint and lie outside E1∪E2. ✔
* **S(c).**
  * At (E1,G), M' = {v}∪A_G. E2 is a single of type v and H is a single of type p (H∩M' = A_G∩A_H since v ∉ H).
  * E2∖(E1∪G) = C∖C_G, and H∖(E1∪G) ⊇ C_H∖C_G. These are disjoint, so C_H ⊆ C_G, hence equal. ✔
* **Lemma K.**
  * {E1,E2,K,F} has intersection ⊆ Q∩{x} = ∅.
  * Union = 49 + |K∖(E1∪E2)| − |K∩O_F| ≥ 61 gives the bound.
  * K meets A_F and C_F by Cor R1 (x ∉ K). ✔
* **Lemma T.** At (E1,G), E2 is the type-v single. R.3 makes H∖(E1∪G) disjoint from C∖C_G, so H∩C ⊆ C_G. ✔

## 3. D1 (§6.0)
Take x ∈ M∖L and F a single of type x. Then L ≠ F (x ∈ F), L ≠ E, E' (they contain M), and {E,E',L,F} has intersection
⊆ {x}∩L = ∅. |E∪E'∪F| = 49, so |L∖(E∪E'∪F)| ≥ 12, giving |L∩(E∪E')| ≤ 9. **SOUND.**
General-r form: the cap is r − 3K + 3, which gives 7 at r=16 and 10 at r=22. It holds literally on both examples (ref_examples.py).

## 4. Case split (§6.2)
* Cross-type (a,c) has a, c ≥ 1 and a+c ≥ 5 (S), and a=1 ⇒ c=4, c=1 ⇒ a=4 (S(c)).
* So the possible non-(4,4) classes are exactly (1,4), (4,1) [Case I] and the seven Case N classes listed in §6.6.
* Same-type disagreement with all cross-type pairs at (4,4) is impossible via a third type (five types exist).
* The (4,1) version of Case I is the (1,4) version with E1 ↔ E2 swapped (Q = E2).
* **Complete.**

## 5. Theorem W6-U (§6.3): SOUND
* **G.**
  * Uniformity of (X,Y) gives F∩(X∪Y) = {y}∪α∪γ ⊂ S, so B_F = S∖(N∖{y}) and O(F) = F∖(X∪Y). F∩O(X) = ∅ trivially, since F∩X ⊂ S.
  * X∩F = {y}∪α has size 5, so (X,F) is a 5-pair.
  * Y∩N' = {y} because Y∩α = ∅. Y's A-part is Y∩(X∖N') = N∖{y} and its C-part is (Y∩F)∖{y} = γ.
  * Uniformity of (X,F) (Case U hypothesis) then gives α', γ', and the good-pair conditions check: X∩S = N'⊔α', F∩S = N'⊔γ'. ✔
* **Relatives.**
  * The move sends α = B_X∖N to N∖{t}, which is disjoint from α. All 5 Kneser neighbours of α are reached, because singles of
    every type t ∈ N exist (R.2).
  * K(9,4) is connected: 126/126, recomputed with an independent BFS.
  * Choosing N = C∪{t} and taking the type-t single U gives B_U = S∖C and O(U)∩O(X) = ∅. ✔
* **H.**
  * X∩U∩V = {t}: the S-part is B_X∖(C_U∪C_V), and the outside part is ⊆ O(X)∩O(U) = ∅.
  * X' ∌ t, so X' ∉ {X,U,V}, since t lies in all three.
  * Union ≤ 13 + 36 + 21 − |X'∩S| − |X'∩O(X)| ≥ 61. ✔
  * Corollary: if B_X ≠ B_{X'} then B_X ⊄ X' (both are 9-sets), so X'∩O(X) = ∅. ✔
* **Closure.**
  * On complements, B ↦ S∖C (C ⊂ B) is adjacency in K(13,4). It reaches all 715 sets (recomputed independently).
  * Each step yields an edge in a good pair, so induction applies. ✔
* **Final family.**
  * B_i = S∖({s0}∪R_i): ∩B_i = ∅ and |∪B_i| = 12. The edges are distinct, so their outsides are pairwise disjoint.
  * The four edges have empty intersection and union 60. Contradiction. ✔ (Recomputed.)

## 6. Theorem W7-I (§7): SOUND
* **Tri-0.**
  * All six pairwise intersections were recomputed from the definitions, along with x12 = v, x13 = w, x23 = p, P1∩P2∩P3 = C0,
    and Q_i of size 3. |Q∩(P1∪P2∪P3)| = 12 gives |Q_*| = 9, and the O_i have size 12.
  * The 4-family is at 61. The S3 symmetry is genuine: the structure is "apex Q plus three base edges".
* **Tri-1.** |P1∪P2∪P3| = 52, and inclusion–exclusion gives Σ|J∩P_i| − 3. ✔
* **Tri-2.**
  * R.2 at (P_i,P_j). Q is the type-x_ij single there, with outside Q_k∪Q_* (12 points), so Y avoids it.
  * x_ik ∈ Y: otherwise {Q,P_i,P_k,Y} has empty intersection and |Q∪P_i∪P_k| = 49. With |Y∩(P_i∪P_k)| ≥ 9, this gives
    Y∩Q ⊆ Q_i∪{x_jk}, which has < 5 points.
  * The bounds follow from D1 at (P_i,P_k) and at (Q,P_k). ✔
* **W7-2.**
  * At (Q,P_i), P_j and P_k are singles with A-parts {x_jk}∪Q_j and {x_jk}∪Q_k (meeting only in x_jk), C-parts C0 and outsides O_j, O_k.
  * S(a) puts W's outside part in U. S(b) gives a_j+c ≥ 5 and a_k+c ≥ 5 with a_j+a_k ≤ 5, so c ≥ 3.
  * P_i = ℓ_i ⊔ C0 ⊔ O_i, so |W∩O_i| = 4−c. ✔
* **W7-5 (CP').**
  * F ∌ p, so F ≠ Q, X1, X2.
  * Q∪X1∪X2 = Q ⊔ C ⊔ (X1∖(Q∪C)) ⊔ (X2∖(Q∪C)), since X1∩X2 ⊂ Q∪C.
  * Summing the Lemma A lower bounds gives the inequality. p ∉ F makes |F∩Q∖(X1∪X2)| = |F∩Q| − |F∩Q∩X1| − |F∩Q∩X2|. ✔
* **CP instance (Q,P_i,W^i_q).**
  * The pairs are 5, 5, 5 (R.3) and Q∩P_i∩W = {q}.
  * (P_i∩W)∖Q = K_W ∪ (W∩O_i), so for Y with Y∩C0 = {c} the right side is [c∈K_W] + [o_W∈Y] − 1. ✔
* **(A).**
  * o_W ∈ O_k lies outside P_a∪P_b.
  * The Y^{ab}_c, c ∈ C0, are (P_a,P_b)-singles of pairwise **different** types (types are the points c of N = C0∪{x_ab}).
  * By R.3 their outside parts are pairwise disjoint, so o_W lies in at most one of them. ✔
  * (A) is applied only to W of index k, the complement of {a,b}. That is the only case where o_W is outside P_a∪P_b, and Step 0
    uses it only there.
* **Step 0 (the flagged step).** W = W^k_q and Y = Y^{ab}_c, with q ∉ Y since Y∩Q_k = ∅.
  * Y∩Q = {x_ak, x_bk} ∪ S_c with x_ak, x_bk ∈ ℓ_k, so the CP left side is |S_c∖A|.
  * e = 4: W∩O_i = ∅, the o-term is 0 and the bound is 0.
  * e = 3, c = m_W: the bound is [o_W∈Y^{ab}_m] − 1 ≥ 0, which forces o_W ∈ Y^{ab}_m (and S_m ⊂ A). By (A), o_W ∉ Y^{ab}_c for
    c ≠ m, so the bound is again 0.
  * Hence S_c ⊂ A^k_q for all c, and 3 ≤ |U_k| ≤ 4. **SOUND.** The Y's are a fixed choice, one per (pair, c); all later steps
    refer to the same choice, so U_k is well defined.
* **Step 1.**
  * Y^{ab}_{c*} ∌ x_ab and contains x_ak, x_bk. With Y_a ⊂ ℓ_a, the left side is |({x_bk}∪Y_b)∖A^a_q| ≤ 0.
  * U_a ⊂ Q_b∪Q_k does not contain x_bk, which forces A^a_q = U_a∪{x_bk} with |U_a| = 3 and Y_b ⊂ U_a. ✔
  * The (a,k) variant also checked.
* **Step 2.** A^k_q = U_k ⊂ Q_a∪Q_b does not contain x_ab, and x_ab ∈ Y^{kb}. ✔
* **Step 3.**
  * (i) q ∈ Q_d∖U_k misses every Y^{dd'}_c (their Q_d∪Q_d' traces are ⊂ U_k), and Step 1 makes d tight.
  * (ii) Step 2 plus tightness of d give Q_k ⊂ U_d, so U_d = Q_k.
  * (iii) Y^{dd'}_{c*}∩Q_{d'} = ∅, so |Y∩Q_d| ≥ 3 while Y∩Q_d ⊂ U_k∩Q_d has ≤ 2 points. ✔
* **Step 4.**
  * (★) derivation ✔ (traces constant = U_k when k is tight).
  * (i) and (ii) re-traced with explicit orderings; both are contradictions. ✔
  * Exhaustive by independent brute force: 8000 = 20³ cases, 0 satisfy (★) for all six orderings.

## 7. Machine checks (re-run by the referee)
| Check | Result |
| --- | --- |
| drat-trim on t21/w7_core_A_c3.cnf + .drat | **s VERIFIED** (5559-clause core, 0.9 s) |
| CNF provenance | regenerating with `W7FLAGS=A,c3 W7CNF=… python3 w7_trace3.py` gives a byte-identical file (md5 9af7e297…) and UNSAT |
| CNF semantics (read w7_trace3.py) | Active constraints are W-facts incl. S(b), Y-facts (Tri-2), (O), CP' for (P_i,W^i_q) and (P_a,P_b) applied to the Y's, and (A) for complementary-index W only. All are proved facts, so the CNF is a sound relaxation and its UNSAT implies W7-I. |
| **Independent referee encoding** work/e616/referee/ref_w7_min.py (own pure-clause encoding, no CardEnc, **only** the facts the hand proof claims: no S(b), no (O), no CP' for (P_a,P_b)) | **UNSAT**; DRAT (ref_w7_min.cnf/.drat) **s VERIFIED** by drat-trim |
| Controls on the referee encoding | without (A): SAT; with only 3 values of c: SAT. Confirms §7.4's claim that (A) and all four C0 points are needed and S(b)/(O) are not. |
| Kneser K(9,4) connectivity | 126/126 (author script + independent BFS) |
| 715-subset closure | 715/715 (author script + independent K(13,4) BFS); final family ∩ = ∅, ∪ = 12, span 60 |
| Step 4 | 8000 cases, 0 satisfying (★) (author script + independent re-implementation) |
| Literal checks on H(16,10,7) and H(22,13,9), work/e616/referee/ref_examples.py, 60 min-pairs each | min pair = 4 / 5; R.1, R.2, R.3-analogue, S(a), S(b), uniformity, D1 cap (7 / 10) and Lemma K line 1 all hold; no S(c) instance arises (both uniform) |
| PG(2,4) skeleton (§7.2) literal | L holds (0 violations among Q + 3/4 lines); CP': 10080 checks, 0 violations. It is tight (bound attained) at the non-concurrent line triples, so CP' cannot be sharpened in general. |

## 8. Attempts at counterexamples (none found)
* Every lemma depends on τ ≥ 5 and r = 21, so no small literal r=21 instance exists to test against. I tested the general-r
  analogues on both EHT extremal examples and on the PG(2,4) model, which satisfies L at r=21 with τ=2. The model exercises
  CP', L and Lemma A without τ ≥ 5. No violations.
* I tried to break W6-U and W7-I where a referee would expect a slip: edge distinctness in every "empty intersection" family,
  well-definedness of U_k and c*(q), whether (A) is used outside its valid index, completeness of the case split, and the
  r=22 sanity (64 > 63) and r=16 vacuity claims. All of these hold.

## 9. Cosmetic issues (no effect on correctness)
* §6.2 cross-refs are stale: "Case I → open, see 6.1/6.5" and "Case N → open, see 6.4". Case I is now closed by §7.4, and Case N
  is in §6.5.
* §7.4's heading timestamp "~09:40 EDT" is later than the file's modification times (~08:24 EDT). This is probably a UTC/EDT slip.
* Step 3(i) says "d is tight … so Step 1 applies". The logic runs the other way: Step 1 applies and *yields* that d is tight.
  The argument itself is fine.
* The notation paragraph after Lemma R uses |A_G| = |C_G| = 4 for every single, which relies on R.2 (all types exist). Worth one
  explicit sentence.

## Bottom line
Lemma A, R, S, K, T, D1, Theorem W6-U (uniform case impossible) and Theorem W7-I (triangle case impossible) are all
**SOUND** at r = 21. The certificate for W7-I is valid, encodes a correct relaxation, and is independently reproduced by a
smaller referee encoding that uses only the ingredients of the hand proof. This review does not cover Case N, so t(21) ∈ {4,5}
remains open: t(21) = 4 ⟺ Case N (§6.6 classes (2,3),(3,2),(2,4),(4,2),(3,3),(3,4),(4,3), no triangle) is impossible.

Referee files: work/e616/referee/ref_w7_min.py (+ .cnf, .drat), ref_examples.py, ref_numeric.py.
