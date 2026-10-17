> **Internal working note.** This file is a raw report written while the proof was being developed and checked. It is kept for provenance. Run names and timings refer to the original working environment. The curated statements are in `paper/` and `README.md`.

# Referee report: Wave 10 exact-outside, N-noK4 class (2,4) closure (Erdős #616, r = 21)
Referee run 2026-10-15, ~14:40–14:55 EDT. This was a hostile reading.
- **Scope:** in docs/proof-notes.md, "Wave 10 exact-outside" (X.1–X.9, including X.2 Lemma KB), "Wave 8 N-noK4" N8.0, and N.4,
  which defines N-noK4.
- **Taken as SOUND without re-checking:** the lemmas refereed in docs/referee/t21-referee.md. These are §1 (A, R.1–R.3, S, T),
  D1, the §6.2 case split, W6-U and W7-I.
- **Independent work:** everything I built is in sat/w10ref/. My encoder does not import or copy any w9/w10x code.

## Verdict summary
| # | Item | Verdict |
|---|---|---|
| 1a | Lemma KB (pool bound K ≤ ⌊½ Σ(21−ν_s)⌋; 19 singles → K = 114) | **SOUND** |
| 1b | Lex-leader SB on pool columns and on named-point classes | **SOUND**, and **not needed** (my encoding has no SB and no POOL, and is still UNSAT) |
| 2 | Independent re-encoding of the 19-edge core + different solver + DRAT | **SOUND: UNSAT, drat-trim `s VERIFIED`** |
| 3 | Each instance kind (L/XL, R3, SA, D1, W7, NK, and the eager layer) follows from proved lemmas under the N-noK4 hypothesis | **SOUND** |
| 4 | Completeness of the case reduction: the (2,4) base and its 19 first-generation singles exist in every (2,4) N-noK4 configuration | **SOUND** |
| — | Overall claim: in N-noK4, no 5-pair has cross-type singles of class (2,4) or (4,2) | **SOUND** (computer-assisted) |

I found no FALSE item and no substantive GAP. The minor remarks are at the end.

## 1. Lemma KB and symmetry breaking
### 1a. Lemma KB: SOUND
**Slots.** For each base 5-pair (Bi,Bj) and each type y not realised by a base edge, τ ≥ 5 gives an edge avoiding N∖{y}.
- R.1 says N is a transversal, so the edge contains y. It is therefore a single of (Bi,Bj).
- R.3 gives |F∩Bi| = |F∩Bj| = 5, with exactly one common point y. So |F∩(Bi∪Bj)| = 9, ν = 9, and |F∖base| ≤ 12.
- With 19 slots, Σ|F_s∖base| ≤ 228. A point lying in ≥ 2 slots is counted at least twice, so |Sh| ≤ 114. ✔
  (For the 24-edge model: 19·12 + 5·16 = 308, giving 154. ✔)

**The rest of the bound.**
- Every other outside point of a slot lies in exactly one model edge. Treating such points as implicit privates is exact for every
  statement used, because all of them are built from intersections and unions of model edges, plus the size 21.
- **Coinciding slots.** Two slots can be the same real edge, e.g. a cl0-single of (E2,G) and of (E2,H). Then all their outside points
  lie in Sh, which is counted. Every encoded statement stays true when evaluated literally on a slot list with repeats:
  - Lemma A becomes 21 ≥ 5.
  - F1 holds.
  - L, R3, D1, SA, W7 and NK are conditional on hypotheses (5-pair, single, different types, M ⊄ L) that a repeated edge either
    satisfies harmlessly or falsifies.
  - Cross-type singles are automatically distinct.
- **No slot is a base edge.** Each base edge meets each slot's avoid set (checked). Even if one were, the encoding would remain exact.

### 1b. Symmetry breaking: SOUND, and not needed
**Pool columns.** Every clause family treats pool columns uniformly:
- E21, A, Lbase, D1 and SA-eager depend only on base membership.
- The lazy forms are symmetric functions of the columns. Totalizers are built over sorted lists, but they are logically symmetric.

**Named classes.** These are points with the same base signature that lie in no avoid set. The base edges are fixed by the
permutation, and AV and R1 refer only to avoid and type points. A type y of a pair always lies in the avoid sets of the other slots
of that pair, which every base pair has, so R1 points are excluded (the authors' check agrees).

**Product group.** The symmetry group is a product of symmetric groups on disjoint column classes, so sorting each class independently
reaches a lex-leader in every orbit.

**POOL.** "Used by 0 or ≥ 2 slots" is a WLOG restriction by the definition of Sh.

**Not needed.** My encoding (§2) has neither SB nor POOL. Omitting POOL is a pure relaxation, since a pool point in one slot is just a
private point. It is still UNSAT. The authors' C3 run (no SB) shows the same.

## 2. Independent re-encoding: UNSAT, DRAT VERIFIED
**Encoder: sat/w10ref/ref_enc.py.** I wrote it from the mathematical statements.
- **Base.** The (2,4) base is built from its definition: M; al = A_G∩A_H (2 points); ag, ah (2 each); a0 (10); cl = C_G = C_H (4);
  c0 (12); og, oh (12 each). The code asserts the defining relations: |G∩H| = 6 = al∪cl, the five base 5-pairs, and disjoint O-parts.
- **Slots.** The 19 slots are derived from the base, not read from a file. They are mapped to the w9_cn24.json indices 0..18 by label,
  and every json avoid set is asserted equal to N∖{y}.
- **Data read.** Only the instance list (which edges each of the 380 instances names) is read from w10x_n24s_core.json.
  SHA-256 e733323f…, which matches w10x_n24s_cert.sha256.
- **Auxiliaries.** Every auxiliary is a full equivalence: Tseitin AND and a Sinz sequential counter in both directions. The authors used
  totalizers, so the cardinality encoding is different.
- **Instances.** Every instance is encoded in exact per-point form, conditional on its hypotheses:
  - **R3:** 5-pair(X,Y) ∧ |Z∩N| = 1 ⇒ |Z∩X|, |Z∩Y| ≤ 5.
  - **D1:** 5-pair ∧ |L∩N| ≤ 4 ⇒ |L∩(X∪Y)| ≤ 9.
  - **SA:** 5-pair ∧ Z1, Z2 single ∧ Z1∩Z2∩N = ∅ ⇒ Z1∩Z2 ⊆ X∪Y, point by point.
  - **W7:** same hypothesis ⇒ |Z1∩Z2∩(X∖Y)| ≥ 2 and |Z1∩Z2∩(Y∖X)| ≥ 2.
  - **NK:** same hypothesis ⇒ |Z1∩Z2| ≥ 6.
  - **L / XL:** both are encoded identically and exactly: common point ∨ Σ_a (mult_a − 1)^+ ≤ 21m − 61, i.e. union ≥ 61.
- **Eager layer.** AV, R1, E21, Lemma A (slot vs base and slot vs slot), R3 and D1 at the base pairs, L on {base subfamily} ∪ {slot}, F1
  (B_k∩F∩F' ≠ ∅), and S(a) at the base pairs.
- **Pool.** K = 114 = the KB bound. No SB, no POOL.

**Result.** ref_n19.cnf (617244 vars, 2334395 clauses). The solver was **Glucose 4 (pysat)**, not CaDiCaL: **UNSAT in 19.6 s**.
- DRAT: ref_n19.cnf.glucose4.drat, 11.8 MB.
- drat-trim: **`s VERIFIED`**. The core has 43534 clauses and 9622 lemmas; 0 RAT lemmas; verification took 5.1 s.
- Log: solve_n19_glucose4.log. SHA-256 values are in ref_n19.sha256 (cnf 50b210a5…, drat 5e502025…, encoder 16df6f86…).
- The CNF regenerates byte-identically.

**Controls (glucose4, my encoding).** Each removes one ingredient and should be SAT. Every SAT model was decoded into a literal
hypergraph (base + slots + privates) and re-checked with plain set arithmetic by ref_check.py:

| removed | result | literal re-check of the model |
|---|---|---|
| NK | SAT 62 s | satisfies all 380 instances with NK off; violates 29 NK instances |
| L/XL | SAT 33 s | violates only 2 L instances |
| D1 | SAT 18 s | violates only 23 D1 instances |
| SA | SAT 141 s | violates only 21 SA instances |
| W7(+NK) | SAT 166 s | violates only 33 W7/NK instances |
| R3 | SAT 95 s | violates only 6 R3 instances |

So the contradiction uses every kind, NK is essential, and the encoding is not vacuous. Each check also found 0 violations of the
eager statements.

**Exactness and soundness control.** I fixed the slot bits to the literal NK-free configuration.
- **Soundness:** the CNF with exactly the 351 instances that the configuration literally satisfies is SAT. So the encoder excludes nothing
  that satisfies the instances.
- **Exactness:** each of four literally violated instances, added alone, makes the CNF UNSAT.

These results agree with the authors' C2 certificate (their encoder, CaDiCaL 1.5.3, drat-trim VERIFIED). Their SHA values match the
files on disk.

## 3. Instance kinds as consequences of proved lemmas: SOUND
Every instance is a conditional statement about arbitrary edges of G, so it holds for any choice of slots once the lemma holds at
every 5-pair.
- **R3 = R.3**, valid at every 5-pair. Singles of all five types exist by R.2, so every single has parts of size exactly 4/4/12
  (referee §2).
- **SA = R.3**, disjoint outside parts of cross-type singles at any 5-pair. "Different types" is encoded as Z1∩Z2∩N = ∅, which makes
  Z1 ≠ Z2 automatic.
- **D1 = §6.0**, at any 5-pair, for any edge L with N ⊄ L. L ∉ {X,Y} is automatic.
- **W7:** S(a) gives a, c ≥ 1, and W7-I (no 5-pair has cross-type singles with a = 1 or c = 1) gives a, c ≥ 2. Since Z1∩Z2∩N = ∅,
  Z1∩Z2∩(X∖Y) = A_{Z1}∩A_{Z2}. ✔
  - Remark: under NK, W7 is implied, since a + c ≥ 6 and a, c ≤ 4 give a, c ≥ 2. But W7-I is still needed to derive NK (see §4).
- **NK:** a cross-type pair with a + c = 5 is either a triangle (a or c = 1, excluded by W7-I) or a (3,2,1,1)-K4 (N.0: all six pairs
  are 5, triples (1,1,2,3)), which N-noK4 excludes (N.4 definition).
  - Hence a + c ≥ 6 at every 5-pair. By S(a) the outside parts are disjoint, so |Z1∩Z2| = a + c. ✔
- **L / XL:** this is property L. With 4 edges and no common point, union = 84 − Σ(mult − 1)^+ ≥ 61.
  - The authors' counter form (Σ pairs − Σ triples ≤ 23, with an escape when a triple counter is at its cap of 6) is a sound weakening.
  - Re-derived: when no triple is capped, the encoded sum is ≤ Σ pairs − Σ triples + 24 ≤ 47.
- **Eager layer:**
  - AV and R1 come from τ ≥ 5 and R.1.
  - Lemma A is exact because privates are never shared.
  - F1 is the 3-wise intersecting property, i.e. L plus Lemma A.
  - Lbase: L on S ∪ {F} is equivalent to F∩I ≠ ∅ or |F∩U| ≤ |U| − 40. ✔
  - The authors' D1 counter form is also a sound weakening: if N ⊄ L then t ≤ 4 and t ≥ i + j − 9; if N ⊆ L then t = 5.

## 4. Completeness of the case reduction: SOUND
**The base is forced.**
- A 5-pair (E1,E2) with cross-type singles G (type v) and H (type w) of class (2,4) is, by R.3 and S(a), exactly the 61-point 4-edge
  configuration encoded: |A_G| = |C_G| = 4, C_G = C_H, |A_G∩A_H| = 2, and O_G, O_H are disjoint 12-sets outside E1∪E2.
- It is unique up to relabelling.
- Class (4,2) is the same configuration with E1 ↔ E2 swapped.

**The singles exist.**
- The base has exactly five 5-pairs: E1E2, E1G, E1H, E2G, E2H. (|G∩H| = 6.)
- The types realised by base edges are v and w at E1E2, v at E1G (E2), w at E1H, v at E2G (E1) and w at E2H.
- So the 19 slots are 3 + 4 + 4 + 4 + 4. Each exists in every configuration by τ ≥ 5 and is a single by R.1.
- The core names 16 of them: (E1,E2) m0, m1, m2; (E1,G) all 4; (E1,H) ah1; (E2,G) all 4; (E2,H) all 4. It names no gen-2 or generic
  edge. Indices used: −4..−1, 0–11, 15–18.

**The hypotheses hold everywhere in N-noK4.**
- N-noK4 (N.4) is a global hypothesis: no (3,2,1,1)-K4 anywhere. Together with W7-I it gives NK at every 5-pair, including 5-pairs
  among slots. That is exactly how the lazy instances use it.

**The reduction to (3,3)/(3,4) follows.**
- W6-U kills "all 5-pairs uniform".
- A 5-pair all of whose cross-type pairs are (4,4) is uniform. Same-type parts agree through a third type, since five types exist.
- Under NK the classes are {(2,4),(4,2),(3,3),(3,4),(4,3),(4,4)}.
- With (2,4)/(4,2) gone, (3,3) or (3,4)/(4,3) remains, as stated in X.

## Minor remarks (no effect on the verdict)
1. X.1 lists TT and POOL/SB as ingredients, but none of them is needed for the (2,4) certificate. TT is absent from the core.
   SB is disproved as a requirement by C3 and by my run. POOL is disproved as a requirement by my run.
2. The X.8 caveat ("no independent re-implementation") is now discharged for the 19-edge core.
3. The claim stays computer-assisted. The certificate is only as good as the instance list, and I have now re-encoded that list
   independently. It says nothing about N-K4 (the nonk control is SAT in both encodings).
4. Wording: "Every one of those is a proved consequence of {L, τ ≥ 5, W7-I, N-noK4}". It also uses Lemma A, R.1–R.3 and D1, which are
   consequences of L and τ ≥ 5, so the statement is fine.

## Files (sat/w10ref/)
- **Code:** ref_enc.py (independent encoder), ref_solve.py (pysat Glucose 4 + DRAT + drat-trim), ref_check.py (literal set-arithmetic
  checker of the eager statements and the 380 instances).
- **Certificate:** ref_n19.cnf, ref_n19.cnf.glucose4.drat, ref_n19.sha256, solve_n19_glucose4.log.
- **Controls:** ctrl_nonk.log, ctrl_drop{L,D1,SA,W7,R3}.log, *.fix.json / *.sat_inst.json / *.viol_inst.json (control configurations).
