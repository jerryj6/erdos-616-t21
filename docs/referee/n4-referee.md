> **Internal working note.** This file is a raw report written while the proof was being developed and checked. It is kept for provenance. Run names and timings refer to the original working environment. The curated statements are in `paper/` and `README.md`.

> **Paths.** File paths in this report have been rewritten to their location in this repository wherever the file is
> included (`lean/`, `sat/`, `docs/`, `data/`). Paths still beginning with `work/`, `candidates/` or `/tmp/` name exploratory
> scripts, build directories or logs from the original working environment that are not part of the proof and were not
> published; nothing the final theorem or the certificate checks depends on is among them.

# Referee: exhaustiveness of the Case-N split (Erdős #616, r = 21)
Independent referee, 2026-10-16, 12:55–13:25 EDT. **Scope:** the case tree that runs from "a 21-uniform family with L and τ ≥ 5"
down to the leaves {W6-U, W7-I, N-K4 (3,2,1,1), N-noK4 (2,4)/(4,2), (3,3), (3,4)/(4,3)}, plus a check that each leaf matches the
base configuration hard-coded in the w10x / w11 / w14 encoders.
**Not in scope:** whether the encoders, the lemma instances inside them, or the certificates are correct. Those have their own
referee files: w10/w11/w14-referee. Everything below was re-derived by hand. My own scripts are in sat/nref/.

## Verdict: the split is EXHAUSTIVE and every reduction step is SOUND. No gap found.
I found two wording defects, neither used anywhere (C1, C2 at the end).

## The tree, as it should be cited (the dependency order matters)
0. Lemma A gives a 5-pair. R.2 gives singles of all 5 types, and R.3 gives every single |A|=|C|=4 and |O|=12.
   → refereed SOUND (t21-referee).
1. **If every 5-pair is uniform**, W6-U closes the case. *Otherwise* fix a non-uniform 5-pair (E1,E2).
2. **W7-I is unconditional.** No 5-pair anywhere has cross-type singles with a = 1 or c = 1. Its hypothesis is only "such a pair
   exists", and it does not presuppose Case I or Case N. So triangles are excluded globally.
3. **NK dichotomy (N8.0; this supersedes the wording of N.4).** Either some 5-pair (X,Y) has cross-type singles Z, Z' with
   |Z∩Z'| = 5, or NK holds at every 5-pair.
   - In the first case:
     - Z∩Z'∩N = ∅, because the types differ and each single meets N in one point.
     - Z∩Z' lies inside X∪Y, by S(a)/R.3.
     - So |Z∩Z'| = a + c with a, c ≥ 1 and a, c ≤ 4. Hence (a,c) is one of (1,4), (4,1), (2,3), (3,2).
     - The first two are excluded by step 2.
     - The last two make {X,Y,Z,Z'} four distinct edges, pairwise meeting in exactly 5 (R.3), with X∩Y∩Z∩Z' = ∅ and
       triples {y}, {y'}, a, c. That is a **(3,2,1,1)-K4 → leaf N-K4 (G14)**.
   - Exhaustive by definition: the second case is literally the negation of the first.
4. **Under NK**, cross-type classes need a, c ≥ 2 (step 2), a, c ≤ 4 and a + c ≥ 6. That leaves exactly
   (2,4), (4,2), (3,3), (3,4), (4,3) and (4,4). I enumerated this by hand and by script.
   - The pair (E1,E2) is non-uniform and has ≥ 3 types (R.2). If every cross-type pair were (4,4), any two same-type singles would
     agree through a third type, so (E1,E2) would be uniform. Hence some cross-type pair (G,H) is of class ≠ (4,4). ✔
   - (4,2) and (4,3) are (2,4) and (3,4) after renaming E1↔E2. This is a pure relabelling, so no symmetry of an encoder is needed.
     Checked: the Venn isomorphism is the edge permutation (1,0,2,3).
   - **Leaves:** (2,4) → w10x. (3,3) and (3,4) → w11. Both use the N24 tag, i.e. the w10x theorem.
5. **No circularity.**
   - G14 uses no Case-N hypothesis. It uses only A, F1/R.1, L, R.3, S(a), S(b), W7-I and D1, with nothing about NK or N24
     (G14.4, trust base).
   - The NK used by w10x and w11 is therefore a **consequence** of G14 + W7-I. It is not an extra case hypothesis.
   - w10x(2,4) uses NK only. w11 uses NK + N24. No leaf uses a later leaf.
   - So the chain is G14 ⇒ NK; NK ⇒ (2,4) closed; NK + (2,4) ⇒ (3,3) and (3,4) closed.

## Per-step verdicts
| Step | Verdict | Note |
|---|---|---|
| §6.2 split U / I / N; Case N = "no triangle, a non-uniform pair, {a,c}∩{2,3} ≠ ∅" | SOUND | With a, c ≥ 2 and a + c ≥ 5 the non-(4,4) classes are exactly the 7 listed in §6.6, and each meets {2,3} |
| N.0 general K4 count (union = 61 for every (a,c); triples [1,1,a,c]) | SOUND | Recomputed (nref/bases.py: pairs [5,5,5,5,5,a+c], union 61 for all 7 classes) |
| N.0(i) "triple vector is (4,1,1,1), (3,2,1,1) or (2,2,2,1)" | **Incomplete, but harmless** (C1) | Not used by the split |
| N.0(iii) region sizes of (3,2,1,1) | SOUND | Pair-private parts 3,2,2,1,1,0; private parts 10/11/12/12; core 16; union 61 (nref/k4types.py) |
| Why (3,2,1,1) is the only K4 leaf | SOUND | An NK violation produces triple multiset {1,1,a,5−a}, i.e. (4,1,1,1) (= triangle, killed by W7-I) or (3,2,1,1). Other K4 types are never produced and never assumed absent; see below |
| (3,2,1,1) is a single labelled configuration | SOUND | The 12 labelled size assignments form one S4-orbit, whose stabiliser is P2↔P3. Venn sizes are forced (pair-private part = 5 − both triples, private part = 21 − the rest) |
| N.4 witness step (k ≥ 2, c' ≥ 2, \|W∩E2\| = k + c', = 5 ⇒ (3,2,1,1)-K4) | SOUND | W is a type-p single of (E1,G). E2 is the type-v single, with A-part M∖v and C-part C_G. Then a = k, c = c', and NT gives ≥ 2. Both k = 2 and k = 3 give a K4 isomorphic to the w13 base (nref/bases.py) |
| N.4's split vs N8.0's split | SOUND | N.4's N-noK4 is NK at every 5-pair, exactly as N8.0 says. N.4's last sentence ("each class either contains a K4 via a witness or lies in N-noK4") is loose; the correct statement is the global dichotomy of step 3 |
| N8.0 (N-noK4 ⟺ NK + some non-uniform pair; classes under NK) | SOUND | |
| NK4.0 ((2,2,2,1) not needed) | SOUND | It needs no case analysis: the split is defined by NK, not by "no K4 of any type" |
| Do the noK4 encoders assume "no K4 of any type"? | **No, so SOUND** | The NK/W7 tag (w10x_exact.check) only forbids \|Z∩Z'\| < 6 for cross-type singles of one 5-pair. (2,2,2,1), (3,2,2,1), (3,2,2,2) and (2,2,2,2) K4s are not excluded. Since none of them contains two cross-type singles of one pair meeting in 5, they are not excluded by anything true either |
| N24 tag (used by w11) | SOUND as a case-tree step | It is symmetric: sorted(a,c) = [2,4] covers (2,4) and (4,2). It is applied at any 5-pair of an NK configuration, which is exactly the hypothesis under which w10x proved it |

## Base configurations vs. leaves (nref/bases.py, nref/slots.py, nref/group.py: all "ALL OK")
* **noK4 leaves.** w10x/w11 use `base_nok4(a,c)` (w9lazy.py):
  - E1 = M + al + ag + ah + a0 and E2 = M + cl + cg + ch + c0, with M = {v,w,m0,m1,m2}.
  - G = v + al + ag + cl + cg + og and H = w + al + ah + cl + ch + oh.
  - |al| = a, |ag| = |ah| = 4 − a; same pattern for c. og and oh are disjoint 12-sets.
  - For (2,4), (3,3) and (3,4), its Venn vector is **identical, with no relabelling,** to my independently built "5-pair + type-v
    single + type-w single, R.3 sizes, O_G∩O_H = ∅, class (a,c)". G∩M = {v}, H∩M = {w}, and the computed class equals (a,c).
  - That configuration is forced by the leaf hypothesis through R.3 + S(a), so the base is unique and is exactly the leaf.
  - Base 5-pairs are E1E2, E1G, E1H, E2G, E2H. G∩H has size a + c ≥ 6, so it is not a 5-pair.
* **First-generation slots.** My own recomputation (one single per base 5-pair and type not realised by a base edge) gives 19:
  3 + 4 + 4 + 4 + 4.
  - For (2,4), the first 19 avoid-sets in w9_cn24.json equal that set exactly.
  - w11's `sel` drops indices 7, 8, 9 = the (E1,H) singles of types al0..al2. That is a relaxation.
  - The generic and extra slots avoid 4-sets of named points, so each exists by τ ≥ 5.
* **N-K4 leaf.** The base used by w13/w14 (MEM/OSZ in w13_enum.py) is:
  - regions v = {0,1,2}, w = {0,1,3}, α = al0,al1 ⊂ {0,2,3}, γ = g0..g2 ⊂ {1,2,3}, m3 ⊂ {0,1}, a3 ⊂ {0,2}, a4 ⊂ {0,3},
    c3 ⊂ {1,2}, c4 ⊂ {1,3};
  - O0..O3 of sizes 10, 11, 12, 12.
  - It has the same Venn vector as w8k4/w9lazy `base_k4('3211')`, and as the (2,3) K4 (identity) and the (3,2) K4 (E1↔E2) built
    from an NK violation, and as both N.4 witness K4s.
  - The base automorphism group has order 576 = 2 (P2↔P3 together with v↔w, O2↔O3) × 288. Stab(B* = {w}∪γ) = 288, and every base
    edge meets B*. This agrees with G14.3/G14.4's WLOG step and with the COV precondition.

## Corrections suggested (cosmetic; no effect on the tree)
* **C1.** N.0(i) claims the triple vector of a K4 is (4,1,1,1), (3,2,1,1) or (2,2,2,1). That is the Σ = 7 list only.
  - F1 + L + region sizes also allow (3,2,2,1), (3,2,2,2) and (2,2,2,2) (nref/k4types.py; NK4.0 already notes "Σ ≥ 8 allowed").
  - Fix: replace "so the triple vector is …" with "if Σ = 7 the vector is …". The split never uses this list.
* **C2.** N.4's closing sentence should be replaced by the global dichotomy of step 3 (= N8.0). Wherever "N-noK4" is cited, it
  should say "NK at every 5-pair, a consequence of G14 + W7-I". Citing it as a case hypothesis is also fine, since step 3 is a
  tautological split.

## Caveat (outside this referee's scope)
Exhaustiveness is established. The conclusion t(21) = 4 still rests on four further things:
* the computer-assisted leaves G14 (N-K4), w10x (2,4) and w11 (3,3), (3,4) being correct encodings of proved lemmas;
* the KB pool bound;
* the G14 relaxation (COV/CONF);
* the G14 compatibility rules.
These are the subjects of the separate w10/w11/w14 referee files.

## Milestone log
- 12:55 EDT: read the sources; skeleton written.
- 13:15 EDT: nref/k4types.py (K4 types, (3,2,1,1) orbit and regions), nref/bases.py (bases vs. leaves, all OK), nref/slots.py
  (gen-1 slots), nref/group.py (576 / 288).
- 13:25 EDT: report complete.
