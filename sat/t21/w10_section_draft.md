## Wave 10 outside-H (2026-10-15, ~12:45–EDT_END EDT)
**Result: Case N is still OPEN.** No UNSAT claim on the problem itself is made in this wave, so there is no DRAT certificate and no
control. What is new: (i) the "non-uniform Lemma H" asked for is exactly OO (N.1) applied at DERIVED 5-pairs. I give its explicit
forms (HN). For cross-type singles it is 0, which is R.3. For same-type singles it is 0 only under a C-agreement hypothesis. For
Lemma-T witnesses against singles it is exactly 4 − c, so it is NOT 0. (ii) Pairwise degree counting is provably too weak (H10.3).
(iii) The real missing ingredient is a 3-way lemma, **SQ (F1 squeeze)**. It is proved below. It alone kills the W9 stall core
(5-edge hand proof, H10.4). (iv) A sound exact LP oracle for outside points (w10_ulp.py) and a CEGAR run with SQ added (H10.5).
Notation as in §1 and N.0(iii). s_XY(Z) := 9 − |Z∩(X∪Y)| for a 5-pair (X,Y) (≥ 0 by D1 when X∩Y ⊄ Z).
