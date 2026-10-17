# Erdős #616: local-to-global transversal bound. Loop notes (2026-10-14)

Status: **OPEN.** Nothing here settles an open value of t(r). What I did get: a certified *structural* result at the
first open case r = 21 (any τ = 5 example needs at least 15 vertices of degree ≥ 2), and negative evidence from
symmetric constructions. Problem 616 is **not** on the Oct 2026 OpenAI-release list.

## 1. Problem (as given at https://www.erdosproblems.com/616 and https://www.erdosproblems.com/latex/616)
Let r ≥ 3. t(r) is the least t such that every r-uniform hypergraph G has τ(G) ≤ t whenever every subhypergraph
on at most 3r−3 vertices has τ ≤ 1. Here τ is the transversal (cover) number.
Equivalently (property L_r): every subfamily of edges whose union has ≤ 3r−3 vertices has a common vertex.

## 2. What is known (sources)
* EHT91 = Erdős, Hajnal, Tuza, *Local constraints ensuring small representing sets*, JCTA 58 (1991) 78–84,
  doi:10.1016/0097-3165(91)90074-Q. I could **not** fetch the PDF: Elsevier blocks the bot.
* The site displays 3r/16 + 7/8 ≤ t ≤ r/5. The forum thread (https://www.erdosproblems.com/forum/thread/616, user
  BitterLemma, 17 Aug 2026) says the paper has floor(3r/16 + 7/8) ≤ t ≤ ceil(r/5), so the floor and ceiling were
  dropped. SciNet finding e18b081e (https://api.scinet.pub/f/e18b081e-6e0d-4664-a08e-3f2013f0897a, published
  2026-08-04, AI-authored, "awaiting independent review") says the same. It also extracts from EHT Theorem 3
  (t ≤ ceil(r/5)) and Theorem 6(II) (construction H(r, 3t+1, 2t+1): t(r) ≥ t+1 for r ≥ 5t + 1 + floor((t−1)/3)) that
  **t(r) = ceil(r/5) for all 3 ≤ r ≤ 20**, and that **t(21) ∈ {4, 5} is the first undetermined value**. The next ones
  are 26, 31, 36, 37, 41, 42, …. I have only these secondary sources for EHT. My own checks agree with them: the
  construction thresholds r0 = 6, 11, 16, 22 for τ = 2..5, and my SAT controls in §5.
* The erdosproblemaday report (https://erdosproblemaday.com/report/616) independently proves t(3..7) = 1,1,1,2,2 and
  the explicit private-block construction.
* The forum also has a Jan 2026 AI "proof" (jkabrg) that t(r) = 2. T. Tao refuted it.
* Earlier screening flagged "r = 3 SAT". **That is moot:** t(3) = 1 is trivial (every minimal empty-intersection
  family spans ≤ 3r−3 when r ≤ 5).
* I searched for later literature and found nothing improving EHT for this exact window.

## 3. Reformulation (my own; all steps proved)
Let X be the set of vertices of degree ≥ 2 (the "core", with n = |X|). Each edge is A_i = S_i ∪ P_i, where
S_i ⊆ X and P_i is a set of r − |S_i| private vertices. Then:
* span(subfamily) = |∪S_i| + Σ(r − |S_i|).
* For ≥ 2 edges, the intersection of the subfamily equals ∩S_i.
* τ(G) = min over C ⊆ X of ( |C| + #{i : S_i ∩ C = ∅} ). This value is a lower bound in general and is attained.

Write T_i = X \ S_i. Then:
* **P1:** τ ≥ 5 iff every 4-subset of X lies in some T_i. "Only if" holds always. "If" holds after taking 5 copies of
  each edge, which needs |S_i| ≤ r − 1.
* L_r iff every subfamily with ∪T_i = X has span ≥ 3r − 2. For m sets this is
  e = (m−1)n − Σ|T_i| + |∩T_i| ≤ (m−3)r + 2.
* **WLOG |T| ≥ 4.** Removing edges with |T| ≤ 3 keeps L_r and P1.
* **Twin collapse:** core vertices with identical membership can be merged.

Lemmas (r = 21, target τ ≥ 5):
* **L1.** Every two edges have |S ∩ S'| ≥ 5. Proof: G is 3-wise intersecting, since three pairwise-intersecting edges
  with empty common intersection span ≤ 3r − 3. So S ∩ S' meets every S''. If |S ∩ S'| ≤ 4, a 4-set containing it
  contradicts P1. Hence 4 ≤ |T| ≤ n − 9 for every T, and **no example has n ≤ 12**.
* **L2(n).** Suppose T, T' ∈ F are disjoint, |T| + |T'| ≤ 3n − 24 − 2·cmax, and n − |T| − |T'| ≤ 8. Then they cannot
  coexist. Proof: complete them with P1-sets T3 ⊇ C3 and T4 ⊇ C4 covering the rest. That gives o = Σc − n ≤ 2n − 24, so
  e ≥ 24 = r + 3, a violating quadruple (or a covering triple, which always violates). At n = 14 this says no two
  disjoint 4-sets.
* **Only m ≤ 4 matters for n ≤ 15.** For m = 5 at n ≤ 15 we would need d ≥ o, but o ≥ 4d and o ≥ 5. Larger m is
  worse. This was checked in the derivation, not by machine.

## 4. Results
**Theorem (new as far as I can find).** Let G be 21-uniform with property L_21 and τ(G) ≥ 5. Then G has ≥ 15 vertices
of degree ≥ 2. Compare EHT's H(22, 13, 9), which has core 13 at r = 22.
* n ≤ 12: by L1.
* n = 13 (hand proof): L1 forces every T to have size 4, so P1 forces F = all 4-sets. That family contains a point plus
  four disjoint triples covering [13]. This gives e = 39 − 16 + 1 = 24, span 60 ≤ 60, which is a violation.
  Machine check: certs/cegar2_r21_K5_n13_c4-4.cnf (715 vars, 12,110 clauses, no lemmas), DRAT VERIFIED by drat-trim.
* n = 14 (computer proof):
  * Certificate: certs/cegar4_r21_K5_n14_c4-5.cnf (3003 vars, 697,232 clauses).
  * Clause make-up: 1001 P1 clauses, 465,000 lazily found violating quadruples, 126,126 L1 instances and 105,105 L2
    instances. The L1 instances are exactly the disjoint 5-set pairs.
  * Solver: UNSAT by CaDiCaL 1.5.3 (pysat). The DRAT proof (certs/…cnf.drat.gz) is **VERIFIED by drat-trim**
    (27 s; certs/drat_n14_L12.txt).
  * Semantics checked independently: verify_cnf.py rebuilds literal edges with private vertices, confirms that every
    blocking clause is a genuine violating subfamily and that the P1 clauses are exact (SEMANTICS OK).
    verify_lemmas.py confirms every lemma clause is an L1 or L2 instance (0 bad).
  * Trusted parts: the written proofs of L1 and L2, the reformulation, and the "m ≤ 4" bound.
* n = 15 was attempted (pool 9373, with L1 + L2) and **not finished**. The CEGAR loop reached about 19M clauses and
  was stopped for memory. It needs better lemmas or symmetry.

**Symmetric-construction search (negative).**
* Families closed under Sym(A_1) × … × Sym(A_p), with X = ⊔A_j, consist of all T of chosen "types" (|T ∩ A_j|).
  For these, L_r reduces exactly to per-part covering arithmetic: d_max,j = min(min_i a_ij, ⌊(Σ_i a_ij − α_j)/(m−1)⌋).
  The search is exact SAT over type subsets (typesearch.py).
* Controls are correct: SAT at r = 22/16/11/6, UNSAT at r = 21/15/10.
* At r = 21, τ ≥ 5:
  * p = 1: UNSAT for n = 13..22.
  * p = 2: UNSAT for every shape with n = 13..19 (62 shapes) and the n = 20 shapes finished so far.
  * p = 3: the first 22+ shapes (n = 13 and part of n = 14) are UNSAT.
  * Both sweeps were left running in the background: p = 2 up to n = 22 with a 240 s cap per shape, and p = 3 for
    n ≤ 16 with a 120 s cap. Check sat/sweep_p2_r21_K5_13-22.txt and sweep_p3_r21_K5_13-16.txt. Any "FOUND"
    line in sweep2.out / sweep3.out is a candidate τ = 5 construction and must be verified literally.
* So no "multi-part H" construction gives t(21) = 5 in that range.

## 5. Files (sat/)
| Purpose | Files |
| --- | --- |
| Core model | core.py |
| CEGAR solvers | cegar2.py (pure clauses), cegar3.py (fast covering enumerator from eager2.py), cegar4.py / cegar6.py (with L1/L2) |
| Solving and proof checking | solve_drat.py, tools/drat-trim (built with zig cc, aarch64) |
| Verification | verify_cnf.py, verify_lemmas.py |
| Symmetric search | typesearch.py, sweep.py, sweep_p*_*.txt |

Replay n = 14:
```
python3 solve_drat.py certs/cegar4_r21_K5_n14_c4-5.cnf
tools/drat-trim certs/cegar4_r21_K5_n14_c4-5.cnf <drat>
python3 verify_cnf.py <(header + certs/cegar4_r21_K5_n14_c4-5.clauses) certs/cegar4_r21_K5_n14_c4-5_pool.npy 14 21 5
python3 verify_lemmas.py certs/cegar4_r21_K5_n14_c4-5.lemmas certs/cegar4_r21_K5_n14_c4-5_pool.npy 14 5
```
Caveat: the sandbox was reset once at about 15:05, losing the first round of files. Everything listed here was
regenerated afterwards.

## 6. Next steps
* n = 15, 16: lemma clauses lose power (L2 gets weaker), and m = 5 enters at n = 16. Add symmetry breaking or orbit-SAT.
* Search orbit-closed families under cyclic or affine groups at n = 16–25 for a τ = 5 example. A hit would settle
  t(21) = 5 and be easy to verify.
* Upper bound: a Venn-type analysis of 4-edge minimal empty-intersection families at r = 21. All pairwise intersections
  are ≥ 5, e ≤ 23 and the triple regions ≥ 1. The goal is to show τ ≤ 4. No progress yet.
* The problem is finite in principle. By Bollobás, a τ-critical 21-uniform hypergraph with τ = 5 has ≤ C(25,4) = 12,650
  edges, so t(21) is decidable, but nowhere near computable this way.

## Scheduled run 2026-10-14 17:13 UTC (13:13 EDT)
Checked: no FOUND at r=21 in orbsweep_results.txt / sweepA.out / sweepB.out (only r=22, r=16 controls). New UNSAT orbit results
(n=15..19: cycmult, semim, semiw, pg23fix, pg23sym, aff); TIMEOUT at n=15 semi:5, n=18 cycmult:5. Wave 6 jobs (w6tri2.py triangle-case region model,
orbsweep chains) are using both CPU cores, so I started nothing new. t(21) still in {4,5}. Stall counter 1 (no new theorem).

## Scheduled run 2026-10-14 18:13 UTC (14:13 EDT)
Environment was reset again (all python jobs dead, pysat/numpy/numba missing). Reinstalled python-sat numpy scipy numba networkx sympy.
No r=21 FOUND in orbsweep_results.txt (23 lines) or sweep*.out. Restarted the unfinished orbit-SAT chains in background:
sweepA2.out (26/pg23pl, then 18/semiw:6 19/cycmult:7 20/cycmult:3 21/semiw:7) and sweepB2.out (18/cyc 19/cyc 20/cyc, S<=13).
w6tri2 triangle-case model not restarted (CPU saturated). t(21) still in {4,5}. Stall counter 2.

## Scheduled run 2026-10-14 19:13 UTC (15:13 EDT)
Environment reset again (uptime 0, deps missing). Reinstalled deps. No r=21 FOUND in orbsweep_results.txt (23 lines). Restarted chains:
sweepA3.out (26/pg23pl), sweepB3.out (18/semiw:6 19/cycmult:7 20/cycmult:3 21/semiw:7). 18/cyc,19/cyc,20/cyc (S<=13) not yet restarted (2 cores only).
No new theorem; t(21) in {4,5}. Stall counter 3.

### 17:14 EDT run
Env reset; reinstalled deps and restarted orbit-SAT chains (sweepA5: 18/19/20 cyc, 19/cycmult:7, 20/cycmult:3, 21/semiw:7; sweepB5: 18/semiw:6). No r=21 FOUND in orbsweep_results.txt. Stall 5; t(21) still in {4,5}.

## 2026-10-14 18:12 EDT run
- Env intact except jobs dead (no python procs); pip reinstall; restarted chains sweepA6 (18/19/20 cyc, 19/cycmult:7, 20/cycmult:3, 21/semiw:7, SMAX=13) and sweepB6 (18/semiw:6, 17/semiw:4, 19/semiw:3). No FOUND in any log/result file. No new theorem. Stall 6 (pivot rule reached; primary target retained per task instruction).

### 19:13 EDT run: env reset, restarted orbit-SAT chains A7/B7; no FOUND; no new proof. Stall 7.

## 20:13 run: restarted orbit sweeps A8/B8; no FOUND; stall 8.

### 21:14 EDT run
Env reset killed sweepA8/B8 without results; restarted as sweepA9/B9. orbsweep_results.txt: 23 rows, all UNSAT/TIMEOUT, no r=21 FOUND. Stall 9.

## 2026-10-14 22:13 EDT run (stall 10)
- Env reset again (pysat gone); reinstalled. orbsweep_results.txt: A9 finished 21/cycmult:2 UNSAT; B9 specs 17/semiw:4 and 19/semiw:3 were INVALID (semiw:k needs k | n, AssertionError), so they never tested anything. 18/semiw:6 timed out. No FOUND at r=21.
- Restarted chain sweepA10 (300 s/group, SMAX=13): 20/cyc 20/semiw:4 20/semiw:5 21/semiw:3 22/cyc 24/cycmult:5 (all valid k|n).
- Small hand fact (triangle case, from D1 on (Q,Pi) and edge J of Tri-1; t_i=|J∩Pi∩Q_i|^~ = |T_i∩Q_i|, q*=|J∩Q_*|): if T_i not subset of Q_i then sum_{j!=i} t_j + q* <= 3, while |J∩Q|>=5 forces sum t + q* >= 2. Consistent, no contradiction; triangle still open.

### 2026-10-14 23:14 EDT
Env reset killed sweepA10 mid-run; restarted as sat/sweepA11.out (20/cyc 20/semiw:4 20/semiw:5 21/semiw:3 22/cyc 24/cycmult:5). No FOUND. No new proof. Stall 11.

### 2026-10-15 00:14 EDT
Env reset; restarted sweepA12 (20/cyc 20/semiw:4 20/semiw:5 21/semiw:3 22/cyc 24/cycmult:5). No FOUND for r=21 in any prior log. Stall 12.

### 2026-10-15 01:14 EDT
Sweep A12 died on reset without results; restarted as A13 (20/cyc 20/semiw:4 20/semiw:5 21/semiw:3 22/cyc 24/cycmult:5, SMAX=13). No r=21 FOUND. Stall 13.

### 2026-10-15 02:14 EDT
Env reset; reinstalled; restarted sweepA14. No r=21 FOUND in orbsweep_results.txt. Stall 14.

### 2026-10-15 03:12 EDT
Launched sweepA15 (cyc at n=18,19,21,22,23,24,25; previously untried). Results go to sat/orbsweep_results.txt. No FOUND at r=21.

### 2026-10-15 04:14 EDT
Env reset again; A15 lost. Launched sweepA16 (cycmult groups 19:7, 23:2, 24:5, 25:2, 21:4). No r=21 FOUND. Stall 16.

## 2026-10-15 07:14 EDT run
- cegar6 n=15 (core>=16) log ends at 19.4M clauses at 160 s with no verdict (killed by memory/reset); plain CEGAR at n=15 does not scale; needs orbit-of-S_15 symmetry breaking or a lex-leader encoding. No FOUND anywhere. Stall 19.

## 2026-10-15 15:14 EDT run
- Wave-11 chat jobs running (N-noK4 (3,3) CEGAR it9; N-K4 Benders it17, 2 CPUs). No FOUND, no new verified result. Not competing for CPU.
