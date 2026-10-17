# Erdős Problem #616: t(21) = 4

This repository contains a computer-assisted proof that **t(21) = 4** for
[Erdős Problem #616](https://www.erdosproblems.com/616), together with

* a paper describing the argument (`paper/`),
* a Lean 4 formalization of the whole argument, end to end, against the statement of the problem in
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (`lean/`),
* the generators, checkers and independent re-encodings of the SAT instances used for the four computational
  leaves (`sat/`), with the certificates (CNF / DRAT / LRAT) distributed as a release asset,
* internal proof notes and referee reports (`docs/`).

The result concerns r = 21 only. It is computer-assisted and has not been externally peer-reviewed; see
[Status and caveats](#status-and-caveats).

## The problem

For r ≥ 3, let t(r) be the largest transversal number τ(𝓕) of a finite r-uniform hypergraph 𝓕 in which every
subhypergraph spanned by at most 3r − 3 vertices has τ ≤ 1. Erdős, Hajnal and Tuza (1991) proved

  ⌊3r/16 + 7/8⌋ ≤ t(r) ≤ ⌈r/5⌉,

and their construction H(r, 3t+1, 2t+1), counted exactly, determines t(r) = ⌈r/5⌉ for 3 ≤ r ≤ 20 (paper §1). At r = 21 the bounds give t(21) ∈ {4, 5}.

## Result

**Theorem.** t(21) = 4. Every finite 21-uniform hypergraph in which every subhypergraph spanned by at most 60
vertices has transversal number at most 1 has transversal number at most 4, and this is attained.

In Lean (`lean/Erdos616/Final.lean`):

```lean
theorem erdos_616_t21_eq_4 :
    Hypergraph.localTransversalBound 21 (3 * 21 - 3) 1 = 4
```

`Hypergraph.localTransversalBound r v a` is the infimum of the valid bounds b, as defined in formal-conjectures
(`FormalConjectures/ErdosProblems/616.lean` and its hypergraph library). The value `= 4` states both that 4 is a valid
bound (the upper bound) and that 3 is not (the lower bound).

## Proof overview

1. **Lower bound.** The Erdős–Hajnal–Tuza construction H(21,10,7): a 10-point kernel K, one edge for each 7-subset S
   of K, padded with 14 private vertices. It has 120 edges, τ = 4, and every subhypergraph spanned by at most 60
   vertices has τ ≤ 1. (Paper §2; Lean `four_le` in `Erdos616/Basic.lean`.)
2. **Reduction.** A counterexample (τ ≥ 5 with the local property) has two edges meeting in exactly 5 vertices
   (a *5-pair*), and a sequence of local lemmas (F1, A, R, S, K, T, D1, CP′) forces a rigid configuration around
   every 5-pair. (Paper §3; `Erdos616/Basic.lean`.)
3. **W6-U (hand proof).** Not every 5-pair is *uniform*. (Paper §4; `Erdos616/HandA.lean`, no computation.)
4. **W7-I (hand proof).** No 5-pair has a *triangle* (cross-type singles of class (1,4) or (4,1)).
   (Paper §5; `Erdos616/W7I.lean`, no computation.)
5. **Case split.** What remains splits exhaustively into four finite configurations: (K) a (3,2,1,1)-K4, and the
   no-K4 classes (N24), (N33), (N34). (Paper §6; `Erdos616/HandA.lean`.)
6. **Four computational leaves.** Each leaf is refuted by an unsatisfiable trace relaxation whose clauses are
   instances of the lemmas already proved. The relaxations are split into root/orbit cases under the symmetry group
   of the base configuration, and each case CNF has a DRAT certificate (checked by `drat-trim`) converted to LRAT and
   re-checked inside Lean. (Paper §7; `sat/`, `Erdos616/G14/`, `Erdos616/NoK4/`, `Erdos616/Cert/`.)

| Leaf | Relaxation | Case CNFs used by the Lean theorem |
|---|---|---|
| (K) (3,2,1,1)-K4 | G14 trace system (18,217 traces, 49,967 states) | 6: `w14_{14968,15116,15954,16054,17917}`, `w14_certdead` |
| (N24) class (2,4) | Φ₂₄ (without the N24 rule) | 7: `tree_24x_0..6` |
| (N33) class (3,3) | Φ₃₃ | 8: `tree_33_0..7` |
| (N34) class (3,4) | Φ₃₄ | 5: `tree_34_0..4` |

For every leaf, the Lean development proves in the kernel that a counterexample yields an assignment satisfying the
case CNF (encoding soundness: `edgeSound`, `pairSound`, the glue theorem `eval_of_check`), and a compiled checker
confirms by `native_decide` that every clause of the parsed CNF is a sound instance of the rules. The LRAT
certificate then gives `False`.

## Trust base

`#print axioms erdos_616_t21_eq_4` (full log in [`lean/VERIFICATION.md`](lean/VERIFICATION.md)) reports:

* `propext`, `Classical.choice`, `Quot.sound` (the standard axioms), and
* **58** auxiliary axioms `….​_native.native_decide.ax_1_1`. Each asserts that one specific closed Boolean
  computation evaluates to `true`, on the strength of the Lean compiler and runtime:
  * 3 acceptance checks of the Φ clause/orbit checker (`ok24x`, `ok33`, `ok34`);
  * 8 checks for leaf (K): universe completeness, root split, and the clause checker on the 6 pieces;
  * 47 LRAT checks with Lean core's `Std.Tactic.BVDecide.LRAT.check` (which has a kernel-checked soundness theorem):
    20 for the Φ case CNFs, 4 single-file G14 certificates, and 21 blocks + 2 final-block checks for the two G14
    certificates checked in chunked mode.

Everything semantic is kernel-checked without native code: the reduction, the lower bound, all hand lemmas, W6-U,
W7-I, the case split, and the encoding soundness of both relaxations. There is no `sorry` in the import closure.
The SAT solvers, `drat-trim`, the DRAT→LRAT conversion and the Python generators are not trusted: a wrong certificate
makes the checker return `false`.

**Negative control.** `lean/test/Neg.lean` states `= 5` with the same proof term; it must fail to elaborate.

## How to verify

### 1. Get the certificates

The CNF, DRAT and LRAT files (≈ 4.6 GB unpacked) are not in git. They are the release asset
`e616-sat-certs.tar.zst` of release **v1.0** (338,202,909 bytes), SHA-256

```
189bc3300f63f16ed4203989f381227b46587002e8717099076ae9c4f6510c95
```

```sh
scripts/fetch_certs.sh                      # downloads the v1.0 asset of this repository's GitHub origin
scripts/fetch_certs.sh path/to/e616-sat-certs.tar.zst   # or use a local copy
```

The script checks the tarball hash and every member (`sat/SHA256SUMS.members`), lays out `data/cnf`, `data/lrat`,
regenerates the LRAT block files of the two large certificates with `sat/lrat/split.py`, and checks the resulting
`data/` tree against `lean/DATA.sha256`. It needs `curl`, `zstd`, `python3` and about 9 GB of disk.

### 2. Build the Lean development

Requirements: [elan](https://github.com/leanprover/elan) (the toolchain `leanprover/lean4:v4.35.0` is pinned in
`lean/lean-toolchain`), Mathlib at commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (pinned in `lean/lakefile.lean`
and `lean/lake-manifest.json`). The C compiler needed for the native checkers is bundled with Lean.

```sh
cd lean
lake exe cache get          # prebuilt Mathlib
lake build                  # builds Erdos616 (default target) incl. Erdos616.Final
lake env lean test/Neg.lean # negative control: must FAIL
```

The checker modules (`Erdos616Checkers.*`, core Lean only) are marked `precompileModules`, so Lake compiles them to a
shared library and the `native_decide` evaluations in the certificate modules run compiled code.

Without Lake, `scripts/build_direct.py` performs the same build with plain `lean`/`leanc` calls (it compiles the four
checker modules to C, links `libErdos616Checkers.so`, and elaborates every module in import order with
`--load-dynlib`):

```sh
python3 scripts/build_direct.py Erdos616.Final --neg --mathlib-lib <dir with Mathlib .olean files> [...]
```

Peak memory is a few GB; the largest step elaborates the 21 LRAT blocks of the two chunked certificates
(their `.olean` files are ≈ 100 MB each).

### 3. Re-check the certificates outside Lean (optional)

```sh
scripts/check_drat.sh       # drat-trim on every case CNF/DRAT pair used by the theorem (needs drat-trim on PATH)
```

### 4. Regenerate the CNFs (optional)

`sat/README.md` describes each leaf, the generator scripts, the case counts, and how to regenerate the CNFs and
DRAT proofs and compare them with the released ones.

### What was verified for this release

See [`lean/VERIFICATION.md`](lean/VERIFICATION.md) for exactly which commands were run on the released tree and what
they printed, including which build path (Lake or `scripts/build_direct.py`) was exercised.

## Repository map

```
README.md            this file
LICENSE              Apache-2.0 (code); the paper is CC BY 4.0
CITATION.cff
paper/               erdos616-t21.tex / .pdf (19 pp.)
lean/                Lake project
  Erdos616Checkers/  core-Lean executable checkers (LRAT parser/checker, chunked LRAT, Φ trace checker, G14 checker)
  Erdos616/Basic.lean        formal-conjectures definitions (copied verbatim), reduction, lower bound, local lemmas
  Erdos616/HandA.lean        W6-U, the case split, assembly from the five leaves
  Erdos616/W7I.lean          W7-I (triangle case), hand proof
  Erdos616/G14/              leaf (K): bridge (edgeSound/pairSound), glue, root split, six case modules
  Erdos616/NoK4/             leaves (N24), (N33), (N34): bridge, symmetry, trace-checker runs
  Erdos616/Cert/             LRAT certificate modules (include_str data from ../data)
  Erdos616/Final.lean        erdos_616_t21_eq_4
  test/Neg.lean              negative control (= 5, must fail)
  VERIFICATION.md            axiom log and verification record
  DATA.sha256                hashes of the data/ layout consumed by the build
sat/                 generators, checkers, independent re-encodings, summary logs, SHA256SUMS (see sat/README.md)
scripts/             fetch_certs.sh, build_direct.py, check_drat.sh
docs/                proof-notes.md, referee/, lean-reports/ (internal working notes), path-map.md
data/                (git-ignored) certificates, created by scripts/fetch_certs.sh
```

## Status and caveats

* **Computer-assisted.** The four leaves have no human-readable proof. They rest on CNFs of up to 4.2 million clauses
  and LRAT proofs of up to about 1.1 GB.
* **`native_decide`.** The Lean proof is not kernel-only; it trusts the Lean compiler and runtime for the 58 Boolean
  evaluations listed above.
* **Not externally peer-reviewed.** All refereeing so far is internal: separate referee passes with independent
  re-implementations and re-encodings of each leaf (reports in `docs/referee/`), carried out with the same kind of
  computational (AI-agent) assistance as the proof itself. An external AI-assisted audit reproduced the no-K4 trace
  universes and found no `sorry`/custom axioms; this is not peer review. Scrutiny is welcome, especially of the
  trace-relaxation soundness (paper §7) and the case split (paper §6).
* **Statement provenance.** The formal-conjectures definitions are copied verbatim into `Erdos616/Basic.lean`, in the
  same namespaces, rather than imported, because formal-conjectures pins Lean v4.33.1 and its own Mathlib while this
  development uses Lean v4.35.0. Definitional identity with the upstream file has not been checked mechanically.
* **Scope.** Only r = 21 is settled. Nothing is claimed for other r, nor about the asymptotics of t(r)/r
  (3/16 vs 1/5).
* **Prior attempt.** An earlier AI-generated claim on #616 (January 2026) was retracted. This work is independent of
  it.
* **Literature.** Every statement attributed to Erdős–Hajnal–Tuza (1991) has been checked against the published text.
  One note: their p. 84 display reads (3r−3, 1) ↛ ⌊3r/16 + 7/8⌋, but their construction (and their own p. 80 statement)
  gives the lower bound t(r) ≥ ⌊3r/16 + 7/8⌋ used here; read literally, the display would contradict their Theorem 3 at
  r = 20. Neither half of the proof uses any result from that paper.
* **Paths.** The paper (§11, Table 4) and the internal reports in `docs/` use repository paths. Paths still starting with
  `work/` or `candidates/` in `docs/` name exploratory scripts and build directories that are not part of the proof and
  were not published; `docs/path-map.md` records the old-to-new correspondence for reading the raw logs.

## Citation

```bibtex
@misc{yong2026erdos616,
  author       = {Jerry Yong},
  title        = {Erd{\H o}s Problem \#616: $t(21) = 4$ --- paper, Lean formalization, SAT encodings},
  year         = {2026},
  howpublished = {\url{https://www.erdosproblems.com/616}},
  note         = {Computer-assisted; Lean 4 formalization; version 1.0}
}
```

See also `CITATION.cff`.

## License

Code (Lean sources, scripts) is released under the Apache License 2.0 (`LICENSE`), the same license as
formal-conjectures, from which the statement definitions are copied. The paper (`paper/`) and the documentation in
`docs/` are released under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
