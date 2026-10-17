# SAT encodings, generators, and independent re-encodings

This directory holds the scripts that produced the case CNFs and DRAT certificates of the four computational leaves,
the independent referee re-implementations, and small summary logs. The certificates themselves (CNF, DRAT, LRAT;
≈ 4.6 GB) are the release asset `e616-sat-certs.tar.zst` (SHA-256 in `SHA256SUMS`, per-member hashes in
`SHA256SUMS.members`); `scripts/fetch_certs.sh` downloads and unpacks it under `data/raw/`.

**Nothing here is trusted by the Lean theorem.** The Lean development re-checks every clause of every case CNF with
its own checker and every certificate with Lean core's verified LRAT checker. These scripts are how the CNFs were
produced, and the referee scripts are the pre-Lean independent cross-checks.

The relative paths inside the scripts (`../../pylib`, `../../tools/drat-trim`, `../w14/...`) still resolve. To run them, create

* `sat/tools/drat-trim` — from <https://github.com/marijnheule/drat-trim> (any recent version);
* `sat/tools/kissat` — Kissat 4.0.4 (<https://github.com/arminbiere/kissat>), used only for some cross-checks;
* `sat/pylib/` — a Python 3.12 environment (or `PYTHONPATH`) with `numpy`, `numba`, `python-sat` (PySAT, for CaDiCaL
  1.5.3 / Glucose 4), and `ortools` (only for some exploratory scripts).

The scripts were written as research code. Their docstrings state what each one computes and which lemmas each rule
comes from; the paper (§7) and `docs/proof-notes.md` give the mathematics.

## Layout

```
sat/
  SHA256SUMS            hash of the release tarball
  SHA256SUMS.members    hashes of every file in the tarball (paths relative to data/raw/)
  w11ref/tr/            leaves (N24), (N33), (N34): the trace relaxations Φ_{a,c}
  t21/w14/              leaf (K): the G14 trace system for the (3,2,1,1)-K4
  t21/w14ref/           leaf (K): independent referee re-implementation (states, pair rules, coverage, orbit, DRAT)
  t21/w13_enum.py       one-new-edge enumeration against the K4 base (used by t21/w14)
  t21/w9lazy.py         earlier point-level model (imported by some w14 scripts for the base)
  t21/*.json            small inputs of the w10ref re-encoding
  nref/                 referee checks of the case split: K4 triple types, automorphism group, base configurations
  w10ref/               independent re-encoding of the earlier exact (2,4) encoding (Glucose 4); not used by Lean
  lrat/                 DRAT→LRAT post-processing: renum.py, split.py (chunked mode), gen*.py (Lean module
                        generators), cmp.py (parser round-trip comparison)
```

## The leaves and their case counts

### (N24), (N33), (N34): no-K4 cross-type classes — `w11ref/tr/`

For a class (a,c) the base is a 5-pair (E₁,E₂) with two cross-type singles G,H (`tr_core.base`). A non-base edge is
summarised by its *trace* on the core points and its private-part counts (a *state*); `tr_states.py` enumerates all
states admitted by the per-edge rules (the lemmas of paper §3). Two traces *conflict* if no state pair and no integer
overlap vector passes the pair rules (`tr_conf.py`). Φ_{a,c} (`tr_cnf.py`) has one variable per trace, a covering
clause COV(B) for every needed core 4-set B (τ ≥ 5), and a binary clause for every conflict.

Universes (traces / states): (2,4) without the N24 rule 9,558 / 30,827; (3,3) 10,674 / 35,493; (3,4) 6,553 / 21,952.

Root split (`tr_case.py plan`): B* = a needed 4-set with fewest avoiders; avoiders of B* are mapped by the base
symmetry group (`tr_sym.py`) onto orbit representatives r; each case is Φ ∧ x_r. `tr_tree.py` refutes each case by
propagation + branching and emits the DRAT proof directly; the case CNF is the sub-formula of Φ it uses.

| Class | Cases (CNF names) | Driver | drat-trim |
|---|---|---|---|
| (2,4) | 7: `tree_24x_0..6` | `run_treeT.sh 24x` (via `pipeline.sh`) | `tree_24x.log`: 7 × `s VERIFIED` |
| (3,3) | 8: `tree_33_0..7` | `run_tree.sh` | `tree.log`: 8 × `s VERIFIED` |
| (3,4) | 5: `tree_34_0..4` | `run_treeT.sh 34` | `tree_34.log`: 5 × `s VERIFIED` |

Checks and controls in the same directory: `tr_certcheck.py` (each case CNF consists exactly of COV clauses, conflict
clauses of the full matrix, and the case unit; `certcheck*.log`), `tr_indep.py` (a second, deliberately naive
implementation of the rules, `indep*.log`), `tr_real.py` (literal configurations pass all rules), `tr_drop.py` /
`tr_ctrlcheck.py` (dropping rule families makes Φ satisfiable; `dep33.log`, `conf_*.log`), and a direct Kissat run
on the unsplit Φ₃₃ (not used).

### (K): the (3,2,1,1)-K4 — `t21/w14/`, referee `t21/w14ref/`

Base: the K4 of the K4-regions lemma (paper §6), with 16 named core points and private parts of sizes 10, 11, 12, 12.
`w14_states.py` enumerates all (trace, o-vector) states of one new edge (using the single-edge constraints of
`t21/w13_enum.py`; completeness of the box: `w14_univ.py`) — 18,217 traces, 49,967 states.
`w14_compat.py` decides pairwise compatibility; `w14_conf.py` builds the trace conflict graph using the order-576
automorphism group (`w14_group.py`). `w14_gac.py` / `w14_sac.py` perform sound global elimination and choose the
root 4-set B* = {w, g0, g1, g2}.

Root split: the avoiders of B* are either eliminated outright (certificate `w14_certdead`, built by
`w14_certdead.py`) or mapped by an automorphism onto one of 5 representatives r ∈ {14968, 15116, 15954, 16054,
17917}. For each r, `w14_tree2.py` runs a DFS with global elimination and emits a DRAT proof (`run_tree2.sh`);
the case CNF is `w14_cert2_<r>.cnf`.

| Piece | CNF | DRAT check |
|---|---|---|
| dead avoiders | `w14_certdead.cnf` | `w14_certdead.core.trimlog`: `s VERIFIED` |
| r = 14968 | `w14_cert2_14968.cnf` | `w14_cert2_14968.trim.tail`: `s VERIFIED` |
| r = 15116 | `w14_cert2_15116.cnf` | `w14_cert2_15116.trim.tail`: `s VERIFIED` |
| r = 15954 | `w14_cert2_15954.cnf` (≈ 4.2 M clauses) | `w14_cert2_15954.trim.tail`: `s VERIFIED` |
| r = 16054 | `w14_cert2_16054.cnf` | `w14_cert2_16054.trim.tail`: `s VERIFIED` |
| r = 17917 | `w14_cert2_17917.cnf` | `w14_cert2_17917.trim.tail`: `s VERIFIED` |

Independent checks: `w14_indep*.py` (explicit-enumeration re-check of every conflict clause in each drat-trim core),
`w14_selftest.py` / `w14_realtest.py` (literal K4 realizations pass), drop-one controls (`w14_lazy_drop*.log`,
`w14_conf_drop*.log`). The referee directory `t21/w14ref/` re-implements states (`ref_states.py`), pair rules
(`pairref.c`, `pairref.py`), coverage (`ref_cov.py`), the orbit step (`ref_orbit.py`), the full conflict matrix
(`ref_fullconf.py`), and re-runs drat-trim (`drat_*.log`) and Kissat (`ks_*.log`), all sharing no code with
`t21/w14/`. Its logs report 0 disagreements.

### Not used by the Lean theorem

`w10ref/` (independent Glucose 4 re-encoding of the earlier exact pool encoding of class (2,4)) and the W7-I
finite-step CNF belong to earlier routes that the final theorem does not import (W7-I is proved by hand in Lean).
Their LRAT files are in the tarball for completeness (`e616lrat/lrat/ref_*.lrat`, `w10x_*.lrat`, `w7_core_A_c3.lrat`);
the corresponding CNFs are not.

## From DRAT to the Lean certificate modules — `lrat/`

For each case CNF: `drat-trim CNF DRAT -L out.lrat` → `renum.py` (lemma ids made contiguous, as Lean's checker indexes
clauses by position) → `lean/Erdos616/Cert/<name>.lean` (generated by `gen.py`). The two largest LRAT files
(w14_15954 ≈ 1.1 GB, w14_16054 ≈ 1.0 GB) are checked in *chunked mode*: `split.py NAME NCLAUSES 100` cuts the proof
into ~100 MB blocks of RUP lemmas (`lem_j.cnf` + `hints_j.txt`); each block is a separate Lean module
(`gen_chunks.py`), and Lean proves `unsat` from the blocks (`LratChunk.unsat_of_blocks`). `scripts/fetch_certs.sh`
regenerates the blocks with `split.py`; the result is byte-identical to the blocks used for the recorded build
(checked against `lean/DATA.sha256`).

## Re-checking

```sh
scripts/fetch_certs.sh        # unpack + verify hashes
scripts/check_drat.sh         # drat-trim on the 26 case certificates used by the theorem
```

To regenerate a no-K4 class from scratch (hours of CPU, several GB of intermediate conflict matrices), run in
`sat/w11ref/tr/`: `python3 tr_states.py a c [no24]`, `./run_conf.sh TAG`, `python3 tr_case.py TAG plan`, then
`tr_tree.py` per case (see `run_tree.sh`, `run_treeT.sh`, `pipeline.sh`), and compare the resulting `tree_*.cnf`
with `data/raw/e616/w11ref/tr/` (`sha256sum -c` against `SHA256SUMS.members`). For leaf (K), run in `sat/t21/w14/`:
`w14_states.py`, `w14_conf.py`, `w14_gac.py`, `w14_sac.py`, `w14_certdead.py`, then `run_tree2.sh`. Regeneration of
the full pipelines from scratch was not re-run for this release; the released CNFs are the ones the logs here refer to.
