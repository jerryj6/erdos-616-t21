# Documentation

* `proof-notes.md` — the full working notes of the upper-bound argument (all lemmas, the case analysis, the
  encodings, and their history). The paper in `paper/` is the curated version; where they differ, the paper and the
  Lean development take precedence.
* `referee/` — internal referee reports: `t21` (local lemmas, W6-U, W7-I), `n4` (exhaustiveness of the case split),
  `w10` and `w11` (no-K4 encodings; `w11` §5 defines the trace relaxations Φ_{a,c} used by Lean), `w14` (leaf (K)).
* `lean-reports/` — reports written while the Lean formalization was built: `plan`, `main` (statement, reduction,
  local lemmas), `handA` (W6-U, case split), `w7i`, `lrat` (LRAT layer), `bridge-g14`, `bridge-nok4`, `final`.
  Long Lean listings that duplicate files now under `lean/` have been replaced by a pointer.
* `loop-notes.md` — early notes (core reformulation, CEGAR searches, symmetric sweeps); scripts in `sat/`.

**These are internal working notes**, kept for provenance. They were written during development, with
computational (AI-agent) assistance, and mention run names and timings of the original working environment. They are not peer review.
