import Lake
open Lake DSL

/-!
Lake project for the Lean formalization of Erdős Problem #616 at r = 21.

* `Erdos616Checkers`: executable checkers that use only Lean core (no Mathlib). They are compiled to native
  shared libraries (`precompileModules`), so the `native_decide` evaluations in dependent modules run native code.
* `Erdos616`: the mathematics (Mathlib) together with the certificate modules. The certificate modules embed CNF and
  LRAT files from `data/` with `include_str`; populate `data/` with `scripts/fetch_certs.sh` before building.
-/

package erdos616 where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"

lean_lib Erdos616Checkers where
  precompileModules := true

@[default_target]
lean_lib Erdos616 where
