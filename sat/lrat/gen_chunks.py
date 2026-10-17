#!/usr/bin/env python3
"""gen_chunks.py NAME NBLOCKS : write chunks/NAME/{NAME_Data,NAME_B<j>,NAME_Final}.lean"""
import sys
name, k = sys.argv[1], int(sys.argv[2])
d=f'chunks/{name}'; ns='E616C.'+name
lem='\n'.join(f'def lemText{j} : String := include_str "lem_{j}.cnf"' for j in range(k))
open(f'{d}/{name}_Data.lean','w').write(f'''import LratChunk
open Std.Sat
namespace {ns}
/-- DIMACS text of the certificate CNF (embedded verbatim). -/
def cnfText : String := include_str "../../data/{name}.cnf"
{lem}
def lemTexts : Array String := #[{", ".join(f"lemText{j}" for j in range(k))}]
/-- the CNF of the theorem -/
def F : CNF Nat := LratChunk.parseDimacsFast cnfText
/-- lemma blocks (untrusted data: each is re-verified as RUP) -/
def L (j : Nat) : CNF Nat := LratChunk.parseDimacsFast (lemTexts.getD j "")
end {ns}
''')
for j in range(k):
    open(f'{d}/{name}_B{j}.lean','w').write(f'''import {name}_Data
open Std.Sat Std.Tactic.BVDecide.LRAT.Internal LratChunk
namespace {ns}.B{j}
def hintText : String := include_str "hints_{j}.txt"
def ok : Bool := checkRups (State.ofCNF (G F L {j})) (L {j}).clauses.toList (hintsOfLRAT hintText)
theorem ok_eq : ok = true := by native_decide
theorem step : ∀ a, CNF.Sat a (G F L {j}) → CNF.Sat a (L {j}) := block_sound _ _ _ ok_eq
end {ns}.B{j}
''')
imports='\n'.join(f'import {name}_B{j}' for j in range(k))
cases='\n'.join(f'    | {j}, _ => {ns}.B{j}.step' for j in range(k))
open(f'{d}/{name}_Final.lean','w').write(f'''{imports}
open Std.Sat LratChunk
namespace {ns}
theorem hlast : hasEmpty (L {k-1}) = true := by native_decide
/-- Every assignment falsifies the CNF of `{name}`. -/
theorem unsat : F.Unsat :=
  unsat_of_blocks F L {k} (fun j hj => match j, hj with
{cases}
    | _ + {k}, h => absurd h (by omega)) (by decide) hlast
theorem not_exists_sat : ¬ ∃ a : Nat → Bool, (LratChunk.parseDimacsFast cnfText).eval a = true := by
  intro ⟨a, h⟩
  have := unsat a
  unfold F at this
  rw [this] at h
  exact Bool.false_ne_true h
#print axioms not_exists_sat
-- parser sanity: dump for external round-trip diff
#eval IO.FS.writeFile "out/{name}.dimacs" F.dimacs
end {ns}
''')
print('ok')
