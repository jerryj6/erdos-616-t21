#!/usr/bin/env python3
"""gen.py NAME CNFPATH  -> certs/NAME.lean (expects lrat/NAME.lrat, symlinks data/NAME.cnf)"""
import sys, os
name, cnf = sys.argv[1], os.path.abspath(sys.argv[2])
here = os.path.dirname(os.path.abspath(__file__))
link = os.path.join(here, 'data', name + '.cnf')
if os.path.lexists(link): os.remove(link)
os.symlink(cnf, link)
ns = 'E616.' + name.replace('-', '_')
src = f'''import LratCheck
open LratCheck Std.Tactic.BVDecide Std.Sat

namespace {ns}

/-- The DIMACS text of `{os.path.relpath(cnf, here)}` (embedded verbatim at elaboration time). -/
def cnfText : String := include_str "../data/{name}.cnf"
/-- LRAT proof produced by `drat-trim CNF DRAT -L` (untrusted input). -/
def lratText : String := include_str "../lrat/{name}.lrat"

def certOk : Bool := LRAT.check (lratOf lratText) (parseDimacs cnfText)

theorem certOk_eq : certOk = true := by native_decide

/-- Every assignment falsifies the CNF. -/
theorem unsat : (parseDimacs cnfText).Unsat := LRAT.check_sound _ _ certOk_eq

/-- No Boolean assignment satisfies the CNF. -/
theorem not_exists_sat : ¬ ∃ a : Nat → Bool, (parseDimacs cnfText).eval a = true := by
  intro ⟨a, h⟩
  have := unsat a
  rw [this] at h
  exact Bool.false_ne_true h

#print axioms not_exists_sat

-- parser sanity: dump the parsed CNF back to DIMACS for an external diff
#eval IO.FS.writeFile "out/{name}.dimacs" (parseDimacs cnfText).dimacs

end {ns}
'''
open(os.path.join(here, 'certs', name + '.lean'), 'w').write(src)
