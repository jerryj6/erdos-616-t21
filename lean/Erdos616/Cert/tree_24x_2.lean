import Erdos616Checkers.LratCheck
open LratCheck Std.Tactic.BVDecide Std.Sat

namespace E616.tree_24x_2

/-- The DIMACS text of `sat/w11ref/tr/tree_24x_2.cnf` (embedded verbatim at elaboration time). -/
def cnfText : String := include_str "../../../data/cnf/tree_24x_2.cnf"
/-- LRAT proof produced by `drat-trim CNF DRAT -L` (untrusted input). -/
def lratText : String := include_str "../../../data/lrat/tree_24x_2.lrat"

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
#eval IO.FS.writeFile "../data/out/tree_24x_2.dimacs" (parseDimacs cnfText).dimacs

end E616.tree_24x_2
