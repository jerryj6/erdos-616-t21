import Erdos616Checkers.LratCheck
open LratCheck Std.Tactic.BVDecide Std.Sat

namespace E616.w14_15116

/-- The DIMACS text of `sat/t21/w14/w14_cert2_15116.cnf` (embedded verbatim at elaboration time). -/
def cnfText : String := include_str "../../../data/cnf/w14_15116.cnf"
/-- LRAT proof produced by `drat-trim CNF DRAT -L` (untrusted input). -/
def lratText : String := include_str "../../../data/lrat/w14_15116.lrat"

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
#eval IO.FS.writeFile "../data/out/w14_15116.dimacs" (parseDimacs cnfText).dimacs

end E616.w14_15116
