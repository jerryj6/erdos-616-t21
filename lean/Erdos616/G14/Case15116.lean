import Erdos616.G14.Glue
import Erdos616.Cert.w14_15116
/-! G14 case r = T[15116]: a trace model containing the representative trace satisfies the case CNF, which is UNSAT
(LRAT-checked theorem `E616.w14_15116.not_exists_sat`). -/
open Std.Sat LratCheck
namespace G14
theorem chk15116 : checkCNF (parseDimacs E616.w14_15116.cnfText) [(15116, true)] = true := by native_decide
theorem case15116 (hu : univOK () = true) (M : Model) (h : M.occ T[15116]!) : False := by
  apply E616.w14_15116.not_exists_sat
  refine ⟨assign M, eval_of_check M hu _ _ chk15116 ?_⟩
  have : assign M 15116 = true := assign_true.2 h
  simp [this]
end G14
#print axioms G14.case15116
