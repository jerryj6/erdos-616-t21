import Erdos616.G14.Glue
import Erdos616.Cert.w14_14968
/-! G14 case r = T[14968]: a trace model containing the representative trace satisfies the case CNF, which is UNSAT
(LRAT-checked theorem `E616.w14_14968.not_exists_sat`). -/
open Std.Sat LratCheck
namespace G14
theorem chk14968 : checkCNF (parseDimacs E616.w14_14968.cnfText) [(14968, true)] = true := by native_decide
theorem case14968 (hu : univOK () = true) (M : Model) (h : M.occ T[14968]!) : False := by
  apply E616.w14_14968.not_exists_sat
  refine ⟨assign M, eval_of_check M hu _ _ chk14968 ?_⟩
  have : assign M 14968 = true := assign_true.2 h
  simp [this]
end G14
#print axioms G14.case14968
