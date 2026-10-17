import Erdos616.G14.Glue
import Erdos616.Cert.w14_17917
/-! G14 case r = T[17917]: a trace model containing the representative trace satisfies the case CNF, which is UNSAT
(LRAT-checked theorem `E616.w14_17917.not_exists_sat`). -/
open Std.Sat LratCheck
namespace G14
theorem chk17917 : checkCNF (parseDimacs E616.w14_17917.cnfText) [(17917, true)] = true := by native_decide
theorem case17917 (hu : univOK () = true) (M : Model) (h : M.occ T[17917]!) : False := by
  apply E616.w14_17917.not_exists_sat
  refine ⟨assign M, eval_of_check M hu _ _ chk17917 ?_⟩
  have : assign M 17917 = true := assign_true.2 h
  simp [this]
end G14
#print axioms G14.case17917
