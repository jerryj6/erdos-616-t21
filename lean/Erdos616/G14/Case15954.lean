import Erdos616.G14.Glue
import Erdos616.Cert.w14_15954.Data
/-! G14 case r = T[15954] (chunk-mode certificate). Only the data module is imported (memory); the UNSAT theorem
`E616C.w14_15954.not_exists_sat` of the `w14_15954_Final` module (statement:
`¬ ∃ a, (LratChunk.parseDimacsFast cnfText).eval a = true`) is taken as the hypothesis `hns`. -/
open Std.Sat
namespace G14
theorem chk15954 : checkCNF (LratChunk.parseDimacsFast E616C.w14_15954.cnfText) [(15954, true)] = true := by native_decide
theorem case15954_of (hns : ¬ ∃ a : Nat → Bool, (LratChunk.parseDimacsFast E616C.w14_15954.cnfText).eval a = true)
    (hu : univOK () = true) (M : Model) (h : M.occ T[15954]!) : False := by
  apply hns
  refine ⟨assign M, eval_of_check M hu _ _ chk15954 ?_⟩
  have : assign M 15954 = true := assign_true.2 h
  simp [this]
end G14
#print axioms G14.case15954_of
