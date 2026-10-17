import Erdos616.G14.Glue
import Erdos616.Cert.w14_16054.Data
/-! G14 case r = T[16054] (chunk-mode certificate). Only the data module is imported (memory); the UNSAT theorem
`E616C.w14_16054.not_exists_sat` of the `w14_16054_Final` module (statement:
`¬ ∃ a, (LratChunk.parseDimacsFast cnfText).eval a = true`) is taken as the hypothesis `hns`. -/
open Std.Sat
namespace G14
theorem chk16054 : checkCNF (LratChunk.parseDimacsFast E616C.w14_16054.cnfText) [(16054, true)] = true := by native_decide
theorem case16054_of (hns : ¬ ∃ a : Nat → Bool, (LratChunk.parseDimacsFast E616C.w14_16054.cnfText).eval a = true)
    (hu : univOK () = true) (M : Model) (h : M.occ T[16054]!) : False := by
  apply hns
  refine ⟨assign M, eval_of_check M hu _ _ chk16054 ?_⟩
  have : assign M 16054 = true := assign_true.2 h
  simp [this]
end G14
#print axioms G14.case16054_of
