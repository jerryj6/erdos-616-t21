import Erdos616.Cert.w14_15954.B0
import Erdos616.Cert.w14_15954.B1
import Erdos616.Cert.w14_15954.B2
import Erdos616.Cert.w14_15954.B3
import Erdos616.Cert.w14_15954.B4
import Erdos616.Cert.w14_15954.B5
import Erdos616.Cert.w14_15954.B6
import Erdos616.Cert.w14_15954.B7
import Erdos616.Cert.w14_15954.B8
import Erdos616.Cert.w14_15954.B9
import Erdos616.Cert.w14_15954.B10
open Std.Sat LratChunk
namespace E616C.w14_15954
theorem hlast : hasEmpty (L 10) = true := by native_decide
/-- Every assignment falsifies the CNF of `w14_15954`. -/
theorem unsat : F.Unsat :=
  unsat_of_blocks F L 11 (fun j hj => match j, hj with
    | 0, _ => E616C.w14_15954.B0.step
    | 1, _ => E616C.w14_15954.B1.step
    | 2, _ => E616C.w14_15954.B2.step
    | 3, _ => E616C.w14_15954.B3.step
    | 4, _ => E616C.w14_15954.B4.step
    | 5, _ => E616C.w14_15954.B5.step
    | 6, _ => E616C.w14_15954.B6.step
    | 7, _ => E616C.w14_15954.B7.step
    | 8, _ => E616C.w14_15954.B8.step
    | 9, _ => E616C.w14_15954.B9.step
    | 10, _ => E616C.w14_15954.B10.step
    | _ + 11, h => absurd h (by omega)) (by decide) hlast
theorem not_exists_sat : ¬ ∃ a : Nat → Bool, (LratChunk.parseDimacsFast cnfText).eval a = true := by
  intro ⟨a, h⟩
  have := unsat a
  unfold F at this
  rw [this] at h
  exact Bool.false_ne_true h
#print axioms not_exists_sat
-- parser sanity: dump for external round-trip diff
#eval IO.FS.writeFile "../data/out/w14_15954.dimacs" F.dimacs
end E616C.w14_15954
