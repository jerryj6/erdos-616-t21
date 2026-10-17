import Erdos616.Cert.w14_15954.Data
open Std.Sat Std.Tactic.BVDecide.LRAT.Internal LratChunk
namespace E616C.w14_15954.B0
def hintText : String := include_str "../../../../data/chunks/w14_15954/hints_0.txt"
def ok : Bool := checkRups (State.ofCNF (G F L 0)) (L 0).clauses.toList (hintsOfLRAT hintText)
theorem ok_eq : ok = true := by native_decide
theorem step : ∀ a, CNF.Sat a (G F L 0) → CNF.Sat a (L 0) := block_sound _ _ _ ok_eq
end E616C.w14_15954.B0
