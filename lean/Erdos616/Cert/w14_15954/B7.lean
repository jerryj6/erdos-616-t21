import Erdos616.Cert.w14_15954.Data
open Std.Sat Std.Tactic.BVDecide.LRAT.Internal LratChunk
namespace E616C.w14_15954.B7
def hintText : String := include_str "../../../../data/chunks/w14_15954/hints_7.txt"
def ok : Bool := checkRups (State.ofCNF (G F L 7)) (L 7).clauses.toList (hintsOfLRAT hintText)
theorem ok_eq : ok = true := by native_decide
theorem step : ∀ a, CNF.Sat a (G F L 7) → CNF.Sat a (L 7) := block_sound _ _ _ ok_eq
end E616C.w14_15954.B7
