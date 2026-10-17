import Erdos616.Cert.w14_16054.Data
open Std.Sat Std.Tactic.BVDecide.LRAT.Internal LratChunk
namespace E616C.w14_16054.B2
def hintText : String := include_str "../../../../data/chunks/w14_16054/hints_2.txt"
def ok : Bool := checkRups (State.ofCNF (G F L 2)) (L 2).clauses.toList (hintsOfLRAT hintText)
theorem ok_eq : ok = true := by native_decide
theorem step : ∀ a, CNF.Sat a (G F L 2) → CNF.Sat a (L 2) := block_sound _ _ _ ok_eq
end E616C.w14_16054.B2
