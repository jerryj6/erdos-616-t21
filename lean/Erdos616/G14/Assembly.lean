import Erdos616.G14.BridgeFinal
import Erdos616.G14.Univ
import Erdos616.G14.Case15116
import Erdos616.G14.Case17917
import Erdos616.G14.Case14968
import Erdos616.G14.Case15954
import Erdos616.G14.Case16054
import Erdos616.G14.CaseDead
/-!
# Erdős #616, r = 21: HandA's `NK4_leaf`, with every certificate fact discharged except the UNSAT statements of the two
chunked certificates (w14_15954, w14_16054), which are taken as hypotheses literally equal to the statements of
`E616C.w14_15954.not_exists_sat` / `E616C.w14_16054.not_exists_sat` (modules `w14_*_Final`, ≈1.15 GB of oleans each).
`G14Close.lean` discharges them.
-/
namespace Erdos616R21

theorem NK4_leaf_of_chunked
    (h15954 : ¬ ∃ a : Nat → Bool, (LratChunk.parseDimacsFast E616C.w14_15954.cnfText).eval a = true)
    (h16054 : ¬ ∃ a : Nat → Bool, (LratChunk.parseDimacsFast E616C.w14_16054.cnfText).eval a = true) :
    NK4_leaf := by
  apply NK4_leaf_of_certs G14.univ_ok G14.root_ok
  · intro r hr M hM
    simp only [G14.reps, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact G14.case14968 G14.univ_ok M hM
    · exact G14.case15116 G14.univ_ok M hM
    · exact G14.case15954_of h15954 G14.univ_ok M hM
    · exact G14.case16054_of h16054 G14.univ_ok M hM
    · exact G14.case17917 G14.univ_ok M hM
  · exact G14.caseDead G14.univ_ok

end Erdos616R21

#print axioms Erdos616R21.NK4_leaf_of_chunked
