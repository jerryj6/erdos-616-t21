import Erdos616.G14.Root
import Erdos616.Cert.w14_certdead
/-! G14 root step: a trace model containing a dead avoider of B* satisfies w14_certdead, which is UNSAT. -/
open Std.Sat LratCheck
namespace G14
theorem chkDead : checkCNF (parseDimacs E616.w14_certdead.cnfText) deadClause = true := by native_decide
theorem caseDead (hu : univOK () = true) (M : Model)
    (h : (deadClause.any fun (i, n) => assign M i == n) = true) : False := by
  apply E616.w14_certdead.not_exists_sat
  exact ⟨assign M, eval_of_check M hu _ _ chkDead h⟩
end G14
#print axioms G14.caseDead
