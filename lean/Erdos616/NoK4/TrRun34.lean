import Erdos616Checkers.TrCheck
import Erdos616.NoK4.WitData
import Erdos616.Cert.tree_34_0
import Erdos616.Cert.tree_34_1
import Erdos616.Cert.tree_34_2
import Erdos616.Cert.tree_34_3
import Erdos616.Cert.tree_34_4
open TrCheck LratCheck

/-- the 5 (34) case CNFs (the exact terms of the LRAT certificates) with their case units. -/
def cnfs34 : List (Std.Sat.CNF Nat × Nat) :=
  [(parseDimacs E616.tree_34_0.cnfText, 2649),
   (parseDimacs E616.tree_34_1.cnfText, 6317),
   (parseDimacs E616.tree_34_2.cnfText, 6324),
   (parseDimacs E616.tree_34_3.cnfText, 6500),
   (parseDimacs E616.tree_34_4.cnfText, 6506)]

theorem ok34 : cls34.checkAll cnfs34 Bs34 wit34 = true := by native_decide
#print axioms ok34
