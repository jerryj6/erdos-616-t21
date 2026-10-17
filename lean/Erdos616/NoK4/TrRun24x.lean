import Erdos616Checkers.TrCheck
import Erdos616.NoK4.WitData
import Erdos616.Cert.tree_24x_0
import Erdos616.Cert.tree_24x_1
import Erdos616.Cert.tree_24x_2
import Erdos616.Cert.tree_24x_3
import Erdos616.Cert.tree_24x_4
import Erdos616.Cert.tree_24x_5
import Erdos616.Cert.tree_24x_6
open TrCheck LratCheck

/-- the 7 (24x) case CNFs (the exact terms of the LRAT certificates) with their case units. -/
def cnfs24x : List (Std.Sat.CNF Nat × Nat) :=
  [(parseDimacs E616.tree_24x_0.cnfText, 3950),
   (parseDimacs E616.tree_24x_1.cnfText, 3959),
   (parseDimacs E616.tree_24x_2.cnfText, 3971),
   (parseDimacs E616.tree_24x_3.cnfText, 3978),
   (parseDimacs E616.tree_24x_4.cnfText, 4009),
   (parseDimacs E616.tree_24x_5.cnfText, 4021),
   (parseDimacs E616.tree_24x_6.cnfText, 4025)]

theorem ok24x : cls24x.checkAll cnfs24x Bs24x wit24x = true := by native_decide
#print axioms ok24x
