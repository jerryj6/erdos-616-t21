import Erdos616Checkers.TrCheck
import Erdos616.NoK4.WitData
import Erdos616.Cert.tree_33_0
import Erdos616.Cert.tree_33_1
import Erdos616.Cert.tree_33_2
import Erdos616.Cert.tree_33_3
import Erdos616.Cert.tree_33_4
import Erdos616.Cert.tree_33_5
import Erdos616.Cert.tree_33_6
import Erdos616.Cert.tree_33_7
open TrCheck LratCheck

/-- the 8 (33) case CNFs (the exact terms of the LRAT certificates) with their case units. -/
def cnfs33 : List (Std.Sat.CNF Nat × Nat) :=
  [(parseDimacs E616.tree_33_0.cnfText, 2531),
   (parseDimacs E616.tree_33_1.cnfText, 2538),
   (parseDimacs E616.tree_33_2.cnfText, 2818),
   (parseDimacs E616.tree_33_3.cnfText, 2827),
   (parseDimacs E616.tree_33_4.cnfText, 4075),
   (parseDimacs E616.tree_33_5.cnfText, 5525),
   (parseDimacs E616.tree_33_6.cnfText, 5532),
   (parseDimacs E616.tree_33_7.cnfText, 5691)]

theorem ok33 : cls33.checkAll cnfs33 Bs33 wit33 = true := by native_decide
#print axioms ok33
