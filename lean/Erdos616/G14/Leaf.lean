import Erdos616.G14.Assembly
import Erdos616.Cert.w14_15954.Final
import Erdos616.Cert.w14_16054.Final
/-!
# Erdős #616, r = 21: HandA's leaf `NK4_leaf`, proved (G14), no hypotheses.
-/
namespace Erdos616R21

theorem NK4_leaf_proved : NK4_leaf :=
  NK4_leaf_of_chunked E616C.w14_15954.not_exists_sat E616C.w14_16054.not_exists_sat

end Erdos616R21

#print axioms Erdos616R21.NK4_leaf_proved
