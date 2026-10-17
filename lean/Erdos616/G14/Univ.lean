import Erdos616.G14.Root
/-! native_decide facts of the G14 bridge that do not need a certificate module. -/
namespace G14
theorem univ_ok : univOK () = true := by native_decide
theorem root_ok : rootOK = true := by native_decide
end G14
#print axioms G14.univ_ok
#print axioms G14.root_ok
