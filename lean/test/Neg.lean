import Erdos616.G14.Leaf
import Erdos616.NoK4.Assembly
/-! Erdős #616: t(21) = 4, end to end. -/
theorem erdos_616_t21_eq_4 :
    Hypergraph.localTransversalBound 21 (3 * 21 - 3) 1 = 5 :=
  erdos_616_r21_of_NK4 Erdos616R21.NK4_leaf_proved
#print axioms erdos_616_t21_eq_4
