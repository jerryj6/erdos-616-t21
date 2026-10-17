import Erdos616.NoK4.Leaves
import Erdos616.W7I

/-! Assembly check: with the three N-noK4 leaves (this bridge) and W7-I (W7I.lean), HandA reduces t(21) = 4 to the
single remaining leaf `NK4_leaf` (G14). -/

theorem erdos_616_r21_of_NK4 (hK4 : Erdos616R21.NK4_leaf) :
    Hypergraph.localTransversalBound 21 (3 * 21 - 3) 1 = 4 :=
  Erdos616R21.erdos_616_r21_of_leaves Erdos616R21.W7I.W7I_leaf hK4 Erdos616R21.NoK4.noK4_24_leaf_holds
    Erdos616R21.NoK4.noK4_33_leaf_holds Erdos616R21.NoK4.noK4_34_leaf_holds

#print axioms erdos_616_r21_of_NK4
