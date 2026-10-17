import Erdos616.NoK4.Pair
import Erdos616.NoK4.TrRun34
import Erdos616.NoK4.TrRun24x
import Erdos616.NoK4.TrRun33
import Erdos616.NoK4.Build
import Erdos616.HandA

/-!
# Erdős #616, r = 21: encoding-soundness bridges for the N-noK4 leaves (2,4), (3,3), (3,4)

For each class the referee's independent trace encoding Φ_{a,c} (sat/w11ref/tr/, docs/referee/w11-referee.md
§5.1) is bridged: a `Base clsXX H` in a counterexample `H` (the labelled base configuration of that class) together with the
lemma-side hypothesis `CLSHyp` (W7-I, NK, N24 at every 5-pair; N24 not used for (2,4)) yields a Boolean assignment
(`x_t := some non-base edge has core trace t`, after relabelling by a base automorphism so that the root edge has the case
representative's trace) satisfying one of the case CNFs `tree_XX_k`, contradicting its Lean-checked `not_exists_sat`.

Sources (all in Erdos616/NoK4/): TrCheck (executable checker), TrRunXX (`native_decide` acceptance of the case CNFs),
NoK4Base / NoK4Frame (semantics, assignment, symmetry), NoK4Edge / NoK4Pair (rule soundness).
-/

open Finset TrCheck

namespace Erdos616R21.NoK4

variable {V : Type*} [DecidableEq V] {H : Finset (Finset V)}

/-! ### `CLSHyp` from HandA's lemma-level hypotheses -/

/-- with rule flags `0` (W7-I, NK, N24 on; N34 off) the class predicate holds on every admissible `(a, c)`. -/
theorem clsOk34 : ∀ a c : Fin 5, (1 ≤ (a : ℕ) ∧ 1 ≤ (c : ℕ) ∧ (a : ℕ) ≠ 1 ∧ (c : ℕ) ≠ 1 ∧ (a : ℕ) + c ≠ 5 ∧ 5 ≤ (a : ℕ) + c ∧
      ¬ ((a : ℕ) = 2 ∧ (c : ℕ) = 4) ∧ ¬ ((a : ℕ) = 4 ∧ (c : ℕ) = 2)) →
    cls34.clsOk a c = true := by decide
theorem clsOk33 : ∀ a c : Fin 5, (1 ≤ (a : ℕ) ∧ 1 ≤ (c : ℕ) ∧ (a : ℕ) ≠ 1 ∧ (c : ℕ) ≠ 1 ∧ (a : ℕ) + c ≠ 5 ∧ 5 ≤ (a : ℕ) + c ∧
      ¬ ((a : ℕ) = 2 ∧ (c : ℕ) = 4) ∧ ¬ ((a : ℕ) = 4 ∧ (c : ℕ) = 2)) →
    cls33.clsOk a c = true := by decide
/-- with rule flags `2` (N24 off), as used for the (2,4) class: no N24 hypothesis needed. -/
theorem clsOk24x : ∀ a c : Fin 5, (1 ≤ (a : ℕ) ∧ 1 ≤ (c : ℕ) ∧ (a : ℕ) ≠ 1 ∧ (c : ℕ) ≠ 1 ∧ (a : ℕ) + c ≠ 5 ∧ 5 ≤ (a : ℕ) + c) →
    cls24x.clsOk a c = true := by decide

/-- `CLSHyp` for (3,4)/(3,3) from HandA's `W7I_prop`, `NK_prop`, `N24_prop` and `cross_class`. -/
theorem clsHyp_of_props {C : Cls}
    (hok : ∀ a c : Fin 5, (1 ≤ (a : ℕ) ∧ 1 ≤ (c : ℕ) ∧ (a : ℕ) ≠ 1 ∧ (c : ℕ) ≠ 1 ∧ (a : ℕ) + c ≠ 5 ∧ 5 ≤ (a : ℕ) + c ∧
      ¬ ((a : ℕ) = 2 ∧ (c : ℕ) = 4) ∧ ¬ ((a : ℕ) = 4 ∧ (c : ℕ) = 2)) →
      C.clsOk a c = true)
    (hC : Counter H) (hW7 : W7I_prop H) (hNK : NK_prop H) (hN24 : N24_prop H) : CLSHyp C H := by
  intro X hX Y hY Z1 hZ1 Z2 hZ2 hM v w hv hw hvw
  have hcp : CrossPair H X Y Z1 Z2 := ⟨hX, hY, hZ1, hZ2, hM, v, w, hvw, hv, hw⟩
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := Erdos616R21.cross_class hC hX hY hZ1 hZ2 hM hv hw hvw
  obtain ⟨h7a, h7c⟩ := hW7 X Y Z1 Z2 hcp
  have hk := hNK X Y Z1 Z2 hcp
  have h5ne : (Z1 ∩ Z2 ∩ (X \ Y)).card + (Z1 ∩ Z2 ∩ (Y \ X)).card ≠ 5 := by omega
  obtain ⟨h24a, h24b⟩ := hN24 X Y Z1 Z2 hcp
  exact hok ⟨(Z1 ∩ Z2 ∩ (X \ Y)).card, by omega⟩ ⟨(Z1 ∩ Z2 ∩ (Y \ X)).card, by omega⟩ ⟨c1, c3, h7a, h7c, h5ne, c5, h24a, h24b⟩

/-- `CLSHyp` for (2,4) (flags 2) from `W7I_prop`, `NK_prop` and `cross_class` only. -/
theorem clsHyp_of_props24 (hC : Counter H) (hW7 : W7I_prop H) (hNK : NK_prop H) : CLSHyp cls24x H := by
  intro X hX Y hY Z1 hZ1 Z2 hZ2 hM v w hv hw hvw
  have hcp : CrossPair H X Y Z1 Z2 := ⟨hX, hY, hZ1, hZ2, hM, v, w, hvw, hv, hw⟩
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := Erdos616R21.cross_class hC hX hY hZ1 hZ2 hM hv hw hvw
  obtain ⟨h7a, h7c⟩ := hW7 X Y Z1 Z2 hcp
  have hk := hNK X Y Z1 Z2 hcp
  have h5ne : (Z1 ∩ Z2 ∩ (X \ Y)).card + (Z1 ∩ Z2 ∩ (Y \ X)).card ≠ 5 := by omega
  exact clsOk24x ⟨(Z1 ∩ Z2 ∩ (X \ Y)).card, by omega⟩ ⟨(Z1 ∩ Z2 ∩ (Y \ X)).card, by omega⟩ ⟨c1, c3, h7a, h7c, h5ne, c5⟩

theorem sane34 : cls34.clsSane = true := by decide
theorem sane33 : cls33.clsSane = true := by decide
theorem sane24x : cls24x.clsSane = true := by decide

/-- **(3,4) leaf**: no counterexample contains the labelled (3,4) base configuration (given W7-I, NK, N24 at every
5-pair, all three refereed lemmas of the hand proof). -/
theorem leaf34_base (hC : Counter H) (hcls : CLSHyp cls34 H) (B : Base cls34 H) : False := by
  refine leaf_of_sound cnfs34 Bs34 wit34 ok34 ?_ hC B (fun B' => B'.edgeSound sane34 hC hcls)
    (fun B' => B'.pairSound sane34 hC hcls)
  intro p hp
  simp only [cnfs34, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact E616.tree_34_0.not_exists_sat
  · exact E616.tree_34_1.not_exists_sat
  · exact E616.tree_34_2.not_exists_sat
  · exact E616.tree_34_3.not_exists_sat
  · exact E616.tree_34_4.not_exists_sat

/-- **(2,4) leaf** (no N24 used). -/
theorem leaf24_base (hC : Counter H) (hcls : CLSHyp cls24x H) (B : Base cls24x H) : False := by
  refine leaf_of_sound cnfs24x Bs24x wit24x ok24x ?_ hC B (fun B' => B'.edgeSound sane24x hC hcls)
    (fun B' => B'.pairSound sane24x hC hcls)
  intro p hp
  simp only [cnfs24x, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact E616.tree_24x_0.not_exists_sat
  · exact E616.tree_24x_1.not_exists_sat
  · exact E616.tree_24x_2.not_exists_sat
  · exact E616.tree_24x_3.not_exists_sat
  · exact E616.tree_24x_4.not_exists_sat
  · exact E616.tree_24x_5.not_exists_sat
  · exact E616.tree_24x_6.not_exists_sat

/-- **(3,3) leaf**. -/
theorem leaf33_base (hC : Counter H) (hcls : CLSHyp cls33 H) (B : Base cls33 H) : False := by
  refine leaf_of_sound cnfs33 Bs33 wit33 ok33 ?_ hC B (fun B' => B'.edgeSound sane33 hC hcls)
    (fun B' => B'.pairSound sane33 hC hcls)
  intro p hp
  simp only [cnfs33, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact E616.tree_33_0.not_exists_sat
  · exact E616.tree_33_1.not_exists_sat
  · exact E616.tree_33_2.not_exists_sat
  · exact E616.tree_33_3.not_exists_sat
  · exact E616.tree_33_4.not_exists_sat
  · exact E616.tree_33_5.not_exists_sat
  · exact E616.tree_33_6.not_exists_sat
  · exact E616.tree_33_7.not_exists_sat

/-! ### The leaves exactly as stated in HandA -/

/-- **HandA leaf `noK4_34_leaf`**: under W7-I, NK, N24 no cross pair has class (3,4). -/
theorem noK4_34_leaf_holds : Erdos616R21.noK4_34_leaf := by
  intro n H hC hW7 hNK hN24 X Y G G' hcp hac
  obtain ⟨hX, hY, hG, hG', hM, v, w, hvw, hv, hw⟩ := hcp
  obtain ⟨B⟩ := base_of_cross cls34 hC hX hY hG hG' hM hv hw hvw multi34 (by rw [hac.1, hac.2]; exact cnt34)
  exact leaf34_base hC (clsHyp_of_props clsOk34 hC hW7 hNK hN24) B

/-- **HandA leaf `noK4_33_leaf`**: under W7-I, NK, N24 no cross pair has class (3,3). -/
theorem noK4_33_leaf_holds : Erdos616R21.noK4_33_leaf := by
  intro n H hC hW7 hNK hN24 X Y G G' hcp hac
  obtain ⟨hX, hY, hG, hG', hM, v, w, hvw, hv, hw⟩ := hcp
  obtain ⟨B⟩ := base_of_cross cls33 hC hX hY hG hG' hM hv hw hvw multi33 (by rw [hac.1, hac.2]; exact cnt33)
  exact leaf33_base hC (clsHyp_of_props clsOk33 hC hW7 hNK hN24) B

/-- **HandA leaf `noK4_24_leaf`**: under W7-I, NK no cross pair has class (2,4) (N24 not used). -/
theorem noK4_24_leaf_holds : Erdos616R21.noK4_24_leaf := by
  intro n H hC hW7 hNK X Y G G' hcp hac
  obtain ⟨hX, hY, hG, hG', hM, v, w, hvw, hv, hw⟩ := hcp
  obtain ⟨B⟩ := base_of_cross cls24x hC hX hY hG hG' hM hv hw hvw multi24x (by rw [hac.1, hac.2]; exact cnt24x)
  exact leaf24_base hC (clsHyp_of_props24 hC hW7 hNK) B

end Erdos616R21.NoK4

#print axioms Erdos616R21.NoK4.noK4_34_leaf_holds
#print axioms Erdos616R21.NoK4.noK4_33_leaf_holds
#print axioms Erdos616R21.NoK4.noK4_24_leaf_holds
