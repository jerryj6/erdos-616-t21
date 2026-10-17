import Erdos616.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fin.SuccPred
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Erdős #616, r = 21 — part HAND-A

Builds on `Full.lean` (compiled as module `E616Full`).  Contents:

* **Theorem W6-U** (upper.md §6.3): if every 5-pair is uniform, there is no counterexample.
  Fully formal, no computation: the Kneser-reachability step is replaced by an element-swap
  induction, and the 715-set closure by a two-step "relative of a relative" argument.
* **The Case-N split** (n4-referee steps 1–5; N.4 / N8.0): non-uniform pair ⇒ a cross pair of class
  ≠ (4,4); NK dichotomy; a pair with `|Z∩Z'| = 5` and W7-I gives a (3,2,1,1)-K4; under NK the
  classes are (2,4),(4,2),(3,3),(3,4),(4,3) ((4,4) excluded); (4,2),(4,3) via the E1↔E2 swap.
* **Lemma KB** (pool bound, upper.md X.2) in generic double-counting form, plus the injection into
  a pool of size `K` and the two `ν` bounds.
* **Assembly**: `erdos_616_r21_of_leaves` derives `localTransversalBound 21 (3*21-3) 1 = 4` from the
  five leaf hypotheses `W7I_leaf`, `NK4_leaf`, `noK4_24_leaf`, `noK4_33_leaf`, `noK4_34_leaf`.
-/

namespace Erdos616R21
open Finset

/-! ## Definitions used by the case split and the leaves -/

section Defs
variable {V : Type*} [DecidableEq V]

/-- `G`, `G'` are singles of *different* types of the 5-pair `(X, Y)`. -/
def CrossPair (H : Finset (Finset V)) (X Y G G' : Finset V) : Prop :=
  X ∈ H ∧ Y ∈ H ∧ G ∈ H ∧ G' ∈ H ∧ (X ∩ Y).card = 5 ∧
  ∃ v w : V, v ≠ w ∧ G ∩ (X ∩ Y) = {v} ∧ G' ∩ (X ∩ Y) = {w}

/-- A 5-pair `(X,Y)` is uniform: all its singles (of all types) have the same `A`-part
`F ∩ (X ∖ Y)` and the same `C`-part `F ∩ (Y ∖ X)`. -/
def UniformPair (H : Finset (Finset V)) (X Y : Finset V) : Prop :=
  ∀ F ∈ H, ∀ F' ∈ H, ∀ x y : V, F ∩ (X ∩ Y) = {x} → F' ∩ (X ∩ Y) = {y} →
    F ∩ (X \ Y) = F' ∩ (X \ Y) ∧ F ∩ (Y \ X) = F' ∩ (Y \ X)

/-- Case U: every 5-pair is uniform. -/
def AllUniform (H : Finset (Finset V)) : Prop :=
  ∀ X ∈ H, ∀ Y ∈ H, (X ∩ Y).card = 5 → UniformPair H X Y

/-- Conclusion of Theorem W7-I for `H`: no 5-pair has cross-type singles with `a = 1` or `c = 1`
(`a = |A_G ∩ A_G'|`, `c = |C_G ∩ C_G'|`). -/
def W7I_prop (H : Finset (Finset V)) : Prop :=
  ∀ X Y G G' : Finset V, CrossPair H X Y G G' →
    (G ∩ G' ∩ (X \ Y)).card ≠ 1 ∧ (G ∩ G' ∩ (Y \ X)).card ≠ 1

/-- NK (N8.0): at every 5-pair, cross-type singles never meet in exactly 5 points. -/
def NK_prop (H : Finset (Finset V)) : Prop :=
  ∀ X Y G G' : Finset V, CrossPair H X Y G G' → (G ∩ G').card ≠ 5

/-- N24 (the w10x theorem, used as a tag by w11): no cross pair of class (2,4) or (4,2). -/
def N24_prop (H : Finset (Finset V)) : Prop :=
  ∀ X Y G G' : Finset V, CrossPair H X Y G G' →
    ¬ ((G ∩ G' ∩ (X \ Y)).card = 2 ∧ (G ∩ G' ∩ (Y \ X)).card = 4) ∧
    ¬ ((G ∩ G' ∩ (X \ Y)).card = 4 ∧ (G ∩ G' ∩ (Y \ X)).card = 2)

/-- A (3,2,1,1)-K4: four edges, pairwise meeting in exactly 5, no common point, triple
intersections of sizes 1, 1, 3, 2 (labelled so that `P0 = E1`, `P1 = E2`, `P2 = G`, `P3 = G'`
for a cross pair of class (3,2)). -/
def K4_3211 (H : Finset (Finset V)) : Prop :=
  ∃ P0 ∈ H, ∃ P1 ∈ H, ∃ P2 ∈ H, ∃ P3 ∈ H,
    (P0 ∩ P1).card = 5 ∧ (P0 ∩ P2).card = 5 ∧ (P0 ∩ P3).card = 5 ∧
    (P1 ∩ P2).card = 5 ∧ (P1 ∩ P3).card = 5 ∧ (P2 ∩ P3).card = 5 ∧
    P0 ∩ P1 ∩ P2 ∩ P3 = ∅ ∧
    (P0 ∩ P1 ∩ P2).card = 1 ∧ (P0 ∩ P1 ∩ P3).card = 1 ∧
    (P0 ∩ P2 ∩ P3).card = 3 ∧ (P1 ∩ P2 ∩ P3).card = 2

/-- "good" 5-pair relative to the 13-set `S` (upper.md §6.3): `X ∩ Y ⊆ S` and every single `F`
of type `y` satisfies `F ∩ (X ∪ Y) = S ∖ (N ∖ {y})`. -/
def Good (H : Finset (Finset V)) (S X Y : Finset V) : Prop :=
  X ∈ H ∧ Y ∈ H ∧ (X ∩ Y).card = 5 ∧ X ∩ Y ⊆ S ∧
  ∀ F ∈ H, ∀ y : V, F ∩ (X ∩ Y) = {y} → F ∩ (X ∪ Y) = S \ ((X ∩ Y).erase y)

theorem good_symm {H : Finset (Finset V)} {S X Y : Finset V} (h : Good H S X Y) :
    Good H S Y X := by
  obtain ⟨hX, hY, h5, hS, hF⟩ := h
  refine ⟨hY, hX, by rwa [inter_comm Y X], by rwa [inter_comm Y X], fun F hF' y hy => ?_⟩
  rw [inter_comm Y X] at hy ⊢
  rw [union_comm Y X]
  exact hF F hF' y hy

theorem crossPair_swap {H : Finset (Finset V)} {X Y G G' : Finset V}
    (h : CrossPair H X Y G G') : CrossPair H Y X G G' := by
  obtain ⟨hX, hY, hG, hG', h5, v, w, hvw, hv, hw⟩ := h
  exact ⟨hY, hX, hG, hG', by rwa [inter_comm Y X], v, w, hvw, by rwa [inter_comm Y X],
    by rwa [inter_comm Y X]⟩

end Defs

/-! ## Leaf hypotheses (to be discharged by the other parts) -/

/-- Leaf W7-I (Theorem W7-I, upper.md §7.4): triangles are excluded globally. -/
def W7I_leaf : Prop :=
  ∀ (n : ℕ) (H : Finset (Finset (Fin n))), Counter H → W7I_prop H

/-- Leaf N-K4 (G14): under W7-I there is no (3,2,1,1)-K4. -/
def NK4_leaf : Prop :=
  ∀ (n : ℕ) (H : Finset (Finset (Fin n))), Counter H → W7I_prop H → ¬ K4_3211 H

/-- Leaf N-noK4 (2,4) (w10x): under W7-I and NK no cross pair has class (2,4). -/
def noK4_24_leaf : Prop :=
  ∀ (n : ℕ) (H : Finset (Finset (Fin n))), Counter H → W7I_prop H → NK_prop H →
    ∀ X Y G G' : Finset (Fin n), CrossPair H X Y G G' →
      ¬ ((G ∩ G' ∩ (X \ Y)).card = 2 ∧ (G ∩ G' ∩ (Y \ X)).card = 4)

/-- Leaf N-noK4 (3,3) (w11): under W7-I, NK and N24 no cross pair has class (3,3). -/
def noK4_33_leaf : Prop :=
  ∀ (n : ℕ) (H : Finset (Finset (Fin n))), Counter H → W7I_prop H → NK_prop H → N24_prop H →
    ∀ X Y G G' : Finset (Fin n), CrossPair H X Y G G' →
      ¬ ((G ∩ G' ∩ (X \ Y)).card = 3 ∧ (G ∩ G' ∩ (Y \ X)).card = 3)

/-- Leaf N-noK4 (3,4) (w11): under W7-I, NK and N24 no cross pair has class (3,4). -/
def noK4_34_leaf : Prop :=
  ∀ (n : ℕ) (H : Finset (Finset (Fin n))), Counter H → W7I_prop H → NK_prop H → N24_prop H →
    ∀ X Y G G' : Finset (Fin n), CrossPair H X Y G G' →
      ¬ ((G ∩ G' ∩ (X \ Y)).card = 3 ∧ (G ∩ G' ∩ (Y \ X)).card = 4)

/-! ## Theorem W6-U -/

section W6U
variable {V : Type*} [DecidableEq V] {H : Finset (Finset V)} (hC : Counter H)
include hC

/-- Basic facts about a good pair: `S ⊆ X ∪ Y`, `|X ∩ S| = 9`, `|X ∖ S| = 12`. -/
theorem good_facts {S X Y : Finset V} (h : Good H S X Y) :
    S ⊆ X ∪ Y ∧ (X ∩ S).card = 9 ∧ (X \ S).card = 12 := by
  obtain ⟨hX, hY, h5, hS, hF⟩ := h
  obtain ⟨y, hy⟩ : (X ∩ Y).Nonempty := card_pos.1 (by omega)
  obtain ⟨F, hFH, hFy⟩ := R2 hC hX hY h5 hy
  have hE := hF F hFH y hFy
  have pt : ∀ z, (z ∈ F ∧ (z ∈ X ∨ z ∈ Y)) ↔ (z ∈ S ∧ ¬ (z ≠ y ∧ z ∈ X ∧ z ∈ Y)) := by
    intro z
    have := Finset.ext_iff.1 hE z
    simp only [mem_inter, mem_union, mem_sdiff, mem_erase] at this
    exact this
  have hSub : S ⊆ X ∪ Y := by
    intro z hz
    rw [mem_union]
    by_cases hzX : z ∈ X
    · exact Or.inl hzX
    · have := (pt z).2 ⟨hz, fun h => hzX h.2.1⟩
      exact this.2
  have hXS : X ∩ S = (X ∩ Y) ∪ (F ∩ (X \ Y)) := by
    ext z
    simp only [mem_inter, mem_union, mem_sdiff]
    constructor
    · rintro ⟨hzX, hzS⟩
      by_cases hzY : z ∈ Y
      · exact Or.inl ⟨hzX, hzY⟩
      · exact Or.inr ⟨((pt z).2 ⟨hzS, fun h => hzY h.2.2⟩).1, hzX, hzY⟩
    · rintro (⟨hzX, hzY⟩ | ⟨hzF, hzX, hzY⟩)
      · exact ⟨hzX, hS (mem_inter.2 ⟨hzX, hzY⟩)⟩
      · exact ⟨hzX, ((pt z).1 ⟨hzF, Or.inl hzX⟩).1⟩
  have hdis : Disjoint (X ∩ Y) (F ∩ (X \ Y)) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    simp only [mem_inter, mem_sdiff] at hz hz'
    exact hz'.2.2 hz.2
  obtain ⟨hFX, -, -⟩ := single_card hC hX hY hFH h5 hFy
  have l1 := card_split_left F X Y
  rw [hFy, card_singleton] at l1
  have h9 : (X ∩ S).card = 9 := by
    rw [hXS, card_union_of_disjoint hdis]; omega
  have hs := card_sdiff_add_card_inter X S
  rw [hC.unif X hX] at hs
  exact ⟨hSub, h9, by omega⟩

/-- Propagation G (upper.md §6.3): if `(X,Y)` is good and `F` is a single of type `y`, then
`(X,F)` is good and `X ∩ F = {y} ∪ ((X ∩ S) ∖ Y)`. -/
theorem good_step (hU : AllUniform H) {S X Y F : Finset V} {y : V} (h : Good H S X Y)
    (hFH : F ∈ H) (hFy : F ∩ (X ∩ Y) = {y}) :
    Good H S X F ∧ X ∩ F = insert y ((X ∩ S) \ Y) := by
  have hfacts := good_facts hC h
  obtain ⟨hX, hY, h5, hS, hF⟩ := h
  have hE := hF F hFH y hFy
  have pt : ∀ z, (z ∈ F ∧ (z ∈ X ∨ z ∈ Y)) ↔ (z ∈ S ∧ ¬ (z ≠ y ∧ z ∈ X ∧ z ∈ Y)) := by
    intro z
    have := Finset.ext_iff.1 hE z
    simp only [mem_inter, mem_union, mem_sdiff, mem_erase] at this
    exact this
  have sg : ∀ z, (z ∈ F ∧ z ∈ X ∧ z ∈ Y) ↔ z = y := by
    intro z
    have := Finset.ext_iff.1 hFy z
    simp only [mem_inter, mem_singleton] at this
    exact this
  have hyF : y ∈ F ∧ y ∈ X ∧ y ∈ Y := (sg y).2 rfl
  have hXF : X ∩ F = insert y ((X ∩ S) \ Y) := by
    ext z
    simp only [mem_inter, mem_insert, mem_sdiff]
    constructor
    · rintro ⟨hzX, hzF⟩
      by_cases hzY : z ∈ Y
      · exact Or.inl ((sg z).1 ⟨hzF, hzX, hzY⟩)
      · exact Or.inr ⟨⟨hzX, ((pt z).1 ⟨hzF, Or.inl hzX⟩).1⟩, hzY⟩
    · rintro (rfl | ⟨⟨hzX, hzS⟩, hzY⟩)
      · exact ⟨hyF.2.1, hyF.1⟩
      · exact ⟨hzX, ((pt z).2 ⟨hzS, fun h => hzY h.2.2⟩).1⟩
  refine ⟨⟨hX, hFH, ?_, ?_, ?_⟩, hXF⟩
  · rw [inter_comm]; exact (single_card hC hX hY hFH h5 hFy).1
  · rw [hXF]
    intro z hz
    rw [mem_insert] at hz
    rcases hz with rfl | hz
    · exact hS (mem_inter.2 ⟨hyF.2.1, hyF.2.2⟩)
    · exact (mem_inter.1 (mem_sdiff.1 hz).1).2
  · intro F' hF'H z hz
    have h5' : (X ∩ F).card = 5 := by
      rw [inter_comm]; exact (single_card hC hX hY hFH h5 hFy).1
    have hYs : Y ∩ (X ∩ F) = {y} := by
      ext w
      simp only [mem_inter, mem_singleton]
      constructor
      · rintro ⟨hwY, hwX, hwF⟩; exact (sg w).1 ⟨hwF, hwX, hwY⟩
      · rintro rfl; exact ⟨hyF.2.2, hyF.2.1, hyF.1⟩
    obtain ⟨e1, e2⟩ := hU X hX F hFH h5' F' hF'H Y hY z y hz hYs
    have p1 : ∀ w, (w ∈ F' ∧ w ∈ X ∧ w ∈ F) ↔ w = z := by
      intro w
      have := Finset.ext_iff.1 hz w
      simp only [mem_inter, mem_singleton] at this
      exact this
    have p2 : ∀ w, (w ∈ F' ∧ w ∈ X ∧ w ∉ F) ↔ (w ∈ Y ∧ w ∈ X ∧ w ∉ F) := by
      intro w
      have := Finset.ext_iff.1 e1 w
      simp only [mem_inter, mem_sdiff] at this
      exact this
    have p3 : ∀ w, (w ∈ F' ∧ w ∈ F ∧ w ∉ X) ↔ (w ∈ Y ∧ w ∈ F ∧ w ∉ X) := by
      intro w
      have := Finset.ext_iff.1 e2 w
      simp only [mem_inter, mem_sdiff] at this
      exact this
    have hz' : z ∈ F' ∧ z ∈ X ∧ z ∈ F := (p1 z).2 rfl
    have hzS : z ∈ S := ((pt z).1 ⟨hz'.2.2, Or.inl hz'.2.1⟩).1
    ext w
    simp only [mem_inter, mem_union, mem_sdiff, mem_erase]
    by_cases hwz : w = z
    · subst hwz
      simp only [hz'.1, hz'.2.1, hz'.2.2, hzS, true_and, true_or, ne_eq, not_true_eq_false,
        false_and, not_false_eq_true]
    · have q1 : ¬ (w ∈ F' ∧ w ∈ X ∧ w ∈ F) := fun h => hwz ((p1 w).1 h)
      have q2 := p2 w
      have q3 := p3 w
      have q4 := pt w
      have q5 : w ∈ X → w ∈ Y → w ∈ S := fun a b => hS (mem_inter.2 ⟨a, b⟩)
      have q6 : w ∈ S → w ∈ X ∨ w ∈ Y := fun a => mem_union.1 (hfacts.1 a)
      constructor
      · rintro ⟨hwF', hwXF⟩
        refine ⟨?_, fun h => q1 ⟨hwF', h.2.1, h.2.2⟩⟩
        by_cases hwX : w ∈ X
        · by_cases hwF : w ∈ F
          · exact absurd ⟨hwF', hwX, hwF⟩ q1
          · exact q5 hwX (q2.1 ⟨hwF', hwX, hwF⟩).1
        · have hwF : w ∈ F := hwXF.resolve_left hwX
          have hwY := (q3.1 ⟨hwF', hwF, hwX⟩).1
          exact (q4.1 ⟨hwF, Or.inr hwY⟩).1
      · rintro ⟨hwS, hno⟩
        by_cases hwX : w ∈ X
        · have hwF : w ∉ F := fun hwF => hno ⟨hwz, hwX, hwF⟩
          have hwY : w ∈ Y := by
            by_contra hwY
            exact hwF ((q4.2 ⟨hwS, fun h => hwY h.2.2⟩).1)
          exact ⟨(q2.2 ⟨hwY, hwX, hwF⟩).1, Or.inl hwX⟩
        · have hwY : w ∈ Y := (q6 hwS).resolve_left hwX
          have hwF : w ∈ F := ((q4.2 ⟨hwS, fun h => hwX h.2.1⟩).1)
          exact ⟨(q3.2 ⟨hwY, hwF, hwX⟩).1, Or.inr hwF⟩

/-- Two applications of G swap one point of `N = X ∩ Y` for one point of `(X ∩ S) ∖ Y`. -/
theorem good_swap (hU : AllUniform H) {S X Y : Finset V} {y z : V} (h : Good H S X Y)
    (hy : y ∈ X ∩ Y) (hzX : z ∈ X ∩ S) (hzY : z ∉ Y) :
    ∃ Z, Good H S X Z ∧ X ∩ Z = insert z ((X ∩ Y).erase y) := by
  obtain ⟨hX, hY, h5, -, -⟩ := id h
  obtain ⟨F, hFH, hFy⟩ := R2 hC hX hY h5 hy
  obtain ⟨hgF, hXF⟩ := good_step hC hU h hFH hFy
  have hzXF : z ∈ X ∩ F := by
    rw [hXF]; exact mem_insert_of_mem (mem_sdiff.2 ⟨hzX, hzY⟩)
  obtain ⟨F', hF'H, hF'z⟩ := R2 hC hX hFH hgF.2.2.1 hzXF
  obtain ⟨hgF', hXF'⟩ := good_step hC hU hgF hF'H hF'z
  refine ⟨F', hgF', ?_⟩
  rw [hXF']
  congr 1
  have hS : X ∩ Y ⊆ S := h.2.2.2.1
  ext w
  have hw := Finset.ext_iff.1 hXF w
  simp only [mem_inter, mem_insert, mem_sdiff] at hw
  simp only [mem_inter, mem_sdiff, mem_erase]
  constructor
  · rintro ⟨⟨hwX, hwS⟩, hwF⟩
    have hn : ¬ (w = y ∨ (w ∈ X ∧ w ∈ S) ∧ w ∉ Y) := fun h' => hwF (hw.2 h').2
    push Not at hn
    exact ⟨hn.1, hwX, hn.2 ⟨hwX, hwS⟩⟩
  · rintro ⟨hwy, hwX, hwY⟩
    refine ⟨⟨hwX, hS (mem_inter.2 ⟨hwX, hwY⟩)⟩, fun hwF => ?_⟩
    rcases hw.1 ⟨hwX, hwF⟩ with h' | h'
    · exact hwy h'
    · exact h'.2 hwY

/-- Relatives (upper.md §6.3): with `X` fixed, every 5-subset `T` of `X ∩ S` is `X ∩ Z` for a
good pair `(X, Z)` (replaces the K(9,4) connectivity check by a swap induction). -/
theorem good_reach (hU : AllUniform H) {S X T : Finset V} (hT : T ⊆ X ∩ S) (hT5 : T.card = 5) :
    ∀ k : ℕ, ∀ Y, Good H S X Y → ((X ∩ Y) \ T).card = k → ∃ Z, Good H S X Z ∧ X ∩ Z = T := by
  intro k
  induction k with
  | zero =>
    intro Y hY hk
    refine ⟨Y, hY, ?_⟩
    have hsub : X ∩ Y ⊆ T := by
      intro w hw
      by_contra hwT
      have : w ∈ (X ∩ Y) \ T := mem_sdiff.2 ⟨hw, hwT⟩
      rw [card_eq_zero] at hk
      rw [hk] at this
      exact Finset.notMem_empty w this
    exact eq_of_subset_of_card_le hsub (by rw [hT5, hY.2.2.1])
  | succ k ih =>
    intro Y hY hk
    obtain ⟨y, hy⟩ : ((X ∩ Y) \ T).Nonempty := card_pos.1 (by omega)
    have h1 := card_sdiff_add_card_inter T (X ∩ Y)
    have h2 := card_sdiff_add_card_inter (X ∩ Y) T
    rw [inter_comm (X ∩ Y) T, hY.2.2.1] at h2
    obtain ⟨z, hz⟩ : (T \ (X ∩ Y)).Nonempty := card_pos.1 (by omega)
    obtain ⟨hzT, hzN⟩ := mem_sdiff.1 hz
    have hzXS := hT hzT
    have hzY : z ∉ Y := fun hzY => hzN (mem_inter.2 ⟨(mem_inter.1 hzXS).1, hzY⟩)
    obtain ⟨hyN, hyT⟩ := mem_sdiff.1 hy
    obtain ⟨Z, hZ, hXZ⟩ := good_swap hC hU hY hyN hzXS hzY
    apply ih Z hZ
    have e : (X ∩ Z) \ T = ((X ∩ Y) \ T).erase y := by
      rw [hXZ]
      ext w
      simp only [mem_sdiff, mem_insert, mem_erase]
      constructor
      · rintro ⟨rfl | ⟨hwy, hwN⟩, hwT⟩
        · exact absurd hzT hwT
        · exact ⟨hwy, hwN, hwT⟩
      · rintro ⟨hwy, hwN, hwT⟩
        exact ⟨Or.inr ⟨hwy, hwN⟩, hwT⟩
    rw [e, card_erase_of_mem hy, hk]
    rfl

/-- Relatives: for a good pair `(X,Y)` and every 4-set `C ⊆ X ∩ S` there is an edge `U` in a good
pair with `U ∩ S = S ∖ C` and `U ∩ X ⊆ S`. -/
theorem good_relative (hU : AllUniform H) {S X Y C : Finset V} (h : Good H S X Y)
    (hCs : C ⊆ X ∩ S) (hC4 : C.card = 4) :
    ∃ U ∈ H, (∃ W, Good H S U W) ∧ U ∩ S = S \ C ∧ U ∩ X ⊆ S := by
  have h9 := (good_facts hC h).2.1
  obtain ⟨t, ht⟩ : ((X ∩ S) \ C).Nonempty := by
    apply card_pos.1
    have := card_sdiff_add_card_inter (X ∩ S) C
    have := card_le_card (inter_subset_right : (X ∩ S) ∩ C ⊆ C)
    omega
  obtain ⟨htXS, htC⟩ := mem_sdiff.1 ht
  have hTs : insert t C ⊆ X ∩ S := insert_subset htXS hCs
  have hT5 : (insert t C).card = 5 := by rw [card_insert_of_notMem htC, hC4]
  obtain ⟨Z, hZ, hXZ⟩ := good_reach hC hU hTs hT5 _ Y h rfl
  have htN : t ∈ X ∩ Z := by rw [hXZ]; exact mem_insert_self t C
  obtain ⟨U, hUH, hUt⟩ := R2 hC hZ.1 hZ.2.1 hZ.2.2.1 htN
  have hE := hZ.2.2.2.2 U hUH t hUt
  rw [hXZ, erase_insert htC] at hE
  obtain ⟨hgU, -⟩ := good_step hC hU hZ hUH hUt
  have hSXZ := (good_facts hC hZ).1
  have pt : ∀ w, (w ∈ U ∧ (w ∈ X ∨ w ∈ Z)) ↔ (w ∈ S ∧ w ∉ C) := by
    intro w
    have := Finset.ext_iff.1 hE w
    simp only [mem_inter, mem_union, mem_sdiff] at this
    exact this
  refine ⟨U, hUH, ⟨X, good_symm hgU⟩, ?_, ?_⟩
  · ext w
    simp only [mem_inter, mem_sdiff]
    constructor
    · rintro ⟨hwU, hwS⟩
      exact (pt w).1 ⟨hwU, mem_union.1 (hSXZ hwS)⟩
    · rintro ⟨hwS, hwC⟩
      exact ⟨((pt w).2 ⟨hwS, hwC⟩).1, hwS⟩
  · intro w hw
    rw [mem_inter] at hw
    exact ((pt w).1 ⟨hw.1, Or.inl hw.2⟩).1

/-- Lemma H (upper.md §6.3). -/
theorem good_H (hU : AllUniform H) {S X Y X' : Finset V} (h : Good H S X Y) (hX' : X' ∈ H)
    (hS13 : S.card = 13) (hnot : ¬ (X ∩ S ⊆ X')) :
    (X' ∩ S).card + (X' ∩ (X \ S)).card ≤ 9 := by
  obtain ⟨-, h9, h12⟩ := good_facts hC h
  have hX := h.1
  obtain ⟨t, htXS, htX'⟩ := not_subset.1 hnot
  have h8 : ((X ∩ S).erase t).card = 8 := by rw [card_erase_of_mem htXS, h9]
  obtain ⟨CU, hCU, hCU4⟩ := exists_subset_card_eq (show 4 ≤ ((X ∩ S).erase t).card by omega)
  have hCV4 : (((X ∩ S).erase t) \ CU).card = 4 := by
    have := card_sdiff_add_card_inter ((X ∩ S).erase t) CU
    rw [inter_eq_right.2 hCU] at this
    omega
  set CV := ((X ∩ S).erase t) \ CU with hCV
  have hCUs : CU ⊆ X ∩ S := hCU.trans (erase_subset _ _)
  have hCVs : CV ⊆ X ∩ S := sdiff_subset.trans (erase_subset _ _)
  obtain ⟨U, hUH, ⟨WU, hgU⟩, hUS, hUX⟩ := good_relative hC hU h hCUs hCU4
  obtain ⟨V', hVH, ⟨WV, hgV⟩, hVS, hVX⟩ := good_relative hC hU h hCVs hCV4
  have hU12 := (good_facts hC hgU).2.2
  have hV12 := (good_facts hC hgV).2.2
  have hL := L4 hC hX hX' hUH hVH (fun w hwX hwX' hwU hwV => by
    have hwS : w ∈ S := hUX (mem_inter.2 ⟨hwU, hwX⟩)
    have hwU' : w ∈ S \ CU := by rw [← hUS]; exact mem_inter.2 ⟨hwU, hwS⟩
    have hwV' : w ∈ S \ CV := by rw [← hVS]; exact mem_inter.2 ⟨hwV, hwS⟩
    by_cases hwt : w = t
    · exact htX' (hwt ▸ hwX')
    · have hwE : w ∈ (X ∩ S).erase t := mem_erase.2 ⟨hwt, mem_inter.2 ⟨hwX, hwS⟩⟩
      apply (mem_sdiff.1 hwV').2
      rw [hCV]
      exact mem_sdiff.2 ⟨hwE, (mem_sdiff.1 hwU').2⟩)
  -- upper bound on the union
  have hsub : X ∪ X' ∪ U ∪ V' ⊆ S ∪ (X \ S) ∪ (U \ S) ∪ (V' \ S) ∪ (X' \ (S ∪ X)) := by
    intro w hw
    simp only [mem_union, mem_sdiff] at hw ⊢
    by_cases hwS : w ∈ S
    · tauto
    · by_cases hwX : w ∈ X
      · tauto
      · tauto
  have c1 := card_le_card hsub
  have c2 := card_union_le (S ∪ (X \ S) ∪ (U \ S) ∪ (V' \ S)) (X' \ (S ∪ X))
  have c3 := card_union_le (S ∪ (X \ S) ∪ (U \ S)) (V' \ S)
  have c4 := card_union_le (S ∪ (X \ S)) (U \ S)
  have c5 := card_union_le S (X \ S)
  have hx1 := card_sdiff_add_card_inter X' (S ∪ X)
  have e : X' ∩ (S ∪ X) = (X' ∩ S) ∪ (X' ∩ (X \ S)) := by
    ext w; simp only [mem_inter, mem_union, mem_sdiff]; tauto
  have hd : Disjoint (X' ∩ S) (X' ∩ (X \ S)) := by
    rw [Finset.disjoint_left]; intro w h1 h2
    exact (mem_sdiff.1 (mem_inter.1 h2).2).2 (mem_inter.1 h1).2
  rw [e, card_union_of_disjoint hd, hC.unif X' hX'] at hx1
  omega

/-- Closure: from one good edge, every `S ∖ D` (`D ⊆ S` a 4-set) is `W ∩ S` for a good edge `W`
(two relative steps; replaces the 715-set closure computation). -/
theorem good_all (hU : AllUniform H) {S X Y D : Finset V} (h : Good H S X Y)
    (_hS13 : S.card = 13) (hD : D ⊆ S) (hD4 : D.card = 4) :
    ∃ W ∈ H, (∃ W', Good H S W W') ∧ W ∩ S = S \ D := by
  have h9 := (good_facts hC h).2.1
  obtain ⟨D', hD', hD'4⟩ := exists_subset_card_eq (show 4 ≤ ((X ∩ S) \ D).card by
    have := card_sdiff_add_card_inter (X ∩ S) D
    have := card_le_card (inter_subset_right : (X ∩ S) ∩ D ⊆ D)
    omega)
  obtain ⟨U, hUH, ⟨U', hgU⟩, hUS, -⟩ := good_relative hC hU h (hD'.trans sdiff_subset) hD'4
  have hDU : D ⊆ U ∩ S := by
    rw [hUS]
    intro w hw
    refine mem_sdiff.2 ⟨hD hw, fun hw' => ?_⟩
    exact (mem_sdiff.1 (hD' hw')).2 hw
  obtain ⟨W, hWH, hgW, hWS, -⟩ := good_relative hC hU hgU hDU hD4
  exact ⟨W, hWH, hgW, hWS⟩

/-- The base: a 5-pair `(a, b)` and the 13-set `S = M ∪ A0 ∪ C0` make `(a, b)` good. -/
theorem good_base (hU : AllUniform H) :
    ∃ S a b : Finset V, Good H S a b ∧ S.card = 13 := by
  obtain ⟨a, ha, b, hb, -, h5⟩ := lemmaA hC
  obtain ⟨x, hx⟩ : (a ∩ b).Nonempty := card_pos.1 (by omega)
  obtain ⟨F0, hF0, hF0x⟩ := R2 hC ha hb h5 hx
  refine ⟨(a ∩ b) ∪ (F0 ∩ (a \ b)) ∪ (F0 ∩ (b \ a)), a, b, ⟨ha, hb, h5, ?_, ?_⟩, ?_⟩
  · intro w hw; exact mem_union_left _ (mem_union_left _ hw)
  · intro F hF y hFy
    obtain ⟨e1, e2⟩ := hU a ha b hb h5 F hF F0 hF0 y x hFy hF0x
    have q3 : ∀ w, (w ∈ F ∧ w ∈ a ∧ w ∈ b) ↔ w = y := by
      intro w
      have := Finset.ext_iff.1 hFy w
      simp only [mem_inter, mem_singleton] at this
      exact this
    ext w
    have q1 := Finset.ext_iff.1 e1 w
    have q2 := Finset.ext_iff.1 e2 w
    simp only [mem_inter, mem_sdiff] at q1 q2
    simp only [mem_inter, mem_union, mem_sdiff, mem_erase]
    by_cases hwy : w = y
    · subst hwy
      have hy := (q3 w).2 rfl
      simp only [hy.1, hy.2.1, hy.2.2, true_and, true_or, ne_eq, not_true_eq_false, false_and,
        not_false_eq_true, or_true]
    · have q3' : ¬ (w ∈ F ∧ w ∈ a ∧ w ∈ b) := fun h => hwy ((q3 w).1 h)
      constructor
      · rintro ⟨hwF, hwab⟩
        refine ⟨?_, fun h => q3' ⟨hwF, h.2.1, h.2.2⟩⟩
        by_cases hwa : w ∈ a <;> by_cases hwb : w ∈ b
        · exact absurd ⟨hwF, hwa, hwb⟩ q3'
        · exact Or.inl (Or.inr (q1.1 ⟨hwF, hwa, hwb⟩))
        · exact Or.inr (q2.1 ⟨hwF, hwb, hwa⟩)
        · exact absurd hwab (by tauto)
      · rintro ⟨hwS, hno⟩
        rcases hwS with (⟨hwa, hwb⟩ | ⟨hwF0, hwa, hwb⟩) | ⟨hwF0, hwb, hwa⟩
        · exact absurd ⟨hwy, hwa, hwb⟩ hno
        · exact ⟨(q1.2 ⟨hwF0, hwa, hwb⟩).1, Or.inl hwa⟩
        · exact ⟨(q2.2 ⟨hwF0, hwb, hwa⟩).1, Or.inr hwb⟩
  · obtain ⟨hFa, hFb, -⟩ := single_card hC ha hb hF0 h5 hF0x
    have l1 := card_split_left F0 a b
    have r1 := card_split_right F0 a b
    rw [hF0x, card_singleton] at l1 r1
    have d1 : Disjoint (a ∩ b) (F0 ∩ (a \ b)) := by
      rw [Finset.disjoint_left]; intro w h1 h2
      exact (mem_sdiff.1 (mem_inter.1 h2).2).2 (mem_inter.1 h1).2
    have d2 : Disjoint ((a ∩ b) ∪ (F0 ∩ (a \ b))) (F0 ∩ (b \ a)) := by
      rw [Finset.disjoint_left]; intro w h1 h2
      have hwa : w ∉ a := (mem_sdiff.1 (mem_inter.1 h2).2).2
      rcases mem_union.1 h1 with h1 | h1
      · exact hwa (mem_inter.1 h1).1
      · exact hwa (mem_sdiff.1 (mem_inter.1 h1).2).1
    rw [card_union_of_disjoint d2, card_union_of_disjoint d1, h5]
    omega

set_option maxHeartbeats 1000000 in
/-- **Theorem W6-U** (upper.md §6.3): Case U is impossible. -/
theorem W6U (hU : AllUniform H) : False := by
  obtain ⟨S, a, b, hg, hS13⟩ := good_base hC hU
  -- a point s0 and a partition of S ∖ {s0} into four triples
  obtain ⟨s0, hs0⟩ : S.Nonempty := card_pos.1 (by omega)
  have hS1 : (S.erase s0).card = 12 := by rw [card_erase_of_mem hs0, hS13]
  obtain ⟨R1, hR1, hR1c⟩ := exists_subset_card_eq (show 3 ≤ (S.erase s0).card by omega)
  have hS2 : ((S.erase s0) \ R1).card = 9 := by
    have := card_sdiff_add_card_inter (S.erase s0) R1
    rw [inter_eq_right.2 hR1] at this; omega
  obtain ⟨R2', hR2, hR2c⟩ := exists_subset_card_eq (show 3 ≤ ((S.erase s0) \ R1).card by omega)
  have hS3 : (((S.erase s0) \ R1) \ R2').card = 6 := by
    have := card_sdiff_add_card_inter ((S.erase s0) \ R1) R2'
    rw [inter_eq_right.2 hR2] at this; omega
  obtain ⟨R3', hR3, hR3c⟩ :=
    exists_subset_card_eq (show 3 ≤ (((S.erase s0) \ R1) \ R2').card by omega)
  have hR4c : ((((S.erase s0) \ R1) \ R2') \ R3').card = 3 := by
    have := card_sdiff_add_card_inter (((S.erase s0) \ R1) \ R2') R3'
    rw [inter_eq_right.2 hR3] at this; omega
  set R4 := (((S.erase s0) \ R1) \ R2') \ R3' with hR4
  -- membership facts
  have m1 : ∀ w ∈ R1, w ∈ S ∧ w ≠ s0 := fun w hw => by
    have := mem_erase.1 (hR1 hw); exact ⟨this.2, this.1⟩
  have m2 : ∀ w ∈ R2', w ∈ S ∧ w ≠ s0 ∧ w ∉ R1 := fun w hw => by
    have h := mem_sdiff.1 (hR2 hw); have := mem_erase.1 h.1; exact ⟨this.2, this.1, h.2⟩
  have m4 : ∀ w ∈ R4, w ∈ S ∧ w ≠ s0 ∧ w ∉ R1 ∧ w ∉ R2' ∧ w ∉ R3' := fun w hw => by
    rw [hR4] at hw
    have h3 := mem_sdiff.1 hw; have h2 := mem_sdiff.1 h3.1; have h1 := mem_sdiff.1 h2.1
    have := mem_erase.1 h1.1
    exact ⟨this.2, this.1, h1.2, h2.2, h3.2⟩
  have cover : ∀ w ∈ S, w = s0 ∨ w ∈ R1 ∨ w ∈ R2' ∨ w ∈ R3' ∨ w ∈ R4 := by
    intro w hw
    by_cases h0 : w = s0
    · exact Or.inl h0
    by_cases h1 : w ∈ R1
    · exact Or.inr (Or.inl h1)
    by_cases h2 : w ∈ R2'
    · exact Or.inr (Or.inr (Or.inl h2))
    by_cases h3 : w ∈ R3'
    · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    rw [hR4]
    exact mem_sdiff.2 ⟨mem_sdiff.2 ⟨mem_sdiff.2 ⟨mem_erase.2 ⟨h0, hw⟩, h1⟩, h2⟩, h3⟩
  have hR3S : R3' ⊆ S := fun w hw =>
    (mem_erase.1 (mem_sdiff.1 (mem_sdiff.1 (hR3 hw)).1).1).2
  have hR3n : ∀ w ∈ R3', w ≠ s0 := fun w hw =>
    (mem_erase.1 (mem_sdiff.1 (mem_sdiff.1 (hR3 hw)).1).1).1
  -- the four 4-sets D_i = {s0} ∪ R_i and their edges
  have hD : ∀ R : Finset V, R ⊆ S → R.card = 3 → (∀ w ∈ R, w ≠ s0) →
      ∃ W ∈ H, (∃ W', Good H S W W') ∧ W ∩ S = S \ insert s0 R := by
    intro R hRS hR3c' hRn
    have h4 : (insert s0 R).card = 4 := by
      rw [card_insert_of_notMem (fun h => hRn s0 h rfl), hR3c']
    exact good_all hC hU hg hS13 (insert_subset hs0 hRS) h4
  obtain ⟨W1, hW1, ⟨W1', hg1⟩, hW1S⟩ :=
    hD R1 (fun w hw => (m1 w hw).1) hR1c (fun w hw => (m1 w hw).2)
  obtain ⟨W2, hW2, ⟨W2', hg2⟩, hW2S⟩ :=
    hD R2' (fun w hw => (m2 w hw).1) hR2c (fun w hw => (m2 w hw).2.1)
  obtain ⟨W3, hW3, ⟨W3', hg3⟩, hW3S⟩ := hD R3' hR3S hR3c hR3n
  obtain ⟨W4, hW4, ⟨W4', hg4⟩, hW4S⟩ :=
    hD R4 (fun w hw => (m4 w hw).1) hR4c (fun w hw => (m4 w hw).2.1)
  have hW1_12 := (good_facts hC hg1).2.2
  -- Lemma H for the pair (W1, W2): the outside part of W1 misses W2
  obtain ⟨r, hr⟩ : R2'.Nonempty := card_pos.1 (by omega)
  have hnot : ¬ (W1 ∩ S ⊆ W2) := by
    intro hsub
    have hrS := (m2 r hr).1
    have hr1 : r ∈ W1 ∩ S := by
      rw [hW1S, mem_sdiff, mem_insert]
      exact ⟨hrS, by rintro (h | h); exact (m2 r hr).2.1 h; exact (m2 r hr).2.2 h⟩
    have hr2 : r ∈ W2 ∩ S := mem_inter.2 ⟨hsub hr1, hrS⟩
    rw [hW2S, mem_sdiff] at hr2
    exact hr2.2 (mem_insert_of_mem hr)
  have hHH := good_H hC hU hg1 hW2 hS13 hnot
  have hW2S9 : (W2 ∩ S).card = 9 := by
    rw [hW2S]
    have := card_sdiff_add_card_inter S (insert s0 R2')
    rw [inter_eq_right.2 (insert_subset hs0 (fun w hw => (m2 w hw).1)),
      card_insert_of_notMem (fun h => (m2 s0 h).2.1 rfl), hR2c] at this
    omega
  have hout : W2 ∩ (W1 \ S) = ∅ := by
    rw [← card_eq_zero]; omega
  -- the four edges have no common point
  have hL := L4 hC hW1 hW2 hW3 hW4 (fun w h1 h2 h3 h4 => by
    by_cases hwS : w ∈ S
    · have e1 : w ∈ S \ insert s0 R1 := by rw [← hW1S]; exact mem_inter.2 ⟨h1, hwS⟩
      have e2 : w ∈ S \ insert s0 R2' := by rw [← hW2S]; exact mem_inter.2 ⟨h2, hwS⟩
      have e3 : w ∈ S \ insert s0 R3' := by rw [← hW3S]; exact mem_inter.2 ⟨h3, hwS⟩
      have e4 : w ∈ S \ insert s0 R4 := by rw [← hW4S]; exact mem_inter.2 ⟨h4, hwS⟩
      simp only [mem_sdiff, mem_insert, not_or] at e1 e2 e3 e4
      rcases cover w hwS with h | h | h | h | h
      · exact e1.2.1 h
      · exact e1.2.2 h
      · exact e2.2.2 h
      · exact e3.2.2 h
      · exact e4.2.2 h
    · have : w ∈ W2 ∩ (W1 \ S) := mem_inter.2 ⟨h2, mem_sdiff.2 ⟨h1, hwS⟩⟩
      rw [hout] at this
      exact Finset.notMem_empty w this)
  -- but their union has at most 12 + 4·12 = 60 points
  have hpart : ∀ W : Finset V, ∀ R : Finset V, W ∩ S = S \ insert s0 R → W ∩ S ⊆ S.erase s0 := by
    intro W R hWS
    rw [hWS]; intro w hw
    simp only [mem_sdiff, mem_insert, not_or] at hw
    exact mem_erase.2 ⟨hw.2.1, hw.1⟩
  have p1 := hpart W1 R1 hW1S
  have p2 := hpart W2 R2' hW2S
  have p3 := hpart W3 R3' hW3S
  have p4 := hpart W4 R4 hW4S
  have hsub : W1 ∪ W2 ∪ W3 ∪ W4 ⊆
      S.erase s0 ∪ (W1 \ S) ∪ (W2 \ S) ∪ (W3 \ S) ∪ (W4 \ S) := by
    intro w hw
    have k1 : w ∈ W1 ∧ w ∈ S → w ∈ S.erase s0 := fun h => p1 (mem_inter.2 h)
    have k2 : w ∈ W2 ∧ w ∈ S → w ∈ S.erase s0 := fun h => p2 (mem_inter.2 h)
    have k3 : w ∈ W3 ∧ w ∈ S → w ∈ S.erase s0 := fun h => p3 (mem_inter.2 h)
    have k4 : w ∈ W4 ∧ w ∈ S → w ∈ S.erase s0 := fun h => p4 (mem_inter.2 h)
    simp only [mem_union, mem_sdiff] at hw ⊢
    by_cases hwS : w ∈ S
    · rcases hw with ((h | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl (Or.inl (k1 ⟨h, hwS⟩))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (k2 ⟨h, hwS⟩))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (k3 ⟨h, hwS⟩))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (k4 ⟨h, hwS⟩))))
    · rcases hw with ((h | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨h, hwS⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨h, hwS⟩))
      · exact Or.inl (Or.inr ⟨h, hwS⟩)
      · exact Or.inr ⟨h, hwS⟩
  have c0 := card_le_card hsub
  have c1 := card_union_le (S.erase s0 ∪ (W1 \ S) ∪ (W2 \ S) ∪ (W3 \ S)) (W4 \ S)
  have c2 := card_union_le (S.erase s0 ∪ (W1 \ S) ∪ (W2 \ S)) (W3 \ S)
  have c3 := card_union_le (S.erase s0 ∪ (W1 \ S)) (W2 \ S)
  have c4 := card_union_le (S.erase s0) (W1 \ S)
  have o2 := (good_facts hC hg2).2.2
  have o3 := (good_facts hC hg3).2.2
  have o4 := (good_facts hC hg4).2.2
  omega

end W6U

/-! ## The Case-N split (n4-referee steps 1–5) -/

section Split
variable {V : Type*} [DecidableEq V] {H : Finset (Finset V)} (hC : Counter H)
include hC

/-- Class (4,4) forces equal parts. -/
theorem parts_eq_of_44 {X Y F F' : Finset V} (hX : X ∈ H) (hY : Y ∈ H) (hF : F ∈ H)
    (hF' : F' ∈ H) (h5 : (X ∩ Y).card = 5) {x y : V} (hx : F ∩ (X ∩ Y) = {x})
    (hy : F' ∩ (X ∩ Y) = {y}) (ha : (F ∩ F' ∩ (X \ Y)).card = 4)
    (hc : (F ∩ F' ∩ (Y \ X)).card = 4) :
    F ∩ (X \ Y) = F' ∩ (X \ Y) ∧ F ∩ (Y \ X) = F' ∩ (Y \ X) := by
  obtain ⟨hFX, hFY, -⟩ := single_card hC hX hY hF h5 hx
  obtain ⟨hF'X, hF'Y, -⟩ := single_card hC hX hY hF' h5 hy
  have l1 := card_split_left F X Y
  have l2 := card_split_left F' X Y
  have r1 := card_split_right F X Y
  have r2 := card_split_right F' X Y
  rw [hx, card_singleton] at l1 r1
  rw [hy, card_singleton] at l2 r2
  have s1 : F ∩ F' ∩ (X \ Y) ⊆ F ∩ (X \ Y) := by
    intro z hz; simp only [mem_inter] at hz ⊢; exact ⟨hz.1.1, hz.2⟩
  have s2 : F ∩ F' ∩ (X \ Y) ⊆ F' ∩ (X \ Y) := by
    intro z hz; simp only [mem_inter] at hz ⊢; exact ⟨hz.1.2, hz.2⟩
  have s3 : F ∩ F' ∩ (Y \ X) ⊆ F ∩ (Y \ X) := by
    intro z hz; simp only [mem_inter] at hz ⊢; exact ⟨hz.1.1, hz.2⟩
  have s4 : F ∩ F' ∩ (Y \ X) ⊆ F' ∩ (Y \ X) := by
    intro z hz; simp only [mem_inter] at hz ⊢; exact ⟨hz.1.2, hz.2⟩
  have e1 := eq_of_subset_of_card_le s1 (by omega)
  have e2 := eq_of_subset_of_card_le s2 (by omega)
  have e3 := eq_of_subset_of_card_le s3 (by omega)
  have e4 := eq_of_subset_of_card_le s4 (by omega)
  exact ⟨e1.symm.trans e2, e3.symm.trans e4⟩

/-- Step 1/4 of the referee tree: a non-uniform 5-pair has a cross pair of class ≠ (4,4). -/
theorem nonuniform_cross (hU : ¬ AllUniform H) :
    ∃ X Y G G' : Finset V, CrossPair H X Y G G' ∧
      ¬ ((G ∩ G' ∩ (X \ Y)).card = 4 ∧ (G ∩ G' ∩ (Y \ X)).card = 4) := by
  by_contra hno
  push Not at hno
  apply hU
  intro X hX Y hY h5 F hF F' hF' x y hx hy
  have hxN : x ∈ X ∩ Y := by
    have : x ∈ F ∩ (X ∩ Y) := by rw [hx]; exact mem_singleton_self x
    exact (mem_inter.1 this).2
  by_cases hxy : x = y
  · subst hxy
    obtain ⟨z, hz⟩ : ((X ∩ Y).erase x).Nonempty := card_pos.1 (by rw [card_erase_of_mem hxN]; omega)
    obtain ⟨hzx, hzN⟩ := mem_erase.1 hz
    obtain ⟨G, hG, hGz⟩ := R2 hC hX hY h5 hzN
    have c1 : CrossPair H X Y F G := ⟨hX, hY, hF, hG, h5, x, z, fun h => hzx h.symm, hx, hGz⟩
    have c2 : CrossPair H X Y F' G := ⟨hX, hY, hF', hG, h5, x, z, fun h => hzx h.symm, hy, hGz⟩
    obtain ⟨a1, b1⟩ := hno X Y F G c1
    obtain ⟨a2, b2⟩ := hno X Y F' G c2
    obtain ⟨e1, e2⟩ := parts_eq_of_44 hC hX hY hF hG h5 hx hGz a1 b1
    obtain ⟨e3, e4⟩ := parts_eq_of_44 hC hX hY hF' hG h5 hy hGz a2 b2
    exact ⟨e1.trans e3.symm, e2.trans e4.symm⟩
  · have c : CrossPair H X Y F F' := ⟨hX, hY, hF, hF', h5, x, y, hxy, hx, hy⟩
    obtain ⟨a1, b1⟩ := hno X Y F F' c
    exact parts_eq_of_44 hC hX hY hF hF' h5 hx hy a1 b1

/-- `cross_class` for a `CrossPair`. -/
theorem crossPair_class {X Y G G' : Finset V} (h : CrossPair H X Y G G') :
    1 ≤ (G ∩ G' ∩ (X \ Y)).card ∧ (G ∩ G' ∩ (X \ Y)).card ≤ 4 ∧
    1 ≤ (G ∩ G' ∩ (Y \ X)).card ∧ (G ∩ G' ∩ (Y \ X)).card ≤ 4 ∧
    5 ≤ (G ∩ G' ∩ (X \ Y)).card + (G ∩ G' ∩ (Y \ X)).card ∧
    (G ∩ G').card = (G ∩ G' ∩ (X \ Y)).card + (G ∩ G' ∩ (Y \ X)).card := by
  obtain ⟨hX, hY, hG, hG', h5, v, w, hvw, hv, hw⟩ := h
  exact cross_class hC hX hY hG hG' h5 hv hw hvw

/-- N.4 / N8.0 step 3: a cross pair of class (3,2) is a (3,2,1,1)-K4. -/
theorem K4_of_32 {X Y G G' : Finset V} (h : CrossPair H X Y G G')
    (ha : (G ∩ G' ∩ (X \ Y)).card = 3) (hc : (G ∩ G' ∩ (Y \ X)).card = 2) : K4_3211 H := by
  have hcl := crossPair_class hC h
  obtain ⟨hX, hY, hG, hG', h5, v, w, hvw, hv, hw⟩ := h
  obtain ⟨hGX, hGY, -⟩ := single_card hC hX hY hG h5 hv
  obtain ⟨hG'X, hG'Y, -⟩ := single_card hC hX hY hG' h5 hw
  have pv : ∀ z, (z ∈ G ∧ z ∈ X ∧ z ∈ Y) ↔ z = v := by
    intro z; have := Finset.ext_iff.1 hv z; simp only [mem_inter, mem_singleton] at this
    exact this
  have pw : ∀ z, (z ∈ G' ∧ z ∈ X ∧ z ∈ Y) ↔ z = w := by
    intro z; have := Finset.ext_iff.1 hw z; simp only [mem_inter, mem_singleton] at this
    exact this
  have no4 : ∀ z, z ∈ X → z ∈ Y → z ∈ G → z ∈ G' → False := by
    intro z h1 h2 h3 h4
    exact hvw (((pv z).1 ⟨h3, h1, h2⟩).symm.trans ((pw z).1 ⟨h4, h1, h2⟩))
  refine ⟨X, hX, Y, hY, G, hG, G', hG', h5, by rw [inter_comm]; exact hGX,
    by rw [inter_comm]; exact hG'X, by rw [inter_comm]; exact hGY,
    by rw [inter_comm]; exact hG'Y, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · ext z; simp only [mem_inter, Finset.notMem_empty, iff_false]
    rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact no4 z h1 h2 h3 h4
  · have : X ∩ Y ∩ G = G ∩ (X ∩ Y) := by rw [inter_comm]
    rw [this, hv, card_singleton]
  · have : X ∩ Y ∩ G' = G' ∩ (X ∩ Y) := by rw [inter_comm]
    rw [this, hw, card_singleton]
  · have : X ∩ G ∩ G' = G ∩ G' ∩ (X \ Y) := by
      ext z; simp only [mem_inter, mem_sdiff]
      constructor
      · rintro ⟨⟨h1, h3⟩, h4⟩; exact ⟨⟨h3, h4⟩, h1, fun h2 => no4 z h1 h2 h3 h4⟩
      · rintro ⟨⟨h3, h4⟩, h1, -⟩; exact ⟨⟨h1, h3⟩, h4⟩
    rw [this, ha]
  · have : Y ∩ G ∩ G' = G ∩ G' ∩ (Y \ X) := by
      ext z; simp only [mem_inter, mem_sdiff]
      constructor
      · rintro ⟨⟨h2, h3⟩, h4⟩; exact ⟨⟨h3, h4⟩, h2, fun h1 => no4 z h1 h2 h3 h4⟩
      · rintro ⟨⟨h3, h4⟩, h2, -⟩; exact ⟨⟨h2, h3⟩, h4⟩
    rw [this, hc]

/-- Step 3 (NK dichotomy): under W7-I, a failure of NK yields a (3,2,1,1)-K4
((2,3) via the E1↔E2 swap). -/
theorem K4_of_not_NK (hW : W7I_prop H) (hNK : ¬ NK_prop H) : K4_3211 H := by
  unfold NK_prop at hNK
  push Not at hNK
  obtain ⟨X, Y, G, G', h, h5⟩ := hNK
  obtain ⟨a1, a4, c1, c4, -, hsum⟩ := crossPair_class hC h
  obtain ⟨na, nc⟩ := hW X Y G G' h
  rcases (by omega : ((G ∩ G' ∩ (X \ Y)).card = 3 ∧ (G ∩ G' ∩ (Y \ X)).card = 2) ∨
      ((G ∩ G' ∩ (X \ Y)).card = 2 ∧ (G ∩ G' ∩ (Y \ X)).card = 3)) with ⟨ha, hc⟩ | ⟨ha, hc⟩
  · exact K4_of_32 hC h ha hc
  · exact K4_of_32 hC (crossPair_swap h) hc ha

end Split

/-! ## Assembly: t(21) = 4 from the leaves -/

/-- Every counterexample on `Fin n` is excluded, given the five leaves. -/
theorem noCounter_of_leaves (hW7 : W7I_leaf) (hK4 : NK4_leaf) (h24 : noK4_24_leaf)
    (h33 : noK4_33_leaf) (h34 : noK4_34_leaf) (n : ℕ) (H : Finset (Finset (Fin n))) :
    ¬ Counter H := by
  intro hC
  have hW := hW7 n H hC
  -- Case U (W6-U)
  by_cases hU : AllUniform H
  · exact W6U hC hU
  obtain ⟨X, Y, G, G', hcp, hn44⟩ := nonuniform_cross hC hU
  -- NK holds everywhere, else N-K4 (G14 leaf)
  have hNK : NK_prop H := by
    by_contra hNK
    exact hK4 n H hC hW (K4_of_not_NK hC hW hNK)
  -- the (2,4) leaf gives N24 at every pair (with the swap for (4,2))
  have hN24 : N24_prop H := by
    intro X Y G G' h
    refine ⟨h24 n H hC hW hNK X Y G G' h, fun ⟨ha, hc⟩ => ?_⟩
    exact h24 n H hC hW hNK Y X G G' (crossPair_swap h) ⟨hc, ha⟩
  obtain ⟨a1, a4, c1, c4, hs, hsum⟩ := crossPair_class hC hcp
  obtain ⟨na, nc⟩ := hW X Y G G' hcp
  have h5 := hNK X Y G G' hcp
  have hN := hN24 X Y G G' hcp
  rcases (by omega : ((G ∩ G' ∩ (X \ Y)).card = 2 ∧ (G ∩ G' ∩ (Y \ X)).card = 4) ∨
      ((G ∩ G' ∩ (X \ Y)).card = 4 ∧ (G ∩ G' ∩ (Y \ X)).card = 2) ∨
      ((G ∩ G' ∩ (X \ Y)).card = 3 ∧ (G ∩ G' ∩ (Y \ X)).card = 3) ∨
      ((G ∩ G' ∩ (X \ Y)).card = 3 ∧ (G ∩ G' ∩ (Y \ X)).card = 4) ∨
      ((G ∩ G' ∩ (X \ Y)).card = 4 ∧ (G ∩ G' ∩ (Y \ X)).card = 3)) with
    h | h | h | h | ⟨ha, hc⟩
  · exact hN.1 h
  · exact hN.2 h
  · exact h33 n H hC hW hNK hN24 X Y G G' hcp h
  · exact h34 n H hC hW hNK hN24 X Y G G' hcp h
  · exact h34 n H hC hW hNK hN24 Y X G G' (crossPair_swap hcp) ⟨hc, ha⟩

/-- **t(21) = 4** (the formal-conjectures statement at r = 21), from the five leaf hypotheses. -/
theorem erdos_616_r21_of_leaves (hW7 : W7I_leaf) (hK4 : NK4_leaf) (h24 : noK4_24_leaf)
    (h33 : noK4_33_leaf) (h34 : noK4_34_leaf) :
    Hypergraph.localTransversalBound 21 (3 * 21 - 3) 1 = 4 :=
  erdos_616_r21_iff.2 (noCounter_of_leaves hW7 hK4 h24 h33 h34)

/-! ## Lemma KB (pool bound, upper.md X.2) -/

section KB
variable {V : Type*} [DecidableEq V]

/-- The shared outside points of a slot list: points outside the base `B` lying in ≥ 2 slots. -/
def sharedPts {ι : Type*} (slots : Finset ι) (F : ι → Finset V) (B : Finset V) : Finset V :=
  ((slots.biUnion F) \ B).filter (fun u => 2 ≤ (slots.filter (fun s => u ∈ F s)).card)

/-- **Lemma KB.** If every slot is a 21-set and `ν s ≤ |F s ∩ B|`, then
`2 · |Sh| ≤ Σ_s (21 − ν s)`. -/
theorem KB {ι : Type*} [DecidableEq ι] (slots : Finset ι) (F : ι → Finset V) (B : Finset V)
    (ν : ι → ℕ) (hcard : ∀ s ∈ slots, (F s).card = 21) (hν : ∀ s ∈ slots, ν s ≤ (F s ∩ B).card) :
    2 * (sharedPts slots F B).card ≤ ∑ s ∈ slots, (21 - ν s) := by
  set U := (slots.biUnion F) \ B with hU
  have step1 : ∀ s ∈ slots, (F s \ B).card = ∑ u ∈ U, if u ∈ F s then 1 else 0 := by
    intro s hs
    rw [← card_filter]
    congr 1
    ext u
    simp only [mem_filter, hU, mem_sdiff, mem_biUnion]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨⟨s, hs, h1⟩, h2⟩, h1⟩
    · rintro ⟨⟨-, h2⟩, h1⟩; exact ⟨h1, h2⟩
  have step2 : ∑ s ∈ slots, (F s \ B).card =
      ∑ u ∈ U, (slots.filter (fun s => u ∈ F s)).card := by
    rw [sum_congr rfl step1, sum_comm]
    refine sum_congr rfl fun u _ => ?_
    rw [card_filter]
  have step3 : ∑ u ∈ sharedPts slots F B, 2 ≤
      ∑ u ∈ U, (slots.filter (fun s => u ∈ F s)).card := by
    calc ∑ u ∈ sharedPts slots F B, 2
        ≤ ∑ u ∈ sharedPts slots F B, (slots.filter (fun s => u ∈ F s)).card := by
          apply sum_le_sum
          intro u hu
          exact (mem_filter.1 hu).2
      _ ≤ ∑ u ∈ U, (slots.filter (fun s => u ∈ F s)).card := by
          apply sum_le_sum_of_subset
          exact filter_subset _ _
  have step4 : ∑ s ∈ slots, (F s \ B).card ≤ ∑ s ∈ slots, (21 - ν s) := by
    apply sum_le_sum
    intro s hs
    have := card_sdiff_add_card_inter (F s) B
    have := hν s hs
    have := hcard s hs
    omega
  rw [sum_const, smul_eq_mul] at step3
  rw [mul_comm]
  omega

omit [DecidableEq V] in
/-- The injection of the shared points into a pool of `K ≥ |Sh|` points (X.2, "Use in the
encoding"). -/
theorem KB_pool (Sh : Finset V) (K : ℕ) (hK : Sh.card ≤ K) :
    ∃ f : Sh → Fin K, Function.Injective f :=
  ⟨Fin.castLE hK ∘ Sh.equivFin, (Fin.castLE_injective hK).comp Sh.equivFin.injective⟩

/-- `ν = 9` for a single of a 5-pair (R.3): `|F ∩ (a ∪ b)| = 9`. -/
theorem nu_single {H : Finset (Finset V)} (hC : Counter H) {a b F : Finset V} (ha : a ∈ H)
    (hb : b ∈ H) (hF : F ∈ H) (hM : (a ∩ b).card = 5) {x : V} (hx : F ∩ (a ∩ b) = {x}) :
    (F ∩ (a ∪ b)).card = 9 := by
  obtain ⟨h1, h2, -⟩ := single_card hC ha hb hF hM hx
  have s := card_split F a b
  have l := card_split_left F a b
  have r := card_split_right F a b
  rw [hx, card_singleton] at s l r
  omega

/-- `ν = 5` for any slot (Lemma A). -/
theorem nu_any {H : Finset (Finset V)} (hC : Counter H) {a F : Finset V} (ha : a ∈ H)
    (hF : F ∈ H) : 5 ≤ (F ∩ a).card :=
  inter_ge5 hC hF ha

end KB

end Erdos616R21
