import Erdos616.G14.BridgePair
import Erdos616.HandA
/-!
# Erdős #616, r = 21: the N-K4 (G14) leaf, assembled

* `W7I_of_prop`: HandA's `W7I_prop` (cross-type singles never meet in exactly one point on a side) + S(a) (they meet)
  gives the bridge's `W7I` (they meet in ≥ 2 points on each side).
* `lbase_of_K4`: a (3,2,1,1)-K4 in HandA's labelling (P0..P3 = E1, E2, G, G') yields a labelled base `LBase H`
  (G14 edge order: `P 0 = E2, P 1 = E1, P 2 = G, P 3 = G'`; the 16 core points enumerated region by region).
* `NK4_leaf_of_certs`: `NK4_leaf` (HandA's statement) from the six certificate facts of the core layer.
-/
open Finset

namespace Erdos616R21
open G14B
variable {V : Type*} [DecidableEq V]

theorem W7I_of_prop {H : Finset (Finset V)} (hC : Counter H) (hW : W7I_prop H) : W7I H := by
  intro a ha b hb G hG G' hG' h5 x y hx hy hxy
  have hcp : CrossPair H a b G G' := ⟨ha, hb, hG, hG', h5, x, y, hxy, hx, hy⟩
  obtain ⟨h1, h2⟩ := hW a b G G' hcp
  obtain ⟨p, hpG, hpG', hpa, hpb⟩ := S_a_A hC ha hb hG hG' hx hy hxy
  obtain ⟨p', hpG2, hpG'2, hpb2, hpa2⟩ := S_a_C hC ha hb hG hG' hx hy hxy
  have c1 : 0 < (G ∩ G' ∩ (a \ b)).card := card_pos.2 ⟨p, by simp [hpG, hpG', hpa, hpb]⟩
  have c2 : 0 < (G ∩ G' ∩ (b \ a)).card := card_pos.2 ⟨p', by simp [hpG2, hpG'2, hpb2, hpa2]⟩
  omega

/-- exact-pair region count when the four sets have no common point -/
theorem exact_pair_card {a b c d : Finset V} (hq : ∀ x, x ∈ a → x ∈ b → x ∈ c → x ∈ d → False) :
    ((a ∩ b) \ (c ∪ d)).card + (a ∩ b ∩ c).card + (a ∩ b ∩ d).card = (a ∩ b).card := by
  have e1 := card_sdiff_eq (a ∩ b) (c ∪ d)
  have e2 : a ∩ b ∩ (c ∪ d) = (a ∩ b ∩ c) ∪ (a ∩ b ∩ d) := inter_union_distrib_left _ _ _
  have e3 := card_union_add_card_inter (a ∩ b ∩ c) (a ∩ b ∩ d)
  have e4 : (a ∩ b ∩ c) ∩ (a ∩ b ∩ d) = ∅ := by
    ext x; simp only [mem_inter, Finset.notMem_empty, iff_false]
    rintro ⟨⟨⟨h1, h2⟩, h3⟩, -, h4⟩; exact hq x h1 h2 h3 h4
  rw [e2] at e1; rw [e4, card_empty] at e3
  omega

/-- a 4-vector -/
def vec4 {α : Type*} (a0 a1 a2 a3 : α) : Fin 4 → α
  | ⟨0, _⟩ => a0 | ⟨1, _⟩ => a1 | ⟨2, _⟩ => a2 | ⟨_ + 3, _⟩ => a3

/-- a 16-vector -/
def vec16 {α : Type*} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : α) : Fin 16 → α
  | ⟨0, _⟩ => a0 | ⟨1, _⟩ => a1 | ⟨2, _⟩ => a2 | ⟨3, _⟩ => a3 | ⟨4, _⟩ => a4 | ⟨5, _⟩ => a5 | ⟨6, _⟩ => a6
  | ⟨7, _⟩ => a7 | ⟨8, _⟩ => a8 | ⟨9, _⟩ => a9 | ⟨10, _⟩ => a10 | ⟨11, _⟩ => a11 | ⟨12, _⟩ => a12
  | ⟨13, _⟩ => a13 | ⟨14, _⟩ => a14 | ⟨_ + 15, _⟩ => a15

theorem G14_col : ∀ i j : Fin 16, (∀ q : Fin 4, (G14.Pm q).testBit i = (G14.Pm q).testBit j) →
    i = j ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨ (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) ∨ (i = 4 ∧ j = 6) ∨
      (i = 6 ∧ j = 4) ∨ (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5) ∨ (i = 7 ∧ j = 8) ∨ (i = 8 ∧ j = 7) ∨
      (i = 7 ∧ j = 9) ∨ (i = 9 ∧ j = 7) ∨ (i = 8 ∧ j = 9) ∨ (i = 9 ∧ j = 8) ∨ (i = 10 ∧ j = 11) ∨
      (i = 11 ∧ j = 10) ∨ (i = 12 ∧ j = 13) ∨ (i = 13 ∧ j = 12) := by
  decide +kernel

/-- **A (3,2,1,1)-K4 yields a labelled base.** HandA labels `P0 = E1, P1 = E2, P2 = G, P3 = G'`; the G14 edge order
is `E2, E1, G, G'` (its triple sizes are `|012| = |013| = 1, |023| = 2, |123| = 3`). -/
theorem lbase_of_K4 {H : Finset (Finset V)} (hK : K4_3211 H) : Nonempty (LBase H) := by
  obtain ⟨P0, h0, P1, h1, P2, h2, P3, h3, c01, c02, c03, c12, c13, c23, hq, t012, t013, t023, t123⟩ := hK
  have quad : ∀ x, x ∈ P0 → x ∈ P1 → x ∈ P2 → x ∈ P3 → False := by
    intro x a b c d
    have : x ∈ P0 ∩ P1 ∩ P2 ∩ P3 := by simp [a, b, c, d]
    rw [hq] at this; simp at this
  -- pair regions
  have r01 := exact_pair_card (a := P0) (b := P1) (c := P2) (d := P3) quad
  have r12 := exact_pair_card (a := P1) (b := P2) (c := P0) (d := P3) (fun x a b c d => quad x c a b d)
  have r13 := exact_pair_card (a := P1) (b := P3) (c := P0) (d := P2) (fun x a b c d => quad x c a d b)
  have r02 := exact_pair_card (a := P0) (b := P2) (c := P1) (d := P3) (fun x a b c d => quad x a c b d)
  have r03 := exact_pair_card (a := P0) (b := P3) (c := P1) (d := P2) (fun x a b c d => quad x a c d b)
  have r23 := exact_pair_card (a := P2) (b := P3) (c := P0) (d := P1) (fun x a b c d => quad x c d a b)
  have e120 : P1 ∩ P2 ∩ P0 = P0 ∩ P1 ∩ P2 := by ext; simp only [mem_inter]; tauto
  have e130 : P1 ∩ P3 ∩ P0 = P0 ∩ P1 ∩ P3 := by ext; simp only [mem_inter]; tauto
  have e132 : P1 ∩ P3 ∩ P2 = P1 ∩ P2 ∩ P3 := by ext; simp only [mem_inter]; tauto
  have e021 : P0 ∩ P2 ∩ P1 = P0 ∩ P1 ∩ P2 := by ext; simp only [mem_inter]; tauto
  have e031 : P0 ∩ P3 ∩ P1 = P0 ∩ P1 ∩ P3 := by ext; simp only [mem_inter]; tauto
  have e032 : P0 ∩ P3 ∩ P2 = P0 ∩ P2 ∩ P3 := by ext; simp only [mem_inter]; tauto
  have e230 : P2 ∩ P3 ∩ P0 = P0 ∩ P2 ∩ P3 := by ext; simp only [mem_inter]; tauto
  have e231 : P2 ∩ P3 ∩ P1 = P1 ∩ P2 ∩ P3 := by ext; simp only [mem_inter]; tauto
  rw [e120] at r12; rw [e130, e132] at r13; rw [e021] at r02; rw [e031, e032] at r03; rw [e230, e231] at r23
  obtain ⟨v, hv⟩ := card_eq_one.1 t012
  obtain ⟨w, hw⟩ := card_eq_one.1 t013
  obtain ⟨al0, al1, hal, hal'⟩ := card_eq_two.1 t123
  obtain ⟨g0, g1, g2, hg01, hg02, hg12, hg⟩ := card_eq_three.1 t023
  obtain ⟨m0, m1, m2, hm01, hm02, hm12, hm⟩ := card_eq_three.1 (show ((P0 ∩ P1) \ (P2 ∪ P3)).card = 3 by omega)
  obtain ⟨a30, a31, ha3, ha3'⟩ := card_eq_two.1 (show ((P1 ∩ P2) \ (P0 ∪ P3)).card = 2 by omega)
  obtain ⟨a40, a41, ha4, ha4'⟩ := card_eq_two.1 (show ((P1 ∩ P3) \ (P0 ∪ P2)).card = 2 by omega)
  obtain ⟨c3, hc3⟩ := card_eq_one.1 (show ((P0 ∩ P2) \ (P1 ∪ P3)).card = 1 by omega)
  obtain ⟨c4, hc4⟩ := card_eq_one.1 (show ((P0 ∩ P3) \ (P1 ∪ P2)).card = 1 by omega)
  have h23 : (P2 ∩ P3) \ (P0 ∪ P1) = ∅ := card_eq_zero.1 (by omega)
  -- membership facts of the 16 points
  have mv : v ∈ P0 ∩ P1 ∩ P2 := by rw [hv]; simp
  have mw : w ∈ P0 ∩ P1 ∩ P3 := by rw [hw]; simp
  have mal0 : al0 ∈ P1 ∩ P2 ∩ P3 := by rw [hal']; simp
  have mal1 : al1 ∈ P1 ∩ P2 ∩ P3 := by rw [hal']; simp
  have mg0 : g0 ∈ P0 ∩ P2 ∩ P3 := by rw [hg]; simp
  have mg1 : g1 ∈ P0 ∩ P2 ∩ P3 := by rw [hg]; simp
  have mg2 : g2 ∈ P0 ∩ P2 ∩ P3 := by rw [hg]; simp
  have mm0 : m0 ∈ (P0 ∩ P1) \ (P2 ∪ P3) := by rw [hm]; simp
  have mm1 : m1 ∈ (P0 ∩ P1) \ (P2 ∪ P3) := by rw [hm]; simp
  have mm2 : m2 ∈ (P0 ∩ P1) \ (P2 ∪ P3) := by rw [hm]; simp
  have ma30 : a30 ∈ (P1 ∩ P2) \ (P0 ∪ P3) := by rw [ha3']; simp
  have ma31 : a31 ∈ (P1 ∩ P2) \ (P0 ∪ P3) := by rw [ha3']; simp
  have ma40 : a40 ∈ (P1 ∩ P3) \ (P0 ∪ P2) := by rw [ha4']; simp
  have ma41 : a41 ∈ (P1 ∩ P3) \ (P0 ∪ P2) := by rw [ha4']; simp
  have mc3 : c3 ∈ (P0 ∩ P2) \ (P1 ∪ P3) := by rw [hc3]; simp
  have mc4 : c4 ∈ (P0 ∩ P3) \ (P1 ∪ P2) := by rw [hc4]; simp
  simp only [mem_inter, mem_sdiff, mem_union, not_or] at mv mw mal0 mal1 mg0 mg1 mg2 mm0 mm1 mm2 ma30 ma31 ma40 ma41 mc3 mc4
  have nv : v ∉ P3 := fun h => quad v mv.1.1 mv.1.2 mv.2 h
  have nw : w ∉ P2 := fun h => quad w mw.1.1 mw.1.2 h mw.2
  have nal0 : al0 ∉ P0 := fun h => quad al0 h mal0.1.1 mal0.1.2 mal0.2
  have nal1 : al1 ∉ P0 := fun h => quad al1 h mal1.1.1 mal1.1.2 mal1.2
  have ng0 : g0 ∉ P1 := fun h => quad g0 mg0.1.1 h mg0.1.2 mg0.2
  have ng1 : g1 ∉ P1 := fun h => quad g1 mg1.1.1 h mg1.1.2 mg1.2
  have ng2 : g2 ∉ P1 := fun h => quad g2 mg2.1.1 h mg2.1.2 mg2.2
  let Q : Fin 4 → Finset V := vec4 P1 P0 P2 P3
  let c : Fin 16 → V := vec16 v w al0 al1 g0 g1 g2 m0 m1 m2 a30 a31 a40 a41 c3 c4
  have hmem : ∀ (i : Fin 16) (q : Fin 4), c i ∈ Q q ↔ (G14.Pm q).testBit i = true := by
    intro i q
    rcases i with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i, hi⟩ <;> rcases q with ⟨_ | _ | _ | _ | q, hq⟩ <;> first | omega |
      simp [c, Q, vec16, vec4, mv, mw, mal0, mal1, mg0, mg1, mg2, mm0, mm1, mm2, ma30, ma31, ma40, ma41, mc3, mc4,
        nv, nw, nal0, nal1, ng0, ng1, ng2] <;> decide
  have cover : ∀ x, ((x ∈ P0 ∧ x ∈ P1) ∨ (x ∈ P0 ∧ x ∈ P2) ∨ (x ∈ P0 ∧ x ∈ P3) ∨ (x ∈ P1 ∧ x ∈ P2) ∨
      (x ∈ P1 ∧ x ∈ P3) ∨ (x ∈ P2 ∧ x ∈ P3)) → ∃ i, c i = x := by
    intro x hx
    by_cases x0 : x ∈ P0 <;> by_cases x1 : x ∈ P1 <;> by_cases x2 : x ∈ P2 <;> by_cases x3 : x ∈ P3
    · exact (quad x x0 x1 x2 x3).elim
    · have : x ∈ P0 ∩ P1 ∩ P2 := by simp [x0, x1, x2]
      rw [hv, mem_singleton] at this; exact ⟨0, this.symm⟩
    · have : x ∈ P0 ∩ P1 ∩ P3 := by simp [x0, x1, x3]
      rw [hw, mem_singleton] at this; exact ⟨1, this.symm⟩
    · have : x ∈ (P0 ∩ P1) \ (P2 ∪ P3) := by simp [x0, x1, x2, x3]
      rw [hm] at this; simp only [mem_insert, mem_singleton] at this
      rcases this with rfl | rfl | rfl
      · exact ⟨7, rfl⟩
      · exact ⟨8, rfl⟩
      · exact ⟨9, rfl⟩
    · have : x ∈ P0 ∩ P2 ∩ P3 := by simp [x0, x2, x3]
      rw [hg] at this; simp only [mem_insert, mem_singleton] at this
      rcases this with rfl | rfl | rfl
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
      · exact ⟨6, rfl⟩
    · have : x ∈ (P0 ∩ P2) \ (P1 ∪ P3) := by simp [x0, x1, x2, x3]
      rw [hc3, mem_singleton] at this; exact ⟨14, this.symm⟩
    · have : x ∈ (P0 ∩ P3) \ (P1 ∪ P2) := by simp [x0, x1, x2, x3]
      rw [hc4, mem_singleton] at this; exact ⟨15, this.symm⟩
    · exfalso; simp_all
    · have : x ∈ P1 ∩ P2 ∩ P3 := by simp [x1, x2, x3]
      rw [hal'] at this; simp only [mem_insert, mem_singleton] at this
      rcases this with rfl | rfl
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    · have : x ∈ (P1 ∩ P2) \ (P0 ∪ P3) := by simp [x0, x1, x2, x3]
      rw [ha3'] at this; simp only [mem_insert, mem_singleton] at this
      rcases this with rfl | rfl
      · exact ⟨10, rfl⟩
      · exact ⟨11, rfl⟩
    · have : x ∈ (P1 ∩ P3) \ (P0 ∪ P2) := by simp [x0, x1, x2, x3]
      rw [ha4'] at this; simp only [mem_insert, mem_singleton] at this
      rcases this with rfl | rfl
      · exact ⟨12, rfl⟩
      · exact ⟨13, rfl⟩
    · exfalso; simp_all
    · have : x ∈ (P2 ∩ P3) \ (P0 ∪ P1) := by simp [x0, x1, x2, x3]
      rw [h23] at this; simp at this
    · exfalso; simp_all
    · exfalso; simp_all
    · exfalso; simp_all
  refine ⟨⟨Q, c, ?_, ?_, hmem, ?_⟩⟩
  · intro q; rcases q with ⟨_ | _ | _ | _ | q, hq⟩ <;> first | omega | exact h1 | exact h0 | exact h2 | exact h3
  · intro i j hij
    have hcol : ∀ q : Fin 4, (G14.Pm q).testBit i = (G14.Pm q).testBit j := by
      intro q
      have e1 := hmem i q
      have e2 := hmem j q
      rw [hij] at e1
      exact Bool.eq_iff_iff.2 ⟨fun h => e2.1 (e1.2 h), fun h => e1.1 (e2.2 h)⟩
    rcases G14_col i j hcol with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    all_goals exfalso; revert hij
    all_goals first
      | exact hal | exact fun h => hal h.symm | exact hg01 | exact fun h => hg01 h.symm | exact hg02
      | exact fun h => hg02 h.symm | exact hg12 | exact fun h => hg12 h.symm | exact hm01
      | exact fun h => hm01 h.symm | exact hm02 | exact fun h => hm02 h.symm | exact hm12
      | exact fun h => hm12 h.symm | exact ha3 | exact fun h => ha3 h.symm | exact ha4
      | exact fun h => ha4 h.symm
  · intro q q' hqq' x hx hx'
    apply cover
    rcases q with ⟨_ | _ | _ | _ | q, hq⟩ <;> rcases q' with ⟨_ | _ | _ | _ | q', hq'⟩ <;>
    first
      | omega
      | (exfalso; exact hqq' rfl)
      | exact Or.inl ⟨hx, hx'⟩
      | exact Or.inl ⟨hx', hx⟩
      | exact Or.inr (Or.inl ⟨hx, hx'⟩)
      | exact Or.inr (Or.inl ⟨hx', hx⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨hx, hx'⟩))
      | exact Or.inr (Or.inr (Or.inl ⟨hx', hx⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hx, hx'⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hx', hx⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hx, hx'⟩))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hx', hx⟩))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hx, hx'⟩)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hx', hx⟩)))))

/-- **The N-K4 leaf (HandA's `NK4_leaf`) from the certificate facts of the core layer.** -/
theorem NK4_leaf_of_certs (hu : G14.univOK () = true) (hr : G14.rootOK = true)
    (caseR : ∀ r ∈ G14.reps, ∀ M : G14.Model, M.occ G14.T[r]! → False)
    (caseDead : ∀ M : G14.Model, (G14.deadClause.any fun (i, n) => G14.assign M i == n) = true → False) :
    NK4_leaf := by
  intro n H hC hW hK
  obtain ⟨B⟩ := lbase_of_K4 hK
  have hW' := W7I_of_prop hC hW
  exact NK4_leaf_of hC B (fun B' => B'.edgeSound hC hW') (fun B' => B'.pairSound hC hW') hu hr caseR caseDead

end Erdos616R21
