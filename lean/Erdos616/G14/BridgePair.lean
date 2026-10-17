import Erdos616.G14.Bridge
/-!
# Erdős #616, r = 21, G14 bridge: pairwise soundness `PairSound` of the encoding

For two edges `F, F'` of a counterexample with a labelled base, the overlap vector `z = st (F ∩ F')`
(`z_q = |F ∩ F' ∩ O_q|`) lies in `zbox`, and all pairwise rules of `G14.rulesAt` hold with `z_U` replaced by its
least admissible value `zumin` (Lemma A; F1; SAME = S(a) + W7-I + S(b); L on `X ∪ {F, F'}` for every set `X` of
≥ 2 base edges; D1 at derived 5-pairs). The only facts used about the overlap outside the base union are
`zumin ≤ |(F ∩ F') \ ⋃P| ≤ u(F), u(F')`.
-/
open Finset

namespace Erdos616R21
open G14B
variable {V : Type*} [DecidableEq V]

/-- L on six edges (repetitions allowed): no common point ⇒ the union has ≥ 61 points. -/
theorem L6 {H : Finset (Finset V)} (hC : Counter H) {a b c d e f : Finset V} (ha : a ∈ H) (hb : b ∈ H)
    (hc : c ∈ H) (hd : d ∈ H) (he : e ∈ H) (hf : f ∈ H)
    (h : ∀ x, x ∈ a → x ∈ b → x ∈ c → x ∈ d → x ∈ e → x ∈ f → False) :
    61 ≤ (a ∪ b ∪ c ∪ d ∪ e ∪ f).card := by
  have := (propL_iff_span H 60).1 hC.propL {a, b, c, d, e, f}
    (by simp [insert_subset_iff, ha, hb, hc, hd, he, hf]) (by simp)
    (fun x => by
      by_contra hx; push Not at hx
      exact h x (hx a (by simp)) (hx b (by simp)) (hx c (by simp)) (hx d (by simp)) (hx e (by simp))
        (hx f (by simp)))
  have e' : ({a, b, c, d, e, f} : Finset (Finset V)).biUnion id = a ∪ b ∪ c ∪ d ∪ e ∪ f := by
    ext; simp <;> tauto
  rw [e'] at this; omega

theorem ne_zero_of_testBit {n k : ℕ} (h : n.testBit k = true) : n ≠ 0 := by
  rintro rfl; rw [Nat.zero_testBit] at h; exact Bool.false_ne_true h

theorem O4_get_le_sum (z : G14.O4) (k : Fin 4) : z.get k ≤ z.sum := by
  obtain ⟨a0, a1, a2, a3⟩ := z
  rcases k with ⟨_ | _ | _ | _ | _, hk⟩ <;> simp [G14.O4.get, G14.O4.sum] <;> omega

theorem outX_eq (X : ℕ) (o : G14.O4) : G14.outX X o =
    (if X.testBit 0 then 0 else o.get 0) + (if X.testBit 1 then 0 else o.get 1) +
      (if X.testBit 2 then 0 else o.get 2) + (if X.testBit 3 then 0 else o.get 3) := by
  simp only [G14.outX, G14.Q4, List.foldl_cons, List.foldl_nil]
  split_ifs <;> omega

theorem osX_eq (X : ℕ) : G14.osX X =
    (if X.testBit 0 then G14.OSZ 0 else 0) + (if X.testBit 1 then G14.OSZ 1 else 0) +
      (if X.testBit 2 then G14.OSZ 2 else 0) + (if X.testBit 3 then G14.OSZ 3 else 0) := by
  simp only [G14.osX, G14.Q4, List.foldl_cons, List.foldl_nil]
  split_ifs <;> omega

theorem mem_zbox {o1 o2 z : G14.O4}
    (h : ∀ q : Fin 4, o1.get q + o2.get q - G14.OSZ q ≤ z.get q ∧ z.get q ≤ o1.get q ∧ z.get q ≤ o2.get q) :
    z ∈ G14.zbox o1 o2 := by
  have hr : ∀ q : Fin 4, z.get q ∈ G14.zr o1 o2 q := by
    intro q; obtain ⟨h1, h2, h3⟩ := h q
    unfold G14.zr; rw [List.mem_range'_1]; omega
  obtain ⟨a0, a1, a2, a3⟩ := z
  unfold G14.zbox
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨a0, hr 0, a1, hr 1, a2, hr 2, a3, hr 3, rfl⟩

namespace LBase
variable {H : Finset (Finset V)} (B : LBase H)

theorem tr_inter (F F' : Finset V) : B.tr (F ∩ F') = B.tr F &&& B.tr F' := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and]
  by_cases hk : k < 16
  · have h1 := B.testBit_tr (F ∩ F') ⟨k, hk⟩
    have h2 := B.testBit_tr F ⟨k, hk⟩
    have h3 := B.testBit_tr F' ⟨k, hk⟩
    simp only at h1 h2 h3
    rw [h1, h2, h3]; simp [mem_inter]
  · rw [B.testBit_tr_ge _ (by omega), B.testBit_tr_ge _ (by omega), B.testBit_tr_ge _ (by omega)]; rfl

theorem tr_sdiff_P (S : Finset V) (j : Fin 4) : B.tr (S \ B.P j) = B.tr S &&& G14.cmp (G14.Pm j) := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and]
  by_cases hk : k < 16
  · have h1 := B.testBit_tr (S \ B.P j) ⟨k, hk⟩
    have h2 := B.testBit_tr S ⟨k, hk⟩
    have h3 := B.hmem ⟨k, hk⟩ j
    have h4 := testBit_cmp (G14.Pm j) ⟨k, hk⟩
    simp only at h1 h2 h3 h4
    rw [h1, h2, h4]
    cases h : (G14.Pm j).testBit k <;> simp [mem_sdiff, h3, h]
  · rw [B.testBit_tr_ge _ (by omega), B.testBit_tr_ge _ (by omega)]; rfl

theorem st_sum (F : Finset V) :
    (B.st F).sum = (F ∩ B.O 0).card + (F ∩ B.O 1).card + (F ∩ B.O 2).card + (F ∩ B.O 3).card := by
  have h0 : B.ov F 0 = (F ∩ B.O 0).card := B.ov_eq F 0
  have h1 : B.ov F 1 = (F ∩ B.O 1).card := B.ov_eq F 1
  have h2 : B.ov F 2 = (F ∩ B.O 2).card := B.ov_eq F 2
  have h3 : B.ov F 3 = (F ∩ B.O 3).card := B.ov_eq F 3
  show B.ov F 0 + B.ov F 1 + B.ov F 2 + B.ov F 3 = _
  rw [h0, h1, h2, h3]

theorem st_g0 (F : Finset V) : (B.st F).get 0 = (F ∩ B.O 0).card := B.st_get_fin F 0
theorem st_g1 (F : Finset V) : (B.st F).get 1 = (F ∩ B.O 1).card := B.st_get_fin F 1
theorem st_g2 (F : Finset V) : (B.st F).get 2 = (F ∩ B.O 2).card := B.st_get_fin F 2
theorem st_g3 (F : Finset V) : (B.st F).get 3 = (F ∩ B.O 3).card := B.st_get_fin F 3

theorem uu_eq (hC : Counter H) {F : Finset V} (hF : F ∈ H) : G14.uu (B.tr F) (B.st F) = (F \ B.PU).card := by
  unfold G14.uu; rw [B.st_sum]; have := B.edge_part hC hF; omega

/-- the overlap decomposition `|F ∩ F'| = pc I + Σ z + z_U` -/
theorem inter_decomp (F F' : Finset V) :
    (F ∩ F').card = G14.pc (B.tr F &&& B.tr F') + (B.st (F ∩ F')).sum + ((F ∩ F') \ B.PU).card := by
  have := B.card_whole (F ∩ F')
  rw [B.st_sum, ← B.tr_inter]; omega

theorem zumin_le (hC : Counter H) {F F' : Finset V} (hF : F ∈ H) (hF' : F' ∈ H) :
    G14.zumin (B.tr F) (B.tr F') (B.st (F ∩ F')) ≤ ((F ∩ F') \ B.PU).card := by
  unfold G14.zumin
  have h1 := B.inter_decomp F F'
  have h2 := inter_ge5 hC hF hF'
  omega

theorem zU_le (F F' : Finset V) : ((F ∩ F') \ B.PU).card ≤ (F \ B.PU).card :=
  card_le_card (sdiff_subset_sdiff inter_subset_left le_rfl)

theorem zU_le' (F F' : Finset V) : ((F ∩ F') \ B.PU).card ≤ (F' \ B.PU).card :=
  card_le_card (sdiff_subset_sdiff inter_subset_right le_rfl)

/-- the overlap vector lies in `zbox` -/
theorem z_mem_zbox (hC : Counter H) (F F' : Finset V) :
    B.st (F ∩ F') ∈ G14.zbox (B.st F) (B.st F') := by
  apply mem_zbox
  intro q
  rw [B.st_get_fin, B.st_get_fin, B.st_get_fin, ← B.card_O hC q]
  refine ⟨?_, card_le_card ?_, card_le_card ?_⟩
  · have h1 := card_union_add_card_inter (F ∩ B.O q) (F' ∩ B.O q)
    have h2 : (F ∩ B.O q) ∪ (F' ∩ B.O q) ⊆ B.O q := union_subset inter_subset_right inter_subset_right
    have h3 : (F ∩ B.O q) ∩ (F' ∩ B.O q) = F ∩ F' ∩ B.O q := by ext; simp only [mem_inter]; tauto
    rw [h3] at h1
    have := card_le_card h2
    omega
  · intro x; simp only [mem_inter]; tauto
  · intro x; simp only [mem_inter]; tauto

/-! ### F1 -/

theorem rule_F1 (hC : Counter H) {F F' : Finset V} (hF : F ∈ H) (hF' : F' ∈ H) (q : Fin 4) :
    (B.tr F &&& B.tr F' &&& G14.Pm q != 0 || decide (0 < (B.st (F ∩ F')).get q)) = true := by
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
  obtain ⟨x, hxF, hxF', hxq⟩ := inter3 hC hF hF' (B.hP q)
  by_cases hx : x ∈ B.core
  · left
    obtain ⟨k, rfl⟩ := B.mem_core.1 hx
    apply ne_zero_of_testBit (k := k)
    rw [Nat.testBit_and, Nat.testBit_and, B.testBit_tr, B.testBit_tr, (B.hmem k q).1 hxq]
    simp [hxF, hxF']
  · right
    rw [B.st_get_fin]
    exact card_pos.2 ⟨x, by simp [O, hxF, hxF', hxq, hx]⟩

/-! ### D1 at derived 5-pairs -/

theorem rule_D1 (hC : Counter H) {F F' : Finset V} (hF : F ∈ H) (hF' : F' ∈ H) (zu : ℕ)
    (hzu : zu ≤ ((F ∩ F') \ B.PU).card) (k : Fin 4) :
    (G14.xq (B.tr F) (B.st F) k != 5 ||
      (B.tr F &&& G14.Pm k &&& G14.cmp (B.tr F') == 0 && (B.st (F ∩ F')).get k == (B.st F).get k) ||
      decide (G14.pc (B.tr F' &&& G14.Pm k) + (B.st F').get k + G14.pc (B.tr F &&& B.tr F' &&& G14.cmp (G14.Pm k)) +
        zu + ((B.st (F ∩ F')).sum - (B.st (F ∩ F')).get k) ≤ 9)) = true := by
  simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq]
  by_cases h5 : G14.xq (B.tr F) (B.st F) k = 5
  swap; · exact Or.inl (Or.inl h5)
  by_cases hs : B.tr F &&& G14.Pm k &&& G14.cmp (B.tr F') = 0 ∧ (B.st (F ∩ F')).get k = (B.st F).get k
  · exact Or.inl (Or.inr hs)
  right
  rw [B.xq_eq] at h5
  have hM : (B.P k ∩ F).card = 5 := by rw [inter_comm]; exact h5
  obtain ⟨x, hxk, hxF, hxF'⟩ : ∃ x, x ∈ B.P k ∧ x ∈ F ∧ x ∉ F' := by
    by_cases hm : B.tr F &&& G14.Pm k &&& G14.cmp (B.tr F') = 0
    · have hne : (B.st (F ∩ F')).get k ≠ (B.st F).get k := fun h => hs ⟨hm, h⟩
      rw [B.st_get_fin, B.st_get_fin] at hne
      have hle : (F ∩ F' ∩ B.O k).card ≤ (F ∩ B.O k).card :=
        card_le_card (fun y => by simp only [mem_inter]; tauto)
      obtain ⟨y, hy, hny⟩ := exists_mem_notMem_of_card_lt_card (lt_of_le_of_ne hle hne)
      rw [mem_inter] at hy
      refine ⟨y, B.O_sub_P k hy.2, hy.1, fun h => hny ?_⟩
      simp [hy.1, hy.2, h]
    · obtain ⟨t, ht⟩ := exists_bit_of_ne
        (and_lt (cmp_lt _ (B.tr_lt F'))) (by decide : (0 : ℕ) < 65536) hm
      rw [Nat.zero_testBit, Nat.testBit_and, Nat.testBit_and, testBit_cmp, B.testBit_tr, B.testBit_tr] at ht
      refine ⟨B.c t, (B.hmem t k).2 ?_, ?_, ?_⟩
      · cases h : (G14.Pm k).testBit t <;> simp_all
      · by_contra h'; simp_all
      · intro h'; simp_all
  have hD := D1 hC (B.hP k) hF hF' hM (mem_inter.2 ⟨hxk, hxF⟩) hxF'
  -- |F' ∩ (P_k ∪ F)| = |F' ∩ P_k| + |F' ∩ F| - |F' ∩ F ∩ P_k|
  have hU := card_union_add_card_inter (F' ∩ B.P k) (F' ∩ F)
  rw [← inter_union_distrib_left] at hU
  have e1 : F' ∩ B.P k ∩ (F' ∩ F) = (F ∩ F') ∩ B.P k := by ext; simp only [mem_inter]; tauto
  have e2 : F' ∩ F = F ∩ F' := inter_comm _ _
  rw [e1, e2, B.card_inter_P, B.card_inter_P, B.tr_inter] at hU
  have hdec := B.inter_decomp F F'
  have hsp := pc_split (B.tr F &&& B.tr F') (G14.Pm k)
  have hle := O4_get_le_sum (B.st (F ∩ F')) k
  rw [B.st_get_fin (F ∩ F') k] at hle ⊢
  rw [B.st_get_fin F' k]
  omega

/-! ### SAME at a base 5-pair: S(a), W7-I, S(b) -/

theorem rule_SAME (hC : Counter H) (hW : W7I H) {F F' : Finset V} (hF : F ∈ H) (hF' : F' ∈ H) (zu : ℕ)
    (hzu : zu = G14.zumin (B.tr F) (B.tr F') (B.st (F ∩ F'))) (i j : Fin 4) (hij : i ≠ j) :
    (!(G14.isSingle (B.tr F) i j && G14.isSingle (B.tr F') i j &&
        (B.tr F &&& (G14.Pm i &&& G14.Pm j)) != (B.tr F' &&& (G14.Pm i &&& G14.Pm j))) ||
      ((B.tr F &&& B.tr F') &&& G14.cmp (G14.Pm i ||| G14.Pm j) == 0 &&
        G14.Q4.all (fun q => q == (i : ℕ) || q == (j : ℕ) || (B.st (F ∩ F')).get q == 0) && zu == 0 &&
        (decide (2 ≤ G14.pc ((B.tr F &&& B.tr F') &&& G14.Pm i &&& G14.cmp (G14.Pm j)) + (B.st (F ∩ F')).get i) &&
         decide (2 ≤ G14.pc ((B.tr F &&& B.tr F') &&& G14.Pm j &&& G14.cmp (G14.Pm i)) + (B.st (F ∩ F')).get j) &&
         decide (5 ≤ G14.pc ((B.tr F &&& B.tr F') &&& G14.Pm i &&& G14.cmp (G14.Pm j)) + (B.st (F ∩ F')).get i +
           (G14.pc ((B.tr F &&& B.tr F') &&& G14.Pm j &&& G14.cmp (G14.Pm i)) + (B.st (F ∩ F')).get j))))) = true := by
  by_cases hs : (G14.isSingle (B.tr F) i j && G14.isSingle (B.tr F') i j &&
      (B.tr F &&& (G14.Pm i &&& G14.Pm j)) != (B.tr F' &&& (G14.Pm i &&& G14.Pm j))) = true
  swap; · simp only [Bool.not_eq_true] at hs; simp [hs]
  apply bor_right
  simp only [G14.isSingle, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hs
  obtain ⟨⟨h1, h2⟩, h3⟩ := hs
  have hN := B.card_PPN hij
  have chF : ∀ t : Fin 16, B.c t ∈ F ∩ (B.P i ∩ B.P j) ↔ (B.tr F &&& (G14.Pm i &&& G14.Pm j)).testBit t = true := by
    intro t; simp only [mem_inter, Nat.testBit_and, B.testBit_tr, Bool.and_eq_true, decide_eq_true_eq, B.hmem]
  have chF' : ∀ t : Fin 16, B.c t ∈ F' ∩ (B.P i ∩ B.P j) ↔ (B.tr F' &&& (G14.Pm i &&& G14.Pm j)).testBit t = true := by
    intro t; simp only [mem_inter, Nat.testBit_and, B.testBit_tr, Bool.and_eq_true, decide_eq_true_eq, B.hmem]
  have sF : F ∩ (B.P i ∩ B.P j) ⊆ B.core := inter_subset_right.trans (B.inter2_sub_core hij)
  have sF' : F' ∩ (B.P i ∩ B.P j) ⊆ B.core := inter_subset_right.trans (B.inter2_sub_core hij)
  obtain ⟨x, hx⟩ := card_eq_one.1 ((B.card_of_sub_core _ sF _ chF).trans h1)
  obtain ⟨y, hy⟩ := card_eq_one.1 ((B.card_of_sub_core _ sF' _ chF').trans h2)
  have hxy : x ≠ y := by
    rintro rfl
    exact B.ne_of_mask_ne chF chF' (and_lt (and_lt (Pm_lt _))) (and_lt (and_lt (Pm_lt _))) h3 (hx.trans hy.symm)
  have hO := S_a_O hC (B.hP i) (B.hP j) hF hF' hN hx hy hxy
  have hsub : ∀ w, w ∈ F → w ∈ F' → w ∈ B.P i ∨ w ∈ B.P j := by
    intro w hw hw'
    by_contra hno
    have hno' : w ∉ B.P i ∪ B.P j := by simpa [not_or] using hno
    exact Finset.disjoint_left.1 hO (mem_sdiff.2 ⟨hw, hno'⟩) (mem_sdiff.2 ⟨hw', hno'⟩)
  obtain ⟨hWA, hWC⟩ := hW (B.P i) (B.hP i) (B.P j) (B.hP j) F hF F' hF' hN x y hx hy hxy
  have hSb := S_b hC (B.hP i) (B.hP j) hF hF' hN hx hy hxy
  -- the A-part `F ∩ F' ∩ (P_i \ P_j)` = core part + `F ∩ F' ∩ O_i`
  have partA : ∀ a b : Fin 4, a ≠ b → (F ∩ F' ∩ (B.P a \ B.P b)).card =
      G14.pc ((B.tr F &&& B.tr F') &&& G14.Pm a &&& G14.cmp (G14.Pm b)) + (B.st (F ∩ F')).get a := by
    intro a b hab
    have h := B.card_inter_P ((F ∩ F') \ B.P b) a
    rw [B.tr_sdiff_P, B.tr_inter] at h
    have e1 : (F ∩ F') \ B.P b ∩ B.P a = F ∩ F' ∩ (B.P a \ B.P b) := by
      ext w; simp only [mem_inter, mem_sdiff]; tauto
    have e2 : (F ∩ F') \ B.P b ∩ B.O a = F ∩ F' ∩ B.O a := by
      ext w; simp only [mem_inter, mem_sdiff]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, fun hb => B.O_disj hab h2 hb⟩, h2⟩
    have e3 : B.tr F &&& B.tr F' &&& G14.cmp (G14.Pm b) &&& G14.Pm a =
        B.tr F &&& B.tr F' &&& G14.Pm a &&& G14.cmp (G14.Pm b) := by
      apply Nat.eq_of_testBit_eq; intro t; simp only [Nat.testBit_and]
      cases (B.tr F).testBit t <;> cases (B.tr F').testBit t <;> cases (G14.cmp (G14.Pm b)).testBit t <;>
        cases (G14.Pm a).testBit t <;> rfl
    rw [e1, e2, e3] at h
    rw [h, B.st_get_fin]
  have hA := partA i j hij
  have hC' := partA j i hij.symm
  rw [hA] at hWA hSb; rw [hC'] at hWC hSb
  -- `F ∩ F' ⊆ P_i ∪ P_j`
  have hzU : ((F ∩ F') \ B.PU).card = 0 := by
    rw [card_eq_zero, sdiff_eq_empty_iff_subset]
    intro w hw; rw [mem_inter] at hw
    rcases hsub w hw.1 hw.2 with h | h
    · exact B.P_sub_PU i h
    · exact B.P_sub_PU j h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨⟨hWA, hWC⟩, hSb⟩⟩
  · by_contra hne
    obtain ⟨t, ht⟩ := exists_bit_of_ne (and_lt (cmp_lt _ (Nat.or_lt_two_pow (Pm_lt16 _) (Pm_lt16 _))))
      (by decide : (0 : ℕ) < 65536) hne
    rw [Nat.zero_testBit, Nat.testBit_and, Nat.testBit_and, testBit_cmp, B.testBit_tr, B.testBit_tr,
      Nat.testBit_or] at ht
    have hcF : B.c t ∈ F := by by_contra h; simp [h] at ht
    have hcF' : B.c t ∈ F' := by by_contra h; simp [h] at ht
    rcases hsub _ hcF hcF' with h | h
    · rw [B.hmem] at h; simp [h] at ht
    · rw [B.hmem] at h; simp [h] at ht
  · rw [G14.Q4_all_fin]; intro q
    simp only [Bool.or_eq_true, beq_iff_eq]
    by_cases hqi : q = i
    · exact Or.inl (Or.inl (by rw [hqi]))
    by_cases hqj : q = j
    · exact Or.inl (Or.inr (by rw [hqj]))
    right
    rw [B.st_get_fin, card_eq_zero, eq_empty_iff_forall_notMem]
    intro w hw
    simp only [mem_inter] at hw
    rcases hsub w hw.1.1 hw.1.2 with h | h
    · exact B.O_disj hqi hw.2 h
    · exact B.O_disj hqj hw.2 h
  · rw [hzu]; unfold G14.zumin
    have := B.inter_decomp F F'
    have := inter_ge5 hC hF hF'
    omega

/-! ### L on `X ∪ {F, F'}` -/

theorem mem_UX (X : ℕ) (x : V) : x ∈ B.UX X ↔ ∃ q : Fin 4, X.testBit q = true ∧ x ∈ B.P q := by
  constructor
  · intro h
    unfold UX at h
    simp only [mem_union] at h
    rcases h with ((h | h) | h) | h <;> split at h <;> first
      | exact ⟨_, by assumption, h⟩ | simp at h
  · rintro ⟨q, hX, hP⟩
    unfold UX; simp only [mem_union]
    rcases q with ⟨_ | _ | _ | _ | _, h⟩
    · left; left; left; simp only [Fin.zero_eta] at hX hP ⊢; rw [if_pos hX]; exact hP
    · left; left; right; rw [if_pos hX]; exact hP
    · left; right; rw [if_pos hX]; exact hP
    · right; rw [if_pos hX]; exact hP
    · omega

theorem rule_L (hC : Counter H) {F F' : Finset V} (hF : F ∈ H) (hF' : F' ∈ H) (zu : ℕ)
    (hzu : zu ≤ ((F ∩ F') \ B.PU).card) (X : ℕ) (a b c d : Fin 4) (hab : a ≠ b)
    (hsel : ∀ q : Fin 4, X.testBit q = true ↔ (q = a ∨ q = b ∨ q = c ∨ q = d))
    (hm : ∀ k : Fin 16, (G14.cupX X).testBit k = selX X k) (hlt : G14.cupX X < 65536)
    (hcap : ∀ k : Fin 16, (G14.Pm a).testBit k = true → (G14.Pm b).testBit k = true →
      (G14.Pm c).testBit k = true → (G14.Pm d).testBit k = true → (G14.capX X).testBit k = true) :
    (G14.capX X &&& (B.tr F &&& B.tr F') != 0 ||
      decide (61 + (G14.pc ((B.tr F &&& B.tr F') &&& G14.cmp (G14.cupX X)) + zu + G14.outX X (B.st (F ∩ F'))) ≤
        (G14.pc (G14.cupX X) + G14.osX X) +
          (G14.pc (B.tr F &&& G14.cmp (G14.cupX X)) + G14.uu (B.tr F) (B.st F) + G14.outX X (B.st F)) +
          (G14.pc (B.tr F' &&& G14.cmp (G14.cupX X)) + G14.uu (B.tr F') (B.st F') + G14.outX X (B.st F')))) =
      true := by
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
  by_cases h0 : G14.capX X &&& (B.tr F &&& B.tr F') = 0
  swap; · exact Or.inl h0
  right
  -- L on P_a, P_b, P_c, P_d, F, F'
  have hL := L6 hC (B.hP a) (B.hP b) (B.hP c) (B.hP d) hF hF' (fun x ha hb hc hd hx hx' => by
    obtain ⟨k, rfl⟩ := B.hcore a b hab x ha hb
    have : (G14.capX X &&& (B.tr F &&& B.tr F')).testBit k = true := by
      rw [Nat.testBit_and, Nat.testBit_and, B.testBit_tr, B.testBit_tr,
        hcap k ((B.hmem k a).1 ha) ((B.hmem k b).1 hb) ((B.hmem k c).1 hc) ((B.hmem k d).1 hd)]
      simp [hx, hx']
    rw [h0, Nat.zero_testBit] at this; exact Bool.false_ne_true this)
  have eU : B.P a ∪ B.P b ∪ B.P c ∪ B.P d ∪ F ∪ F' = (B.UX X) ∪ (F ∪ F') := by
    ext x
    simp only [mem_union, B.mem_UX]
    constructor
    · rintro (((((h | h) | h) | h) | h) | h)
      · exact Or.inl ⟨a, (hsel a).2 (Or.inl rfl), h⟩
      · exact Or.inl ⟨b, (hsel b).2 (Or.inr (Or.inl rfl)), h⟩
      · exact Or.inl ⟨c, (hsel c).2 (Or.inr (Or.inr (Or.inl rfl))), h⟩
      · exact Or.inl ⟨d, (hsel d).2 (Or.inr (Or.inr (Or.inr rfl))), h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (⟨q, hq, h⟩ | h | h)
      · rcases (hsel q).1 hq with rfl | rfl | rfl | rfl
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
        · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
        · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  rw [eU] at hL
  -- |(B.UX X) ∪ G| = |(B.UX X)| + |G \ (B.UX X)|
  have k1 := card_union_add_card_inter (B.UX X) (F ∪ F')
  have k2 := card_sdiff_eq (F ∪ F') (B.UX X)
  rw [inter_comm] at k2
  -- |(F ∪ F') \ (B.UX X)| + |(F ∩ F') \ (B.UX X)| = |F \ (B.UX X)| + |F' \ (B.UX X)|
  have k3 := card_union_add_card_inter (F \ (B.UX X)) (F' \ (B.UX X))
  have f1 : (F \ (B.UX X)) ∪ (F' \ (B.UX X)) = (F ∪ F') \ (B.UX X) := by ext; simp only [mem_union, mem_sdiff]; tauto
  have f2 : (F \ (B.UX X)) ∩ (F' \ (B.UX X)) = (F ∩ F') \ (B.UX X) := by ext; simp only [mem_inter, mem_sdiff]; tauto
  rw [f1, f2] at k3
  have k4 := card_sdiff_eq F (B.UX X)
  have k5 := card_sdiff_eq F' (B.UX X)
  have k6 := card_sdiff_eq (F ∩ F') (B.UX X)
  have cF := B.card_inter_UX F X _ hm
  have cF' := B.card_inter_UX F' X _ hm
  have cI := B.card_inter_UX (F ∩ F') X _ hm
  rw [B.tr_inter] at cI
  have cU := B.card_inter_UX (B.UX X) X _ hm
  rw [inter_self, B.tr_UX X _ hm hlt, Nat.and_self] at cU
  have oU : ∀ q : Fin 4, X.testBit q = true → (B.UX X ∩ B.O q).card = G14.OSZ q := by
    intro q hq; rw [B.UX_O X q hq, B.card_O hC q]
  have pF := B.edge_part hC hF
  have pF' := B.edge_part hC hF'
  have pI := B.inter_decomp F F'
  rw [B.uu_eq hC hF, B.uu_eq hC hF', outX_eq, outX_eq, outX_eq, osX_eq]
  have s1 := pc_split (B.tr F) (G14.cupX X)
  have s2 := pc_split (B.tr F') (G14.cupX X)
  have s3 := pc_split (B.tr F &&& B.tr F') (G14.cupX X)
  have g1 := B.st_sum (F ∩ F')
  rw [B.st_g0 F, B.st_g1 F, B.st_g2 F, B.st_g3 F, B.st_g0 F', B.st_g1 F', B.st_g2 F', B.st_g3 F',
    B.st_g0 (F ∩ F'), B.st_g1 (F ∩ F'), B.st_g2 (F ∩ F'), B.st_g3 (F ∩ F')]
  have o0 := oU 0; have o1 := oU 1; have o2 := oU 2; have o3 := oU 3
  have hz1 := B.zU_le F F'
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at o0 o1 o2 o3 g1 ⊢
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [h3] at o3
  have uF := hC.unif F hF
  have uF' := hC.unif F' hF'
  rcases Bool.eq_false_or_eq_true (X.testBit 0) with b0 | b0 <;>
  rcases Bool.eq_false_or_eq_true (X.testBit 1) with b1 | b1 <;>
  rcases Bool.eq_false_or_eq_true (X.testBit 2) with b2 | b2 <;>
  rcases Bool.eq_false_or_eq_true (X.testBit 3) with b3 | b3 <;>
  simp only [b0, b1, b2, b3, ite_true, ite_false, if_true, if_false, Bool.false_eq_true, forall_const,
    true_implies, false_implies] at cF cF' cI cU o0 o1 o2 o3 ⊢ <;>
  omega

/-! ### all pairwise rules, and `PairSound` -/

theorem rules_all (hC : Counter H) (hW : W7I H) {F F' : Finset V} (hF : F ∈ H) (hF' : F' ∈ H) :
    G14.rulesAt (B.tr F) (B.st F) (B.tr F') (B.st F') (B.st (F ∩ F'))
      (G14.zumin (B.tr F) (B.tr F') (B.st (F ∩ F'))) = true := by
  have hzm := B.zumin_le hC hF hF'
  unfold G14.rulesAt
  dsimp only
  refine band_of (band_of (band_of (band_of (band_of (band_of ?r1 ?r2) ?r3) ?r4) ?r5) ?r6) ?r7
  · rw [decide_eq_true_eq, B.uu_eq hC hF, B.uu_eq hC hF']
    have := B.zU_le F F'; have := B.zU_le' F F'
    omega
  · rw [decide_eq_true_eq]; unfold G14.zumin; omega
  · rw [G14.Q4_all_fin]; intro q; exact B.rule_F1 hC hF hF' q
  · rw [List.all_eq_true]; intro p hp
    simp only [G14.PR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact B.rule_SAME hC hW hF hF' _ rfl 0 1 (by decide)
    · exact B.rule_SAME hC hW hF hF' _ rfl 0 2 (by decide)
    · exact B.rule_SAME hC hW hF hF' _ rfl 0 3 (by decide)
    · exact B.rule_SAME hC hW hF hF' _ rfl 1 2 (by decide)
    · exact B.rule_SAME hC hW hF hF' _ rfl 1 3 (by decide)
    · exact B.rule_SAME hC hW hF hF' _ rfl 2 3 (by decide)
  · rw [List.all_eq_true]; intro X hX
    simp only [G14.XS, List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact B.rule_L hC hF hF' _ hzm 3 0 1 1 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact B.rule_L hC hF hF' _ hzm 5 0 2 2 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact B.rule_L hC hF hF' _ hzm 6 1 2 2 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact B.rule_L hC hF hF' _ hzm 9 0 3 3 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact B.rule_L hC hF hF' _ hzm 10 1 3 3 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact B.rule_L hC hF hF' _ hzm 12 2 3 3 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact B.rule_L hC hF hF' _ hzm 7 0 1 2 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact B.rule_L hC hF hF' _ hzm 11 0 1 3 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact B.rule_L hC hF hF' _ hzm 13 0 2 3 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact B.rule_L hC hF hF' _ hzm 14 1 2 3 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact B.rule_L hC hF hF' _ hzm 15 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [G14.Q4_all_fin]; intro k; exact B.rule_D1 hC hF hF' _ hzm k
  · rw [G14.Q4_all_fin]; intro k
    have h := B.rule_D1 hC hF' hF (G14.zumin (B.tr F) (B.tr F') (B.st (F ∩ F')))
      (by rw [inter_comm F' F]; exact hzm) k
    rw [inter_comm F' F, Nat.and_comm (B.tr F') (B.tr F)] at h
    exact h

/-- **Pairwise soundness — proved.** -/
theorem pairSound (hC : Counter H) (hW : W7I H) : B.PairSound := by
  intro F hF F' hF' _ _ _
  unfold G14.feasible
  exact List.any_eq_true.2 ⟨_, B.z_mem_zbox hC F F', B.rules_all hC hW hF hF'⟩

end LBase
end Erdos616R21
