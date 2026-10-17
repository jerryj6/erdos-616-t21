import Erdos616.NoK4.Edge

/-!
# Rule soundness, part 2: the pair rules (`PairSound`)
-/

open Finset TrCheck

namespace Erdos616R21.NoK4

variable {V : Type*} [DecidableEq V] {C : Cls} {H : Finset (Finset V)}

namespace Base

variable (B : Base C H)

theorem tr_inter (X Y : Finset V) : B.tr (X ∩ Y) = B.tr X &&& B.tr Y := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < C.n
  · rw [Nat.testBit_and, B.bitT _ ht, B.bitT _ ht, B.bitT _ ht]; simp
  · rw [Nat.testBit_and, B.bitT_big _ ht, B.bitT_big _ ht]; rfl

theorem card_parts (W : Finset V) : W.card = C.pc (B.tr W) + (B.st W).sum + (W \ B.BU).card := by
  have hr := B.region W
  have hc := B.card_ci_eq_pc W (B.tr W) (fun i hi => by rw [B.testBit_tr]; tauto)
  rw [hc] at hr
  simp only [st, V4.sum]
  omega

/-- `|W ∩ (P i ∖ P j)| = |w ∧ P_i ∖ P_j| + |W ∩ O_i|` -/
theorem card_WPiPj (W : Finset V) {i j : ℕ} (hi : i < 4) (hj : j < 4) (hij : i ≠ j) :
    (W ∩ (B.P i \ B.P j)).card = C.pc (C.nd (B.tr W &&& C.P i) (C.P j)) + (W ∩ B.O i).card := by
  have h := Erdos616R21.card_sdiff_eq (W ∩ (B.P i \ B.P j)) B.cs
  have e1 : (W ∩ (B.P i \ B.P j)) \ B.cs = W ∩ B.O i := by
    ext x; simp only [mem_sdiff, mem_inter, O]
    constructor
    · rintro ⟨⟨h1, h2, -⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2, B.O_excl hi hj (by simp [O, h2, h3]) (Ne.symm hij)⟩, h3⟩
  have e2 : (W ∩ (B.P i \ B.P j) ∩ B.cs).card = C.pc (C.nd (B.tr W &&& C.P i) (C.P j)) := by
    apply B.card_core_only _ inter_subset_right
    intro t ht
    simp only [testBit_nd C _ _ t ht, Nat.testBit_and, B.bitP hi ht, B.bitP hj ht, B.bitT W ht,
      Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not, mem_inter, mem_sdiff,
      B.core_mem_cs ht, and_true]
    try tauto
  rw [e1, e2] at h; omega

/-! ### pair rule (1): Lemma A -/

theorem pA_ok (hC : Counter H) {X Y : Finset V} (hX : X ∈ H) (hY : Y ∈ H) :
    5 ≤ C.pc (B.tr X &&& B.tr Y) + (B.st (X ∩ Y)).sum + ((X ∩ Y) \ B.BU).card := by
  rw [← B.tr_inter, ← B.card_parts]; exact Erdos616R21.inter_ge5 hC hX hY

/-! ### pair rule (2): F1 with each base edge -/

theorem pF1_ok (hC : Counter H) {X Y : Finset V} (hX : X ∈ H) (hY : Y ∈ H) {q : ℕ} (hq : q < 4) :
    B.tr X &&& B.tr Y &&& C.P q ≠ 0 ∨ (B.st (X ∩ Y)).get q ≠ 0 := by
  obtain ⟨x, hxX, hxY, hxq⟩ := Erdos616R21.inter3 hC hX hY (B.P_mem q hq)
  by_cases hc : x ∈ B.cs
  · obtain ⟨k, hk, rfl⟩ := B.mem_cs.1 hc
    left
    apply ne_zero_of_bit (k := k)
    simp only [Nat.testBit_and, B.bitT X hk, B.bitT Y hk, B.bitP hq hk, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hxX, hxY⟩, hxq⟩
  · right
    rw [B.st_get _ q hq]
    apply Nat.pos_iff_ne_zero.1
    exact card_pos.2 ⟨x, mem_inter.2 ⟨mem_inter.2 ⟨hxX, hxY⟩, mem_sdiff.2 ⟨hxq, hc⟩⟩⟩

/-! ### pair rule (3): L on `{S-edges, X, Y}` -/

theorem pc_ie (a c m : ℕ) :
    C.pc (C.nd (a ||| c) m) + C.pc (C.nd (a &&& c) m) = C.pc (C.nd a m) + C.pc (C.nd c m) := by
  simp only [Cls.pc, pcK_eq]
  rw [← card_union_add_card_inter ((range C.n).filter (fun i => (C.nd a m).testBit i = true))]
  congr 2
  · ext i; simp only [mem_filter, mem_range, mem_union]
    constructor
    · rintro ⟨hi, h⟩
      rw [testBit_nd C _ _ i hi, Nat.testBit_or] at h
      rw [testBit_nd C _ _ i hi, testBit_nd C _ _ i hi]
      simp only [Bool.and_eq_true, Bool.or_eq_true] at h ⊢
      tauto
    · rintro (⟨hi, h⟩ | ⟨hi, h⟩) <;> refine ⟨hi, ?_⟩ <;>
        rw [testBit_nd C _ _ i hi] at h ⊢ <;> rw [Nat.testBit_or] <;>
        simp only [Bool.and_eq_true, Bool.or_eq_true] at h ⊢ <;> tauto
  · ext i; simp only [mem_filter, mem_range, mem_inter]
    constructor
    · rintro ⟨hi, h⟩
      rw [testBit_nd C _ _ i hi, Nat.testBit_and] at h
      rw [testBit_nd C _ _ i hi, testBit_nd C _ _ i hi]
      simp only [Bool.and_eq_true] at h ⊢
      tauto
    · rintro ⟨⟨hi, h1⟩, ⟨-, h2⟩⟩
      refine ⟨hi, ?_⟩
      rw [testBit_nd C _ _ i hi] at h1 h2 ⊢
      rw [Nat.testBit_and]
      simp only [Bool.and_eq_true] at h1 h2 ⊢
      tauto

theorem slotE_O (hs : C.clsSane = true) (hH : ∀ e ∈ H, e.card = 21) (S : ℕ) {X E : Finset V} (hXE : X ⊆ E)
    {q : ℕ} (hq : q < 4) :
    ((B.slot S X 0 ∪ B.slot S X 1 ∪ B.slot S X 2 ∪ B.slot S X 3 ∪ E) ∩ B.O q).card =
      if Cls.mem S q then C.OS q else (E ∩ B.O q).card := by
  split_ifs with hm
  · rw [← B.card_O hs q hq hH]; congr 1
    ext x; simp only [mem_inter, mem_union]
    constructor
    · exact fun h => h.2
    · intro hx; refine ⟨?_, hx⟩
      have := (B.mem_slot_O S X hq hq hx).2 (Or.inl ⟨hm, rfl⟩)
      rcases q4_cases hq with rfl | rfl | rfl | rfl <;> tauto
  · congr 1
    ext x; simp only [mem_inter, mem_union]
    constructor
    · rintro ⟨h, hx⟩
      refine ⟨?_, hx⟩
      have key : ∀ r, r < 4 → x ∈ B.slot S X r → x ∈ E := by
        intro r hr hxr
        rcases (B.mem_slot_O S X hq hr hx).1 hxr with ⟨h1, rfl⟩ | ⟨-, h2⟩
        · exact absurd h1 hm
        · exact hXE h2
      rcases h with ((((h | h) | h) | h) | h)
      · exact key 0 (by omega) h
      · exact key 1 (by omega) h
      · exact key 2 (by omega) h
      · exact key 3 (by omega) h
      · exact h
    · rintro ⟨h, hx⟩; exact ⟨Or.inr h, hx⟩

set_option maxHeartbeats 2000000 in
theorem slotE_ci (S : ℕ) {X E : Finset V} (hXE : X ⊆ E) (mE : ℕ)
    (hmE : ∀ i, i < C.n → (B.core i ∈ E ↔ mE.testBit i = true)) :
    (B.ci (B.slot S X 0 ∪ B.slot S X 1 ∪ B.slot S X 2 ∪ B.slot S X 3 ∪ E)).card =
      C.pc (C.cupS S) + C.pc (C.nd mE (C.cupS S)) := by
  rw [← pc_split]
  apply B.card_ci_eq_pc
  intro i hi
  rw [Nat.testBit_or, cupS_bit, Bool.or_eq_true, ← hmE i hi]
  have h0 := B.P_bit (q := 0) (by omega) hi
  have h1 := B.P_bit (q := 1) (by omega) hi
  have h2 := B.P_bit (q := 2) (by omega) hi
  have h3 := B.P_bit (q := 3) (by omega) hi
  have hX := @hXE (B.core i)
  simp only [mem_union, slot]
  cases Cls.mem S 0 <;> cases Cls.mem S 1 <;> cases Cls.mem S 2 <;> cases Cls.mem S 3 <;>
    simp only [Bool.false_eq_true, if_false, if_true, Bool.false_and, Bool.true_and, Bool.false_or,
      Bool.or_false, Bool.or_eq_true, h0, h1, h2, h3] <;> tauto

set_option maxHeartbeats 2000000 in
theorem slotE_BU (S : ℕ) {X E : Finset V} (hXE : X ⊆ E) :
    (B.slot S X 0 ∪ B.slot S X 1 ∪ B.slot S X 2 ∪ B.slot S X 3 ∪ E) \ B.BU = E \ B.BU := by
  ext x; simp only [mem_sdiff, mem_union, slot, BU]
  have := @hXE x
  cases Cls.mem S 0 <;> cases Cls.mem S 1 <;> cases Cls.mem S 2 <;> cases Cls.mem S 3 <;>
    simp only [Bool.false_eq_true, if_false, if_true] <;> tauto

set_option maxHeartbeats 1000000 in
theorem pL_ok (hs : C.clsSane = true) (hC : Counter H) {X Y : Finset V} (hX : X ∈ H) (hY : Y ∈ H) (S : ℕ)
    (hS : S ∈ Cls.subs) :
    B.tr X &&& B.tr Y &&& C.capS S ≠ 0 ∨
    61 + (C.pc (C.nd (B.tr X &&& B.tr Y) (C.cupS S)) + ((X ∩ Y) \ B.BU).card + Cls.outS S (B.st (X ∩ Y))) ≤
      C.osS S + C.pc (C.cupS S) +
        (C.pc (C.nd (B.tr X) (C.cupS S)) + (21 - (C.pc (B.tr X) + (B.st X).sum)) + Cls.outS S (B.st X)) +
        (C.pc (C.nd (B.tr Y) (C.cupS S)) + (21 - (C.pc (B.tr Y) + (B.st Y).sum)) + Cls.outS S (B.st Y)) := by
  have hH := hC.unif
  by_cases hcap : B.tr X &&& B.tr Y &&& C.capS S ≠ 0
  · exact Or.inl hcap
  right
  push Not at hcap
  have hL := L6 hC (B.slot_mem S hX (q := 0) (by omega)) (B.slot_mem S hX (q := 1) (by omega))
    (B.slot_mem S hX (q := 2) (by omega)) (B.slot_mem S hX (q := 3) (by omega)) hX hY (by
      intro x h0 h1 h2 h3 hxX hxY
      obtain ⟨⟨q, r⟩, hp, hmq, hmr⟩ := subs_two S hS
      obtain ⟨hq, hr, hqr⟩ := pairs4_spec hp
      simp only at hq hr hqr hmq hmr
      have hin : ∀ s, s < 4 → x ∈ B.slot S X s := by
        intro s hs; rcases q4_cases hs with rfl | rfl | rfl | rfl <;> assumption
      have hP : ∀ s, s < 4 → Cls.mem S s = true → x ∈ B.P s := by
        intro s hs hm; have := hin s hs; simpa [slot, hm] using this
      obtain ⟨k, hk, rfl⟩ := B.two q r x hq hr hqr (hP q hq hmq) (hP r hr hmr)
      have hbit : ∀ s, s < 4 → (!Cls.mem S s || (C.P s).testBit k) = true := by
        intro s hs; cases hm : Cls.mem S s
        · rfl
        · simp only [Bool.not_true, Bool.false_or]; exact (B.P_bit hs hk).2 (hP s hs hm)
      have hbk : (B.tr X &&& B.tr Y &&& C.capS S).testBit k = true := by
        rw [Nat.testBit_and, Nat.testBit_and, capS_bit, hbit 0 (by omega), hbit 1 (by omega),
          hbit 2 (by omega), hbit 3 (by omega)]
        simp only [Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨(B.testBit_tr X k).2 ⟨hk, hxX⟩, (B.testBit_tr Y k).2 ⟨hk, hxY⟩⟩, hk⟩
      rw [hcap] at hbk; simp at hbk)
  have hXE : X ⊆ X ∪ Y := subset_union_left
  have hmE : ∀ i, i < C.n → (B.core i ∈ X ∪ Y ↔ (B.tr X ||| B.tr Y).testBit i = true) := by
    intro i hi; rw [Nat.testBit_or, B.bitT X hi, B.bitT Y hi]; simp
  have eU : B.slot S X 0 ∪ B.slot S X 1 ∪ B.slot S X 2 ∪ B.slot S X 3 ∪ X ∪ Y =
      B.slot S X 0 ∪ B.slot S X 1 ∪ B.slot S X 2 ∪ B.slot S X 3 ∪ (X ∪ Y) := by
    rw [union_assoc]
  rw [eU] at hL
  have hr := B.region (B.slot S X 0 ∪ B.slot S X 1 ∪ B.slot S X 2 ∪ B.slot S X 3 ∪ (X ∪ Y))
  rw [B.slotE_ci S hXE _ hmE, B.slotE_O hs hH S hXE (q := 0) (by omega), B.slotE_O hs hH S hXE (q := 1) (by omega),
    B.slotE_O hs hH S hXE (q := 2) (by omega), B.slotE_O hs hH S hXE (q := 3) (by omega),
    B.slotE_BU S hXE] at hr
  have hie := pc_ie (C := C) (B.tr X) (B.tr Y) (C.cupS S)
  obtain ⟨huX, -⟩ := B.u_eq hH hX
  obtain ⟨huY, -⟩ := B.u_eq hH hY
  have hUO : ∀ q, q < 4 → ((X ∪ Y) ∩ B.O q).card + (X ∩ Y ∩ B.O q).card = (X ∩ B.O q).card + (Y ∩ B.O q).card := by
    intro q hq
    have := card_union_add_card_inter (X ∩ B.O q) (Y ∩ B.O q)
    have e1 : X ∩ B.O q ∪ Y ∩ B.O q = (X ∪ Y) ∩ B.O q := by ext; simp only [mem_union, mem_inter]; tauto
    have e2 : X ∩ B.O q ∩ (Y ∩ B.O q) = X ∩ Y ∩ B.O q := by ext; simp only [mem_inter]; tauto
    rw [e1, e2] at this; exact this
  have hUB : ((X ∪ Y) \ B.BU).card + ((X ∩ Y) \ B.BU).card = (X \ B.BU).card + (Y \ B.BU).card := by
    have := card_union_add_card_inter (X \ B.BU) (Y \ B.BU)
    have e1 : X \ B.BU ∪ Y \ B.BU = (X ∪ Y) \ B.BU := by ext; simp only [mem_union, mem_sdiff]; tauto
    have e2 : X \ B.BU ∩ (Y \ B.BU) = (X ∩ Y) \ B.BU := by ext; simp only [mem_inter, mem_sdiff]; tauto
    rw [e1, e2] at this; exact this
  have u0 := hUO 0 (by omega); have u1 := hUO 1 (by omega)
  have u2 := hUO 2 (by omega); have u3 := hUO 3 (by omega)
  rw [osS_eq, outS_eq, outS_eq, outS_eq, B.st_get X 0 (by omega), B.st_get X 1 (by omega),
    B.st_get X 2 (by omega), B.st_get X 3 (by omega), B.st_get Y 0 (by omega), B.st_get Y 1 (by omega),
    B.st_get Y 2 (by omega), B.st_get Y 3 (by omega), B.st_get _ 0 (by omega), B.st_get _ 1 (by omega),
    B.st_get _ 2 (by omega), B.st_get _ 3 (by omega)]
  rw [← huX, ← huY]
  revert hr
  cases Cls.mem S 0 <;> cases Cls.mem S 1 <;> cases Cls.mem S 2 <;> cases Cls.mem S 3 <;>
    simp only [Bool.false_eq_true, if_false, if_true] <;> intro hr <;> omega

/-! ### pair rule (4): both edges singles of a base 5-pair -/

theorem pSAME_ok (hs : C.clsSane = true) (hC : Counter H) (hcls : CLSHyp C H) {X Y : Finset V} (hX : X ∈ H)
    (hY : Y ∈ H) : C.pSAME (B.tr X) (B.tr Y) (B.st (X ∩ Y)) ((X ∩ Y) \ B.BU).card = true := by
  unfold Cls.pSAME
  dsimp only
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨i, j⟩ := p
  obtain ⟨hi, hj, hij⟩ := pairs4_spec hp
  simp only at hi hj hij
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true]
  by_cases h5 : C.pc (C.P i &&& C.P j) = 5
  swap
  · exact Or.inl (Or.inl (Or.inl (Or.inl h5)))
  by_cases h1 : C.pc (B.tr X &&& (C.P i &&& C.P j)) = 1
  swap
  · exact Or.inl (Or.inl (Or.inl (Or.inr h1)))
  by_cases h2 : C.pc (B.tr Y &&& (C.P i &&& C.P j)) = 1
  swap
  · exact Or.inl (Or.inl (Or.inr h2))
  by_cases h3 : B.tr X &&& (C.P i &&& C.P j) = B.tr Y &&& (C.P i &&& C.P j)
  · exact Or.inl (Or.inr h3)
  right
  have hM : (B.P i ∩ B.P j).card = 5 := by rw [B.card_N hi hj hij]; exact h5
  obtain ⟨k1, hk1n, -, hX1⟩ := B.single_of_pc _ (fun x hx => B.inter_sub_cs hi hj hij (mem_inter.1 hx).2) _
    (fun k hk => B.bit_WN X hi hj k hk) h1
  obtain ⟨k2, hk2n, -, hY2⟩ := B.single_of_pc _ (fun x hx => B.inter_sub_cs hi hj hij (mem_inter.1 hx).2) _
    (fun k hk => B.bit_WN Y hi hj k hk) h2
  have hne : B.core k1 ≠ B.core k2 := by
    intro he
    apply h3
    apply Nat.eq_of_testBit_eq
    intro t
    by_cases ht : t < C.n
    · apply Bool.eq_iff_iff.2
      rw [← B.bit_WN X hi hj t ht, ← B.bit_WN Y hi hj t ht, hX1, hY2, he]
    · simp [Nat.testBit_and, Base.bit_big hs hi ht, B.bitT_big X ht, B.bitT_big Y ht]
  have hdis := Erdos616R21.S_a_O hC (B.P_mem i hi) (B.P_mem j hj) hX hY hM hX1 hY2 hne
  have out : ∀ x, x ∈ X → x ∈ Y → x ∉ B.P i → x ∉ B.P j → False := by
    intro x hxX hxY h3' h4'
    exact Finset.disjoint_left.1 hdis (mem_sdiff.2 ⟨hxX, by simp [h3', h4']⟩)
      (mem_sdiff.2 ⟨hxY, by simp [h3', h4']⟩)
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · apply Nat.eq_of_testBit_eq
    intro t
    rw [Nat.zero_testBit]
    by_cases ht : t < C.n
    · simp only [testBit_nd C _ _ t ht, Nat.testBit_and, Nat.testBit_or, B.bitP hi ht, B.bitP hj ht,
        B.bitT X ht, B.bitT Y ht]
      apply Bool.eq_false_iff.2
      intro h
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_true_eq,
        decide_eq_false_iff_not] at h
      exact out _ h.1.1 h.1.2 h.2.1 h.2.2
    · simp [Cls.nd, Nat.testBit_and, Nat.testBit_xor, Cls.full, Nat.testBit_two_pow_sub_one, ht, B.bitT_big X ht, B.bitT_big Y ht, Base.bit_big hs hi ht, Base.bit_big hs hj ht]
  · rw [card_eq_zero, eq_empty_iff_forall_notMem]
    intro x hx
    simp only [mem_sdiff, mem_inter] at hx
    have hPi : x ∉ B.P i := fun h => hx.2 (by
      simp only [BU, mem_union]; rcases q4_cases hi with rfl | rfl | rfl | rfl <;> tauto)
    have hPj : x ∉ B.P j := fun h => hx.2 (by
      simp only [BU, mem_union]; rcases q4_cases hj with rfl | rfl | rfl | rfl <;> tauto)
    exact out x hx.1.1 hx.1.2 hPi hPj
  · intro q hq
    simp only [Cls.q4, List.mem_cons, List.not_mem_nil, or_false] at hq
    have hq4 : q < 4 := by rcases hq with rfl | rfl | rfl | rfl <;> omega
    by_cases hqi : q = i
    · exact Or.inl (Or.inl hqi)
    by_cases hqj : q = j
    · exact Or.inl (Or.inr hqj)
    right
    rw [B.st_get _ q hq4, card_eq_zero, eq_empty_iff_forall_notMem]
    intro x hx
    simp only [mem_inter] at hx
    exact out x hx.1.1 hx.1.2 (B.O_excl hq4 hi hx.2 (Ne.symm hqi)) (B.O_excl hq4 hj hx.2 (Ne.symm hqj))
  · have hc := hcls _ (B.P_mem i hi) _ (B.P_mem j hj) _ hX _ hY hM _ _ hX1 hY2 hne
    rw [B.card_WPiPj (X ∩ Y) hi hj hij, B.card_WPiPj (X ∩ Y) hj hi (Ne.symm hij), B.tr_inter] at hc
    rw [B.st_get _ i hi, B.st_get _ j hj]
    exact hc

/-! ### pair rule (5): derived 5-pair `(P_k, A)` seen from `B'` -/

theorem foldl_skip (z : V4) {k : ℕ} (hk : k < 4) :
    Cls.q4.foldl (fun acc q => if q == k then acc else acc + z.get q) 0 + z.get k = z.sum := by
  rcases q4_cases hk with rfl | rfl | rfl | rfl <;> simp [Cls.q4, V4.get, V4.sum] <;> omega

/-- `|W ∖ P_k| = |w ∖ P_k| + |W ∖ BU| + Σ_{q ≠ k} |W ∩ O_q|` and `|W| = |W ∩ P_k| + |W ∖ P_k|` -/
theorem card_W_sdiff_P (W : Finset V) {k : ℕ} (hk : k < 4) :
    (W \ B.P k).card + (B.st W).get k = C.pc (C.nd (B.tr W) (C.P k)) + (W \ B.BU).card + (B.st W).sum := by
  have hr := B.region (W \ B.P k)
  have hci : (B.ci (W \ B.P k)).card = C.pc (C.nd (B.tr W) (C.P k)) := by
    apply B.card_ci_eq_pc
    intro t ht
    simp only [testBit_nd C _ _ t ht, B.bitP hk ht, B.bitT W ht, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_true_eq, decide_eq_false_iff_not, mem_sdiff]
  have hO : ∀ q, q < 4 → ((W \ B.P k) ∩ B.O q).card = if q = k then 0 else (W ∩ B.O q).card := by
    intro q hq
    split_ifs with hqk
    · subst hqk; rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro x hx; simp only [mem_inter, mem_sdiff, O] at hx; exact hx.1.2 hx.2.1
    · congr 1; ext x; simp only [mem_inter, mem_sdiff]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, B.O_excl hq hk h2 (fun e => hqk e.symm)⟩, h2⟩
  have hU : (W \ B.P k) \ B.BU = W \ B.BU := by
    ext x; simp only [mem_sdiff, BU, mem_union]
    rcases q4_cases hk with rfl | rfl | rfl | rfl <;> tauto
  rw [hci, hO 0 (by omega), hO 1 (by omega), hO 2 (by omega), hO 3 (by omega), hU] at hr
  rw [B.st_get W k hk]
  simp only [st, V4.sum]
  rcases q4_cases hk with rfl | rfl | rfl | rfl <;> simp at hr <;> omega

theorem pDer1_ok (hs : C.clsSane = true) (hC : Counter H) (hcls : CLSHyp C H) {A B' : Finset V} (hA : A ∈ H)
    (hB : B' ∈ H) :
    C.pDer1 (B.tr A) (B.st A) (B.tr B') (B.st B') (B.tr A &&& B.tr B') (B.st (A ∩ B'))
      ((A ∩ B') \ B.BU).card = true := by
  unfold Cls.pDer1
  dsimp only
  rw [List.all_eq_true]
  intro k hk
  simp only [Cls.q4, List.mem_cons, List.not_mem_nil, or_false] at hk
  have hk4 : k < 4 := by rcases hk with rfl | rfl | rfl | rfl <;> omega
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true]
  by_cases hx5 : C.xq (B.tr A) (B.st A) k = 5
  swap
  · exact Or.inl hx5
  right
  have hM : (B.P k ∩ A).card = 5 := by rw [inter_comm, ← B.xq_eq A hk4]; exact hx5
  set W := A ∩ B' with hW
  -- the two counts
  have hnB : C.pc (B.tr A &&& B.tr B' &&& C.P k) + (B.st W).get k = (B' ∩ (B.P k ∩ A)).card := by
    rw [← B.tr_inter, B.st_get W k hk4, ← B.card_XP W hk4]
    congr 1; ext x; simp only [mem_inter, hW]; tauto
  have hoff := B.card_W_sdiff_P W hk4
  have hfold := foldl_skip (B.st W) hk4
  have hWk : (W \ B.P k).card = ((B' ∩ A) \ B.P k).card := by
    congr 1; ext x; simp only [mem_inter, mem_sdiff, hW]; tauto
  have hparts := Erdos616R21.card_sdiff_eq (B' ∩ A) (B.P k)
  have hBA : B' ∩ A ∩ B.P k = B' ∩ (B.P k ∩ A) := by ext x; simp only [mem_inter]; tauto
  rw [hBA] at hparts
  have htW : B.tr W = B.tr A &&& B.tr B' := B.tr_inter A B'
  rw [htW] at hoff
  have hfold' : Cls.q4.foldl (fun acc q => if q = k then acc else acc + (B.st W).get q) 0 + (B.st W).get k =
      (B.st W).sum := by
    rcases q4_cases hk4 with rfl | rfl | rfl | rfl <;> simp [Cls.q4, V4.get, V4.sum] <;> omega
  set offk := C.pc (C.nd (B.tr A &&& B.tr B') (C.P k)) + (W \ B.BU).card +
    Cls.q4.foldl (fun acc q => if q = k then acc else acc + (B.st W).get q) 0 with hoffk
  have hoffk' : offk = ((B' ∩ A) \ B.P k).card := by
    rw [hoffk]; omega
  refine ⟨?_, ?_⟩
  · -- D1
    by_cases h5 : 5 ≤ C.pc (B.tr A &&& B.tr B' &&& C.P k) + (B.st W).get k
    · exact Or.inl h5
    right
    have hlt : (B' ∩ (B.P k ∩ A)).card < (B.P k ∩ A).card := by rw [hM, ← hnB]; omega
    obtain ⟨x, hxN, hxB⟩ : ∃ x, x ∈ B.P k ∩ A ∧ x ∉ B' := by
      by_contra hno; push Not at hno
      have : B.P k ∩ A ⊆ B' ∩ (B.P k ∩ A) := fun x hx => mem_inter.2 ⟨hno x hx, hx⟩
      exact absurd (card_le_card this) (by omega)
    have hD := Erdos616R21.D1 hC (B.P_mem k hk4) hA hB hM hxN hxB
    have e : B' ∩ (B.P k ∪ A) = B' ∩ B.P k ∪ ((B' ∩ A) \ B.P k) := by
      ext x; simp only [mem_inter, mem_union, mem_sdiff]; tauto
    have hU := card_union_add_card_inter (B' ∩ B.P k) ((B' ∩ A) \ B.P k)
    have e2 : B' ∩ B.P k ∩ ((B' ∩ A) \ B.P k) = ∅ := by
      ext x; simp only [mem_inter, mem_sdiff, Finset.notMem_empty, iff_false]; tauto
    rw [e2, card_empty, add_zero, ← e] at hU
    rw [B.xq_eq B' hk4]
    omega
  · by_cases h1 : C.pc (B.tr A &&& B.tr B' &&& C.P k) + (B.st W).get k = 1
    swap
    · exact Or.inl h1
    right
    have h1' : (B' ∩ (B.P k ∩ A)).card = 1 := by rw [← hnB]; exact h1
    obtain ⟨x, hx⟩ := card_eq_one.1 h1'
    obtain ⟨hBk, hBA5, -⟩ := Erdos616R21.single_card hC (B.P_mem k hk4) hA hB hM hx
    have hxB : x ∈ B' := by have := mem_singleton_self x; rw [← hx] at this; exact (mem_inter.1 this).1
    refine ⟨⟨by rw [B.xq_eq B' hk4]; exact hBk, by omega⟩, ?_⟩
    intro j hj
    simp only [Cls.q4, List.mem_cons, List.not_mem_nil, or_false] at hj
    have hj4 : j < 4 := by rcases hj with rfl | rfl | rfl | rfl <;> omega
    by_cases hjk : j = k
    · exact Or.inl hjk
    right
    by_cases hy1 : C.pc (B.tr A &&& C.P k &&& C.P j) = 1
    swap
    · exact Or.inl (Or.inl hy1)
    by_cases hyb : B.tr B' &&& (B.tr A &&& C.P k &&& C.P j) = 0
    swap
    · exact Or.inl (Or.inr hyb)
    right
    obtain ⟨t, htn, -, hy⟩ := B.single_of_pc (B.P j ∩ (B.P k ∩ A))
      (fun z hz => B.inter_sub_cs hj4 hk4 hjk (by simp only [mem_inter] at hz ⊢; exact ⟨hz.1, hz.2.1⟩)) _
      (fun t ht => by
        simp only [Nat.testBit_and, B.bitP hk4 ht, B.bitP hj4 ht, B.bitT A ht, Bool.and_eq_true,
          decide_eq_true_eq, mem_inter]; tauto) hy1
    have htB : B.core t ∉ B' := by
      intro h
      have : (B.tr B' &&& (B.tr A &&& C.P k &&& C.P j)).testBit t = true := by
        have hm : B.core t ∈ B.P j ∩ (B.P k ∩ A) := by rw [hy]; exact mem_singleton_self _
        simp only [mem_inter] at hm
        simp only [Nat.testBit_and, B.bitP hk4 htn, B.bitP hj4 htn, B.bitT A htn, B.bitT B' htn,
          Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨h, ⟨hm.2.2, hm.2.1⟩, hm.1⟩
      rw [hyb] at this; simp at this
    have hne : x ≠ B.core t := fun e => htB (e ▸ hxB)
    have hdis := Erdos616R21.S_a_O hC (B.P_mem k hk4) hA hB (B.P_mem j hj4) hM hx hy hne
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply Nat.eq_of_testBit_eq
      intro s
      rw [Nat.zero_testBit]
      by_cases hsn : s < C.n
      · simp only [testBit_nd C _ _ s hsn, Nat.testBit_and, B.bitP hj4 hsn, B.bitP hk4 hsn, B.bitT A hsn,
          B.bitT B' hsn]
        apply Bool.eq_false_iff.2
        intro h
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not] at h
        obtain ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩ := h
        exact Finset.disjoint_left.1 hdis (mem_sdiff.2 ⟨h1', by simp [h3', h4']⟩)
          (mem_sdiff.2 ⟨h2', by simp [h3', h4']⟩)
      · simp [Cls.nd, Nat.testBit_and, Nat.testBit_xor, Cls.full, Nat.testBit_two_pow_sub_one, hsn, B.bitT_big A hsn, B.bitT_big B' hsn, Base.bit_big hs hj4 hsn, Base.bit_big hs hk4 hsn]
    · rw [B.st_get B' j hj4, B.st_get W j hj4]
      congr 1
      ext z; simp only [mem_inter, hW]
      constructor
      · rintro ⟨hzB, hzO⟩
        refine ⟨⟨?_, hzB⟩, hzO⟩
        by_contra hzA
        have hzk : z ∉ B.P k := B.O_excl hj4 hk4 hzO (Ne.symm hjk)
        exact Finset.disjoint_left.1 hdis (mem_sdiff.2 ⟨hzB, by simp [hzk, hzA]⟩)
          (mem_sdiff.2 ⟨(mem_sdiff.1 hzO).1, by simp [hzk, hzA]⟩)
      · rintro ⟨⟨-, hzB⟩, hzO⟩; exact ⟨hzB, hzO⟩
    · have hc := hcls _ (B.P_mem k hk4) _ hA _ hB _ (B.P_mem j hj4) hM _ _ hx hy hne
      have ca : (B' ∩ B.P j ∩ (B.P k \ A)).card = C.pc (C.nd (B.tr B' &&& C.P j &&& C.P k) (B.tr A)) := by
        apply B.card_core_only _ (fun z hz => B.inter_sub_cs hj4 hk4 hjk (by
          simp only [mem_inter, mem_sdiff] at hz ⊢; exact ⟨hz.1.2, hz.2.1⟩))
        intro s hsn
        simp only [testBit_nd C _ _ s hsn, Nat.testBit_and, B.bitP hj4 hsn, B.bitP hk4 hsn, B.bitT A hsn,
          B.bitT B' hsn, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
          mem_inter, mem_sdiff]
        try tauto
      have cc : (B' ∩ B.P j ∩ (A \ B.P k)).card =
          C.pc (C.nd (B.tr A &&& B.tr B' &&& C.P j) (C.P k)) + (B.st W).get j := by
        rw [← B.tr_inter, B.st_get W j hj4, ← B.card_WPiPj W hj4 hk4 hjk]
        congr 1; ext z; simp only [mem_inter, mem_sdiff, hW]; tauto
      rw [← ca, ← cc]; exact hc

/-! ### pair rule (6): the derived 5-pair `(X, Y)` -/

theorem pDer2_ok (hs : C.clsSane = true) (hC : Counter H) (hcls : CLSHyp C H) {X Y : Finset V} (hX : X ∈ H)
    (hY : Y ∈ H) (h5 : (X ∩ Y).card = 5) :
    C.pDer2 (B.tr X) (B.st X) (B.tr Y) (B.st Y) (B.tr X &&& B.tr Y) (B.st (X ∩ Y)) = true := by
  unfold Cls.pDer2
  dsimp only
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    decide_eq_true_eq]
  have hnj : ∀ j, j < 4 → C.pc (B.tr X &&& B.tr Y &&& C.P j) + (B.st (X ∩ Y)).get j = (B.P j ∩ (X ∩ Y)).card := by
    intro j hj
    rw [← B.tr_inter, B.st_get _ j hj, ← B.card_XP (X ∩ Y) hj, inter_comm]
  refine ⟨?_, ?_⟩
  · intro j hj
    simp only [Cls.q4, List.mem_cons, List.not_mem_nil, or_false] at hj
    have hj4 : j < 4 := by rcases hj with rfl | rfl | rfl | rfl <;> omega
    rw [hnj j hj4, B.xq_eq X hj4, B.xq_eq Y hj4]
    refine ⟨?_, ?_⟩
    · by_cases h : 5 ≤ (B.P j ∩ (X ∩ Y)).card
      · exact Or.inl h
      right
      obtain ⟨x, hxN, hxj⟩ : ∃ x, x ∈ X ∩ Y ∧ x ∉ B.P j := by
        by_contra hno; push Not at hno
        have : X ∩ Y ⊆ B.P j ∩ (X ∩ Y) := fun x hx => mem_inter.2 ⟨hno x hx, hx⟩
        exact h (h5 ▸ card_le_card this)
      have hD := Erdos616R21.D1 hC hX hY (B.P_mem j hj4) h5 hxN hxj
      have hU := card_union_add_card_inter (X ∩ B.P j) (Y ∩ B.P j)
      have e1 : X ∩ B.P j ∪ Y ∩ B.P j = B.P j ∩ (X ∪ Y) := by ext; simp only [mem_union, mem_inter]; tauto
      have e2 : X ∩ B.P j ∩ (Y ∩ B.P j) = B.P j ∩ (X ∩ Y) := by ext; simp only [mem_inter]; tauto
      rw [e1, e2] at hU; omega
    · by_cases h1 : (B.P j ∩ (X ∩ Y)).card = 1
      · right
        obtain ⟨x, hx⟩ := card_eq_one.1 h1
        obtain ⟨hjX, hjY, -⟩ := Erdos616R21.single_card hC hX hY (B.P_mem j hj4) h5 hx
        rw [inter_comm X, inter_comm Y]; exact ⟨hjX, hjY⟩
      · exact Or.inl h1
  · intro p hp
    obtain ⟨j, k⟩ := p
    obtain ⟨hj4, hk4, hjk⟩ := pairs4_spec hp
    simp only at hj4 hk4 hjk
    rw [hnj j hj4, hnj k hk4]
    by_cases h1 : (B.P j ∩ (X ∩ Y)).card = 1
    swap
    · exact Or.inl (Or.inl (Or.inl h1))
    by_cases h2 : (B.P k ∩ (X ∩ Y)).card = 1
    swap
    · exact Or.inl (Or.inl (Or.inr h2))
    by_cases h3 : B.tr X &&& B.tr Y &&& (C.P j &&& C.P k) = 0
    swap
    · exact Or.inl (Or.inr h3)
    right
    obtain ⟨xj, hxj⟩ := card_eq_one.1 h1
    obtain ⟨xk, hxk⟩ := card_eq_one.1 h2
    have hne : xj ≠ xk := by
      intro he; subst he
      have hmj : xj ∈ B.P j ∩ (X ∩ Y) := by rw [hxj]; exact mem_singleton_self _
      have hmk : xj ∈ B.P k ∩ (X ∩ Y) := by rw [hxk]; exact mem_singleton_self _
      simp only [mem_inter] at hmj hmk
      obtain ⟨t, htn, rfl⟩ := B.two j k xj hj4 hk4 hjk hmj.1 hmk.1
      have : (B.tr X &&& B.tr Y &&& (C.P j &&& C.P k)).testBit t = true := by
        simp only [Nat.testBit_and, B.bitP hj4 htn, B.bitP hk4 htn, B.bitT X htn, B.bitT Y htn,
          Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hmj.2.1, hmj.2.2⟩, hmj.1, hmk.1⟩
      rw [h3] at this; simp at this
    have hdis := Erdos616R21.S_a_O hC hX hY (B.P_mem j hj4) (B.P_mem k hk4) h5 hxj hxk hne
    refine ⟨?_, ?_⟩
    · apply Nat.eq_of_testBit_eq
      intro s
      rw [Nat.zero_testBit]
      by_cases hsn : s < C.n
      · simp only [testBit_nd C _ _ s hsn, Nat.testBit_and, Nat.testBit_or, B.bitP hj4 hsn, B.bitP hk4 hsn,
          B.bitT X hsn, B.bitT Y hsn]
        apply Bool.eq_false_iff.2
        intro h
        simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_true_eq,
          decide_eq_false_iff_not] at h
        obtain ⟨⟨h1', h2'⟩, h3', h4'⟩ := h
        exact Finset.disjoint_left.1 hdis (mem_sdiff.2 ⟨h1', by simp [h3', h4']⟩)
          (mem_sdiff.2 ⟨h2', by simp [h3', h4']⟩)
      · simp [Cls.nd, Nat.testBit_and, Nat.testBit_xor, Cls.full, Nat.testBit_two_pow_sub_one, hsn, B.bitT_big X hsn, B.bitT_big Y hsn, Base.bit_big hs hj4 hsn, Base.bit_big hs hk4 hsn]
    · have hc := hcls _ hX _ hY _ (B.P_mem j hj4) _ (B.P_mem k hk4) h5 _ _ hxj hxk hne
      have ca : (B.P j ∩ B.P k ∩ (X \ Y)).card = C.pc (C.nd (C.P j &&& C.P k &&& B.tr X) (B.tr Y)) := by
        apply B.card_core_only _ (fun z hz => B.inter_sub_cs hj4 hk4 hjk (by
          simp only [mem_inter, mem_sdiff] at hz ⊢; exact hz.1))
        intro s hsn
        simp only [testBit_nd C _ _ s hsn, Nat.testBit_and, B.bitP hj4 hsn, B.bitP hk4 hsn, B.bitT X hsn,
          B.bitT Y hsn, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
          mem_inter, mem_sdiff]
        try tauto
      have cc : (B.P j ∩ B.P k ∩ (Y \ X)).card = C.pc (C.nd (C.P j &&& C.P k &&& B.tr Y) (B.tr X)) := by
        apply B.card_core_only _ (fun z hz => B.inter_sub_cs hj4 hk4 hjk (by
          simp only [mem_inter, mem_sdiff] at hz ⊢; exact hz.1))
        intro s hsn
        simp only [testBit_nd C _ _ s hsn, Nat.testBit_and, B.bitP hj4 hsn, B.bitP hk4 hsn, B.bitT X hsn,
          B.bitT Y hsn, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
          mem_inter, mem_sdiff]
        try tauto
      rw [← ca, ← cc]; exact hc

/-- **PairSound**: every pair of distinct non-base edges passes all pair rules at its true overlap vector. -/
theorem pairSound (hs : C.clsSane = true) (hC : Counter H) (hcls : CLSHyp C H) : B.PairSound := by
  intro X hX Y hY _ _ _
  unfold Cls.pairRules
  dsimp only
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq]
  refine ⟨⟨⟨⟨⟨⟨B.pA_ok hC hX hY, ?_⟩, ?_⟩, B.pSAME_ok hs hC hcls hX hY⟩, B.pDer1_ok hs hC hcls hX hY⟩, ?_⟩, ?_⟩
  · intro q hq
    simp only [Cls.q4, List.mem_cons, List.not_mem_nil, or_false] at hq
    exact B.pF1_ok hC hX hY (by rcases hq with rfl | rfl | rfl | rfl <;> omega)
  · intro S hS
    exact B.pL_ok hs hC hX hY S hS
  · have := B.pDer1_ok hs hC hcls hY hX
    rw [Nat.and_comm (B.tr Y), inter_comm Y X] at this
    exact this
  · by_cases h5 : C.pc (B.tr X &&& B.tr Y) + (B.st (X ∩ Y)).sum + ((X ∩ Y) \ B.BU).card = 5
    · right
      apply B.pDer2_ok hs hC hcls hX hY
      rw [B.card_parts, B.tr_inter]; exact h5
    · exact Or.inl h5

end Base

end Erdos616R21.NoK4
