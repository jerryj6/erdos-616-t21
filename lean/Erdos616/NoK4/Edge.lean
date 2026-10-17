import Erdos616.NoK4.Frame

/-!
# Rule soundness, part 1: helper lemmas and the per-edge rules (`EdgeSound`)
-/

open Finset TrCheck

namespace Erdos616R21.NoK4

variable {V : Type*} [DecidableEq V] {C : Cls} {H : Finset (Finset V)}

/-- The lemma-side hypothesis on cross-type singles used by `cls_ok`: at every 5-pair `(X, Y)` of `H` and singles
`Z1, Z2` of different types, `cls_ok(|Z1 ∩ Z2 ∩ (X ∖ Y)|, |Z1 ∩ Z2 ∩ (Y ∖ X)|)`. For flags `0` this packages W7-I
(`a, c ≥ 2`), NK (`a + c ≥ 6`), N24 (`(a,c) ∉ {(2,4),(4,2)}`) and S(a)/S(b) (`a, c ≥ 1`, `a + c ≥ 5`). -/
def CLSHyp (C : Cls) (H : Finset (Finset V)) : Prop :=
  ∀ X ∈ H, ∀ Y ∈ H, ∀ Z1 ∈ H, ∀ Z2 ∈ H, (X ∩ Y).card = 5 → ∀ v w : V, Z1 ∩ (X ∩ Y) = {v} →
    Z2 ∩ (X ∩ Y) = {w} → v ≠ w → C.clsOk (Z1 ∩ Z2 ∩ (X \ Y)).card (Z1 ∩ Z2 ∩ (Y \ X)).card = true

theorem L5 (hC : Counter H) {a b c d e : Finset V} (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) (hd : d ∈ H)
    (he : e ∈ H) (h : ∀ x, x ∈ a → x ∈ b → x ∈ c → x ∈ d → x ∈ e → False) :
    61 ≤ (a ∪ b ∪ c ∪ d ∪ e).card := by
  have := (Erdos616R21.propL_iff_span H 60).1 hC.propL {a, b, c, d, e}
    (by simp [insert_subset_iff, ha, hb, hc, hd, he]) (by simp)
    (fun x => by
      by_contra hx; push Not at hx
      exact h x (hx a (by simp)) (hx b (by simp)) (hx c (by simp)) (hx d (by simp)) (hx e (by simp)))
  have e' : ({a, b, c, d, e} : Finset (Finset V)).biUnion id = a ∪ b ∪ c ∪ d ∪ e := by
    ext; simp <;> tauto
  rw [e'] at this; omega

theorem L6 (hC : Counter H) {a b c d e f : Finset V} (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) (hd : d ∈ H)
    (he : e ∈ H) (hf : f ∈ H) (h : ∀ x, x ∈ a → x ∈ b → x ∈ c → x ∈ d → x ∈ e → x ∈ f → False) :
    61 ≤ (a ∪ b ∪ c ∪ d ∪ e ∪ f).card := by
  have := (Erdos616R21.propL_iff_span H 60).1 hC.propL {a, b, c, d, e, f}
    (by simp [insert_subset_iff, ha, hb, hc, hd, he, hf]) (by simp)
    (fun x => by
      by_contra hx; push Not at hx
      exact h x (hx a (by simp)) (hx b (by simp)) (hx c (by simp)) (hx d (by simp)) (hx e (by simp))
        (hx f (by simp)))
  have e' : ({a, b, c, d, e, f} : Finset (Finset V)).biUnion id = a ∪ b ∪ c ∪ d ∪ e ∪ f := by
    ext; simp <;> tauto
  rw [e'] at this; omega

namespace Base

variable (B : Base C H)

theorem P_bit {q i : ℕ} (hq : q < 4) (hi : i < C.n) : (C.P q).testBit i = true ↔ B.core i ∈ B.P q :=
  (B.P_core q i hq hi).symm

theorem P_full (hs : C.clsSane = true) {q : ℕ} (hq : q < 4) : C.P q < 2 ^ C.n := by
  simp only [Cls.clsSane, Cls.q4, List.all_cons, List.all_nil, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, Bool.and_true] at hs
  have hpos : 0 < 2 ^ C.n := Nat.two_pow_pos _
  have : C.P q ≤ C.full := by rcases q4_cases hq with rfl | rfl | rfl | rfl <;> omega
  simp only [Cls.full] at this; omega

theorem P_bit_lt (hs : C.clsSane = true) {q i : ℕ} (hq : q < 4) (h : (C.P q).testBit i = true) : i < C.n := by
  by_contra hi
  have hlt : C.P q < 2 ^ i :=
    lt_of_lt_of_le (Base.P_full hs hq) (Nat.pow_le_pow_right (by omega) (by omega))
  rw [Nat.testBit_lt_two_pow hlt] at h; exact absurd h (by decide)

/-- a core-only set has the popcount of its mask as cardinality -/
theorem card_core_only (Z : Finset V) (hZ : Z ⊆ B.cs) (m : ℕ)
    (hm : ∀ i, i < C.n → (B.core i ∈ Z ↔ m.testBit i = true)) : Z.card = C.pc m := by
  have h1 := B.card_ci Z
  rw [inter_eq_left.2 hZ] at h1
  rw [← h1]; exact B.card_ci_eq_pc Z m hm

/-- points of two distinct base edges are core -/
theorem inter_sub_cs {q r : ℕ} (hq : q < 4) (hr : r < 4) (hqr : q ≠ r) : B.P q ∩ B.P r ⊆ B.cs := by
  intro x hx
  rw [mem_inter] at hx
  obtain ⟨i, hi, rfl⟩ := B.two q r x hq hr hqr hx.1 hx.2
  exact B.core_mem_cs hi

theorem mem_cs_iff' {x : V} : x ∈ B.cs ↔ ∃ i, i < C.n ∧ B.core i = x := B.mem_cs

/-- `|X ∩ P q| = |b ∧ P_q| + o_q` -/
theorem card_XP (X : Finset V) {q : ℕ} (hq : q < 4) :
    (X ∩ B.P q).card = C.pc (B.tr X &&& C.P q) + (X ∩ B.O q).card := by
  have h := Erdos616R21.card_sdiff_eq (X ∩ B.P q) B.cs
  have e1 : (X ∩ B.P q) \ B.cs = X ∩ B.O q := by
    ext x; simp only [mem_sdiff, mem_inter, O]; tauto
  have e2 : (X ∩ B.P q ∩ B.cs).card = C.pc (B.tr X &&& C.P q) := by
    apply B.card_core_only _ inter_subset_right
    intro i hi
    rw [Nat.testBit_and, Bool.and_eq_true, B.testBit_tr, B.P_bit hq hi]
    simp only [mem_inter, B.core_mem_cs hi, and_true]; tauto
  rw [e1, e2] at h; omega

theorem card_XO_le (hs : C.clsSane = true) (hH : ∀ e ∈ H, e.card = 21) (X : Finset V) {q : ℕ} (hq : q < 4) :
    (X ∩ B.O q).card ≤ C.OS q := by
  rw [← B.card_O hs q hq hH]
  exact card_le_card inter_subset_right

theorem xq_eq (X : Finset V) {q : ℕ} (hq : q < 4) : C.xq (B.tr X) (B.st X) q = (X ∩ B.P q).card := by
  rw [Cls.xq, B.st_get X q hq, B.card_XP X hq]

/-! ### generic facts on the mask helpers -/

theorem pc_split (m a : ℕ) : C.pc (m ||| a) = C.pc m + C.pc (C.nd a m) := by
  simp only [Cls.pc, pcK_eq]
  rw [← card_union_add_card_inter]
  have e1 : (range C.n).filter (fun i => (m ||| a).testBit i = true) =
      (range C.n).filter (fun i => m.testBit i = true) ∪ (range C.n).filter (fun i => (C.nd a m).testBit i = true) := by
    ext i; simp only [mem_filter, mem_range, mem_union, Nat.testBit_or, Bool.or_eq_true]
    constructor
    · rintro ⟨hi, h | h⟩
      · exact Or.inl ⟨hi, h⟩
      · by_cases hm : m.testBit i = true
        · exact Or.inl ⟨hi, hm⟩
        · exact Or.inr ⟨hi, by rw [testBit_nd C a m i hi]; simp_all⟩
    · rintro (⟨hi, h⟩ | ⟨hi, h⟩)
      · exact ⟨hi, Or.inl h⟩
      · rw [testBit_nd C a m i hi] at h; simp at h; exact ⟨hi, Or.inr h.1⟩
  have e2 : (range C.n).filter (fun i => m.testBit i = true) ∩ (range C.n).filter (fun i => (C.nd a m).testBit i = true) = ∅ := by
    ext i; simp only [mem_filter, mem_range, mem_inter, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hi, h1⟩, ⟨-, h2⟩⟩
    rw [testBit_nd C a m i hi] at h2; simp [h1] at h2
  rw [e1, e2, card_empty, add_zero]

theorem capS_bit (S i : ℕ) : (C.capS S).testBit i =
    (decide (i < C.n) && (!Cls.mem S 0 || (C.P 0).testBit i) && (!Cls.mem S 1 || (C.P 1).testBit i) &&
      (!Cls.mem S 2 || (C.P 2).testBit i) && (!Cls.mem S 3 || (C.P 3).testBit i)) := by
  unfold Cls.capS Cls.q4
  simp only [List.foldl_cons, List.foldl_nil]
  cases Cls.mem S 0 <;> cases Cls.mem S 1 <;> cases Cls.mem S 2 <;> cases Cls.mem S 3 <;>
    simp [Nat.testBit_and, Cls.full, Nat.testBit_two_pow_sub_one, Bool.and_assoc, Bool.and_comm,
      Bool.and_left_comm]

theorem cupS_bit (S i : ℕ) : (C.cupS S).testBit i =
    ((Cls.mem S 0 && (C.P 0).testBit i) || (Cls.mem S 1 && (C.P 1).testBit i) ||
      (Cls.mem S 2 && (C.P 2).testBit i) || (Cls.mem S 3 && (C.P 3).testBit i)) := by
  unfold Cls.cupS Cls.q4
  simp only [List.foldl_cons, List.foldl_nil]
  cases Cls.mem S 0 <;> cases Cls.mem S 1 <;> cases Cls.mem S 2 <;> cases Cls.mem S 3 <;>
    simp [Nat.testBit_or, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

theorem osS_eq (S : ℕ) : C.osS S = (if Cls.mem S 0 then C.OS 0 else 0) + (if Cls.mem S 1 then C.OS 1 else 0) +
    (if Cls.mem S 2 then C.OS 2 else 0) + (if Cls.mem S 3 then C.OS 3 else 0) := by
  unfold Cls.osS Cls.q4
  simp only [List.foldl_cons, List.foldl_nil]
  cases Cls.mem S 0 <;> cases Cls.mem S 1 <;> cases Cls.mem S 2 <;> cases Cls.mem S 3 <;> simp <;> omega

theorem outS_eq (S : ℕ) (v : V4) : Cls.outS S v = (if Cls.mem S 0 then 0 else v.get 0) +
    (if Cls.mem S 1 then 0 else v.get 1) + (if Cls.mem S 2 then 0 else v.get 2) +
    (if Cls.mem S 3 then 0 else v.get 3) := by
  unfold Cls.outS Cls.q4
  simp only [List.foldl_cons, List.foldl_nil]
  cases Cls.mem S 0 <;> cases Cls.mem S 1 <;> cases Cls.mem S 2 <;> cases Cls.mem S 3 <;> simp <;> omega

/-! ### the per-edge rules -/

theorem eBox_ok (hs : C.clsSane = true) (hH : ∀ e ∈ H, e.card = 21) {X : Finset V} (hX : X ∈ H) :
    C.eBox (B.tr X) (B.st X) = true := by
  unfold Cls.eBox
  simp only [Cls.q4, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  rotate_left 4
  · first | exact (B.u_eq hH hX).2 | exact decide_eq_true (B.u_eq hH hX).2
  · rw [B.st_get X 0 (by omega)]; exact B.card_XO_le hs hH X (q := 0) (by omega)
  · rw [B.st_get X 1 (by omega)]; exact B.card_XO_le hs hH X (q := 1) (by omega)
  · rw [B.st_get X 2 (by omega)]; exact B.card_XO_le hs hH X (q := 2) (by omega)
  · rw [B.st_get X 3 (by omega)]; exact B.card_XO_le hs hH X (q := 3) (by omega)

theorem eA_ok (hC : Counter H) {X : Finset V} (hX : X ∈ H) : C.eA (B.tr X) (B.st X) = true := by
  unfold Cls.eA
  simp only [Cls.q4, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [B.xq_eq X (q := 0) (by omega)]; exact Erdos616R21.inter_ge5 hC hX (B.P_mem 0 (by omega))
  · rw [B.xq_eq X (q := 1) (by omega)]; exact Erdos616R21.inter_ge5 hC hX (B.P_mem 1 (by omega))
  · rw [B.xq_eq X (q := 2) (by omega)]; exact Erdos616R21.inter_ge5 hC hX (B.P_mem 2 (by omega))
  · rw [B.xq_eq X (q := 3) (by omega)]; exact Erdos616R21.inter_ge5 hC hX (B.P_mem 3 (by omega))

/-- a nonzero mask from a witnessed bit -/
theorem ne_zero_of_bit {m k : ℕ} (h : m.testBit k = true) : m ≠ 0 := by
  rintro rfl; simp at h

theorem eF1_ok (hC : Counter H) {X : Finset V} (hX : X ∈ H) : C.eF1 (B.tr X) = true := by
  unfold Cls.eF1
  have key : ∀ i j, i < 4 → j < 4 → i ≠ j → (B.tr X &&& C.P i &&& C.P j != 0) = true := by
    intro i j hi hj hij
    obtain ⟨x, hxX, hxi, hxj⟩ := Erdos616R21.inter3 hC hX (B.P_mem i hi) (B.P_mem j hj)
    obtain ⟨k, hk, rfl⟩ := B.two i j x hi hj hij hxi hxj
    simp only [bne_iff_ne, ne_eq]
    apply ne_zero_of_bit (k := k)
    rw [Nat.testBit_and, Nat.testBit_and, Bool.and_eq_true, Bool.and_eq_true, B.testBit_tr, B.P_bit hi hk,
      B.P_bit hj hk]
    exact ⟨⟨⟨hk, hxX⟩, hxi⟩, hxj⟩
  simp only [Cls.pairs4, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨key 0 1 (by omega) (by omega) (by omega), key 0 2 (by omega) (by omega) (by omega),
    key 0 3 (by omega) (by omega) (by omega), key 1 2 (by omega) (by omega) (by omega),
    key 1 3 (by omega) (by omega) (by omega), key 2 3 (by omega) (by omega) (by omega)⟩

/-! ### L on `{S-edges, X}` -/

/-- the slot family: base edge `P q` for `q ∈ S`, otherwise the extra edge `X` -/
def slot (S : ℕ) (X : Finset V) (q : ℕ) : Finset V := if Cls.mem S q then B.P q else X

theorem slot_mem (S : ℕ) {X : Finset V} (hX : X ∈ H) {q : ℕ} (hq : q < 4) : B.slot S X q ∈ H := by
  unfold slot; split_ifs
  · exact B.P_mem q hq
  · exact hX

theorem subs_two : ∀ S ∈ Cls.subs, ∃ p ∈ Cls.pairs4, Cls.mem S p.1 = true ∧ Cls.mem S p.2 = true := by
  decide

theorem pairs4_spec {p : ℕ × ℕ} (hp : p ∈ Cls.pairs4) : p.1 < 4 ∧ p.2 < 4 ∧ p.1 ≠ p.2 := by
  simp only [Cls.pairs4, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- a point of `O q` lies in slot `r` iff (`r ∈ S` and `r = q`) or (`r ∉ S` and it lies in `X`) -/
theorem mem_slot_O (S : ℕ) (X : Finset V) {q r : ℕ} (hq : q < 4) (hr : r < 4) {x : V} (hx : x ∈ B.O q) :
    x ∈ B.slot S X r ↔ (Cls.mem S r = true ∧ r = q) ∨ (Cls.mem S r = false ∧ x ∈ X) := by
  unfold slot
  cases hm : Cls.mem S r
  · simp
  · simp only [if_true, true_and, Bool.true_eq_false, false_and, or_false]
    constructor
    · intro hxr; by_contra hrq; exact B.O_excl hq hr hx hrq hxr
    · rintro rfl; exact (mem_sdiff.1 hx).1

theorem slotU_O (hs : C.clsSane = true) (hH : ∀ e ∈ H, e.card = 21) (S : ℕ) (X : Finset V) {q : ℕ}
    (hq : q < 4) :
    ((B.slot S X 0 ∪ B.slot S X 1 ∪ B.slot S X 2 ∪ B.slot S X 3 ∪ X) ∩ B.O q).card =
      if Cls.mem S q then C.OS q else (X ∩ B.O q).card := by
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
      have key : ∀ r, r < 4 → x ∈ B.slot S X r → x ∈ X := by
        intro r hr hxr
        rcases (B.mem_slot_O S X hq hr hx).1 hxr with ⟨h1, rfl⟩ | ⟨-, h2⟩
        · exact absurd h1 hm
        · exact h2
      rcases h with ((((h | h) | h) | h) | h)
      · exact key 0 (by omega) h
      · exact key 1 (by omega) h
      · exact key 2 (by omega) h
      · exact key 3 (by omega) h
      · exact h
    · rintro ⟨h, hx⟩; exact ⟨Or.inr h, hx⟩

set_option maxHeartbeats 2000000 in
theorem slotU_ci (S : ℕ) (X : Finset V) :
    (B.ci (B.slot S X 0 ∪ B.slot S X 1 ∪ B.slot S X 2 ∪ B.slot S X 3 ∪ X)).card =
      C.pc (C.cupS S) + C.pc (C.nd (B.tr X) (C.cupS S)) := by
  rw [← pc_split]
  apply B.card_ci_eq_pc
  intro i hi
  rw [Nat.testBit_or, cupS_bit, Bool.or_eq_true]
  have h0 := B.P_bit (q := 0) (by omega) hi
  have h1 := B.P_bit (q := 1) (by omega) hi
  have h2 := B.P_bit (q := 2) (by omega) hi
  have h3 := B.P_bit (q := 3) (by omega) hi
  have hb := B.testBit_tr X i
  simp only [mem_union, slot]
  cases Cls.mem S 0 <;> cases Cls.mem S 1 <;> cases Cls.mem S 2 <;> cases Cls.mem S 3 <;>
    simp only [Bool.false_eq_true, if_false, if_true, Bool.false_and, Bool.true_and, Bool.false_or,
      Bool.or_false, Bool.or_eq_true, h0, h1, h2, h3, hb, hi, true_and] <;> tauto

set_option maxHeartbeats 2000000 in
theorem slotU_BU (S : ℕ) (X : Finset V) :
    (B.slot S X 0 ∪ B.slot S X 1 ∪ B.slot S X 2 ∪ B.slot S X 3 ∪ X) \ B.BU = X \ B.BU := by
  ext x; simp only [mem_sdiff, mem_union, slot, BU]
  cases Cls.mem S 0 <;> cases Cls.mem S 1 <;> cases Cls.mem S 2 <;> cases Cls.mem S 3 <;>
    simp only [Bool.false_eq_true, if_false, if_true] <;> tauto

set_option maxHeartbeats 1000000 in
theorem eL_ok (hs : C.clsSane = true) (hC : Counter H) {X : Finset V} (hX : X ∈ H) :
    C.eL (B.tr X) (B.st X) = true := by
  have hH := hC.unif
  unfold Cls.eL
  dsimp only
  rw [List.all_eq_true]
  intro S hS
  rw [Bool.or_eq_true]
  by_cases hcap : (B.tr X &&& C.capS S != 0) = true
  · exact Or.inl hcap
  right
  have hcap0 : B.tr X &&& C.capS S = 0 := by simpa using hcap
  have hL := L5 hC (B.slot_mem S hX (q := 0) (by omega)) (B.slot_mem S hX (q := 1) (by omega))
    (B.slot_mem S hX (q := 2) (by omega)) (B.slot_mem S hX (q := 3) (by omega)) hX (by
      intro x h0 h1 h2 h3 hxX
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
      have hbk : (B.tr X &&& C.capS S).testBit k = true := by
        rw [Nat.testBit_and, capS_bit, hbit 0 (by omega), hbit 1 (by omega), hbit 2 (by omega),
          hbit 3 (by omega)]
        simp only [Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨(B.testBit_tr X k).2 ⟨hk, hxX⟩, hk⟩
      rw [hcap0] at hbk; simp at hbk)
  have hr := B.region (B.slot S X 0 ∪ B.slot S X 1 ∪ B.slot S X 2 ∪ B.slot S X 3 ∪ X)
  rw [B.slotU_ci, B.slotU_O hs hH S X (q := 0) (by omega), B.slotU_O hs hH S X (q := 1) (by omega),
    B.slotU_O hs hH S X (q := 2) (by omega), B.slotU_O hs hH S X (q := 3) (by omega), B.slotU_BU] at hr
  obtain ⟨hu, -⟩ := B.u_eq hH hX
  rw [osS_eq, outS_eq, B.st_get X 0 (by omega), B.st_get X 1 (by omega), B.st_get X 2 (by omega),
    B.st_get X 3 (by omega)]
  rw [← hu]
  apply decide_eq_true
  revert hr
  cases Cls.mem S 0 <;> cases Cls.mem S 1 <;> cases Cls.mem S 2 <;> cases Cls.mem S 3 <;>
    simp only [Bool.false_eq_true, if_false, if_true] <;> intro hr <;> omega

/-! ### rules at a base 5-pair -/

theorem single_of_pc (Z : Finset V) (hZ : Z ⊆ B.cs) (m : ℕ)
    (hm : ∀ i, i < C.n → (B.core i ∈ Z ↔ m.testBit i = true)) (h1 : C.pc m = 1) :
    ∃ k, k < C.n ∧ m.testBit k = true ∧ Z = {B.core k} := by
  have hc := B.card_core_only Z hZ m hm
  rw [h1] at hc
  obtain ⟨x, rfl⟩ := card_eq_one.1 hc
  obtain ⟨k, hk, hxk⟩ := B.mem_cs.1 (hZ (mem_singleton_self x))
  subst hxk
  exact ⟨k, hk, (hm k hk).1 (mem_singleton_self _), rfl⟩

/-- core membership in `W ∩ (P i ∩ P j)` is the bit of `b ∧ P_i ∧ P_j` -/
theorem bit_WN (W : Finset V) {i j : ℕ} (hi : i < 4) (hj : j < 4) (k : ℕ) (hk : k < C.n) :
    B.core k ∈ W ∩ (B.P i ∩ B.P j) ↔ (B.tr W &&& (C.P i &&& C.P j)).testBit k = true := by
  rw [Nat.testBit_and, Nat.testBit_and, Bool.and_eq_true, Bool.and_eq_true, B.testBit_tr, B.P_bit hi hk,
    B.P_bit hj hk]
  simp only [mem_inter]; tauto

theorem card_N {i j : ℕ} (hi : i < 4) (hj : j < 4) (hij : i ≠ j) :
    (B.P i ∩ B.P j).card = C.pc (C.P i &&& C.P j) :=
  B.card_core_only _ (B.inter_sub_cs hi hj hij) _ (fun k hk => by
    rw [Nat.testBit_and, Bool.and_eq_true, B.P_bit hi hk, B.P_bit hj hk]; simp)

theorem card_WN (W : Finset V) {i j : ℕ} (hi : i < 4) (hj : j < 4) (hij : i ≠ j) :
    (W ∩ (B.P i ∩ B.P j)).card = C.pc (B.tr W &&& (C.P i &&& C.P j)) :=
  B.card_core_only _ (fun x hx => B.inter_sub_cs hi hj hij (mem_inter.1 hx).2) _
    (fun k hk => B.bit_WN W hi hj k hk)

/-- a mask that is not contained in `b` has a bit outside `b` -/
theorem exists_bit_not {b N : ℕ} (h : b &&& N ≠ N) : ∃ k, N.testBit k = true ∧ b.testBit k = false := by
  by_contra hno
  push Not at hno
  apply h
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and]
  cases hN : N.testBit k
  · simp
  · have := hno k hN; simp_all

/-- D1 at a base 5-pair for an edge `W` -/
theorem D1_base (hs : C.clsSane = true) (hC : Counter H) {W : Finset V} (hW : W ∈ H) {i j : ℕ} (hi : i < 4)
    (hj : j < 4) (hij : i ≠ j) (h5 : C.pc (C.P i &&& C.P j) = 5)
    (hbn : B.tr W &&& (C.P i &&& C.P j) ≠ C.P i &&& C.P j) :
    (W ∩ B.P i).card + (W ∩ B.P j).card ≤ 9 + C.pc (B.tr W &&& (C.P i &&& C.P j)) := by
  obtain ⟨k, hkN, hkb⟩ := exists_bit_not hbn
  have hkn : k < C.n := by
    rw [Nat.testBit_and, Bool.and_eq_true] at hkN; exact Base.P_bit_lt hs hi hkN.1
  have hM : (B.P i ∩ B.P j).card = 5 := by rw [B.card_N hi hj hij]; exact h5
  have hkM : B.core k ∈ B.P i ∩ B.P j := by
    rw [Nat.testBit_and, Bool.and_eq_true, B.P_bit hi hkn, B.P_bit hj hkn] at hkN
    exact mem_inter.2 hkN
  have hkW : B.core k ∉ W := by
    intro h; have := (B.testBit_tr W k).2 ⟨hkn, h⟩; rw [hkb] at this; exact absurd this (by decide)
  have hD := Erdos616R21.D1 hC (B.P_mem i hi) (B.P_mem j hj) hW hM hkM hkW
  have hU := card_union_add_card_inter (W ∩ B.P i) (W ∩ B.P j)
  have e1 : W ∩ B.P i ∪ W ∩ B.P j = W ∩ (B.P i ∪ B.P j) := by ext; simp only [mem_union, mem_inter]; tauto
  have e2 : W ∩ B.P i ∩ (W ∩ B.P j) = W ∩ (B.P i ∩ B.P j) := by ext; simp only [mem_inter]; tauto
  rw [e1, e2, B.card_WN W hi hj hij] at hU
  omega

theorem bitP {q k : ℕ} (hq : q < 4) (hk : k < C.n) : (C.P q).testBit k = decide (B.core k ∈ B.P q) := by
  apply Bool.eq_iff_iff.2; rw [B.P_bit hq hk]; simp

theorem bitT (X : Finset V) {k : ℕ} (hk : k < C.n) : (B.tr X).testBit k = decide (B.core k ∈ X) := by
  apply Bool.eq_iff_iff.2; rw [B.testBit_tr]; simp [hk]

/-- bits of a mask built from `P q`'s are zero beyond `n` -/
theorem bit_big (hs : C.clsSane = true) {q t : ℕ} (hq : q < 4) (ht : ¬ t < C.n) : (C.P q).testBit t = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (Base.P_full hs hq) (Nat.pow_le_pow_right (by omega) (by omega)))

theorem bitT_big (X : Finset V) {t : ℕ} (ht : ¬ t < C.n) : (B.tr X).testBit t = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (B.tr_lt X) (Nat.pow_le_pow_right (by omega) (by omega)))

theorem eBasePair_ok (hs : C.clsSane = true) (hC : Counter H) (hcls : CLSHyp C H) {X : Finset V}
    (hX : X ∈ H) {i j : ℕ} (hi : i < 4) (hj : j < 4) (hij : i ≠ j) :
    C.eBasePair (B.tr X) (B.st X) i j = true := by
  unfold Cls.eBasePair
  dsimp only
  by_cases h5 : C.pc (C.P i &&& C.P j) = 5
  swap
  · simp [h5]
  have hM : (B.P i ∩ B.P j).card = 5 := by rw [B.card_N hi hj hij]; exact h5
  rw [if_neg (by simp [h5])]
  rw [B.xq_eq X hi, B.xq_eq X hj]
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq]
  refine ⟨?_, ?_⟩
  · by_cases hbn : B.tr X &&& (C.P i &&& C.P j) = C.P i &&& C.P j
    · exact Or.inl hbn
    · exact Or.inr (B.D1_base hs hC hX hi hj hij h5 hbn)
  · by_cases h1 : C.pc (B.tr X &&& (C.P i &&& C.P j)) = 1
    swap
    · exact Or.inl h1
    right
    obtain ⟨k, hkn, -, hXk⟩ := B.single_of_pc _ (fun x hx => B.inter_sub_cs hi hj hij (mem_inter.1 hx).2) _
      (fun k hk => B.bit_WN X hi hj k hk) h1
    obtain ⟨hXi, hXj, -⟩ := Erdos616R21.single_card hC (B.P_mem i hi) (B.P_mem j hj) hX hM hXk
    refine ⟨⟨hXi, hXj⟩, ?_⟩
    have key : ∀ k', k' < 4 → k' ≠ i → k' ≠ j →
        (¬ C.pc (C.P k' &&& (C.P i &&& C.P j)) = 1 ∨ C.P k' &&& (C.P i &&& C.P j) = B.tr X &&& (C.P i &&& C.P j)) ∨
        ((C.nd (B.tr X &&& C.P k') (C.P i ||| C.P j) = 0 ∧ (B.st X).get k' = 0) ∧
          C.clsOk (C.pc (C.nd (B.tr X &&& C.P k' &&& C.P i) (C.P j)))
            (C.pc (C.nd (B.tr X &&& C.P k' &&& C.P j) (C.P i))) = true) := by
      intro k' hk' hki hkj
      by_cases hy1 : C.pc (C.P k' &&& (C.P i &&& C.P j)) = 1
      swap
      · exact Or.inl (Or.inl hy1)
      by_cases hyb : C.P k' &&& (C.P i &&& C.P j) = B.tr X &&& (C.P i &&& C.P j)
      · exact Or.inl (Or.inr hyb)
      right
      obtain ⟨m, hmn, -, hPm⟩ := B.single_of_pc (B.P k' ∩ (B.P i ∩ B.P j))
        (fun x hx => B.inter_sub_cs hi hj hij (mem_inter.1 hx).2) _
        (fun t ht => by
          simp only [Nat.testBit_and, B.bitP hk' ht, B.bitP hi ht, B.bitP hj ht, Bool.and_eq_true,
            decide_eq_true_eq, mem_inter]) hy1
      have hmk : m ≠ k := by
        intro hmk; subst hmk
        apply hyb
        apply Nat.eq_of_testBit_eq
        intro t
        by_cases ht : t < C.n
        · have e1 : B.core t ∈ B.P k' ∩ (B.P i ∩ B.P j) ↔ B.core t ∈ X ∩ (B.P i ∩ B.P j) := by
            rw [hPm, hXk]
          simp only [mem_inter] at e1
          apply Bool.eq_iff_iff.2
          simp only [Nat.testBit_and, B.bitP hk' ht, B.bitP hi ht, B.bitP hj ht, B.bitT X ht,
            Bool.and_eq_true, decide_eq_true_eq]
          exact e1
        · simp [Nat.testBit_and, Base.bit_big hs hk' ht, B.bitT_big X ht]
      have hvw : B.core m ≠ B.core k := fun h => hmk (B.core_inj _ _ hmn hkn h)
      have hdis := Erdos616R21.S_a_O hC (B.P_mem i hi) (B.P_mem j hj) hX (B.P_mem k' hk') hM hXk hPm
        (Ne.symm hvw)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · apply Nat.eq_of_testBit_eq
        intro t
        rw [Nat.zero_testBit]
        by_cases ht : t < C.n
        · simp only [testBit_nd C _ _ t ht, Nat.testBit_and, Nat.testBit_or, B.bitP hk' ht, B.bitP hi ht,
            B.bitP hj ht, B.bitT X ht]
          apply Bool.eq_false_iff.2
          intro h
          simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_true_eq,
            decide_eq_false_iff_not] at h
          obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
          exact Finset.disjoint_left.1 hdis (mem_sdiff.2 ⟨h1, by simp [h3, h4]⟩)
            (mem_sdiff.2 ⟨h2, by simp [h3, h4]⟩)
        · simp [Cls.nd, Nat.testBit_and, Nat.testBit_xor, Cls.full, Nat.testBit_two_pow_sub_one, ht, B.bitT_big X ht, Base.bit_big hs hi ht, Base.bit_big hs hj ht, Base.bit_big hs hk' ht]
      · rw [B.st_get X k' hk', card_eq_zero, eq_empty_iff_forall_notMem]
        intro x hx
        rw [mem_inter] at hx
        have h3 : x ∉ B.P i := B.O_excl hk' hi hx.2 (Ne.symm hki)
        have h4 : x ∉ B.P j := B.O_excl hk' hj hx.2 (Ne.symm hkj)
        have h2 : x ∈ B.P k' := (mem_sdiff.1 hx.2).1
        exact Finset.disjoint_left.1 hdis (mem_sdiff.2 ⟨hx.1, by simp [h3, h4]⟩)
          (mem_sdiff.2 ⟨h2, by simp [h3, h4]⟩)
      · have hc := hcls _ (B.P_mem i hi) _ (B.P_mem j hj) _ hX _ (B.P_mem k' hk') hM _ _ hXk hPm
          (Ne.symm hvw)
        have ca : (X ∩ B.P k' ∩ (B.P i \ B.P j)).card =
            C.pc (C.nd (B.tr X &&& C.P k' &&& C.P i) (C.P j)) := by
          apply B.card_core_only _ (fun x hx => B.inter_sub_cs hk' hi hki (by
            simp only [mem_inter, mem_sdiff] at hx ⊢; exact ⟨hx.1.2, hx.2.1⟩))
          intro t ht
          simp only [testBit_nd C _ _ t ht, Nat.testBit_and, B.bitP hk' ht, B.bitP hi ht, B.bitP hj ht,
            B.bitT X ht, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
            mem_inter, mem_sdiff]
          try tauto
        have cc : (X ∩ B.P k' ∩ (B.P j \ B.P i)).card =
            C.pc (C.nd (B.tr X &&& C.P k' &&& C.P j) (C.P i)) := by
          apply B.card_core_only _ (fun x hx => B.inter_sub_cs hk' hj hkj (by
            simp only [mem_inter, mem_sdiff] at hx ⊢; exact ⟨hx.1.2, hx.2.1⟩))
          intro t ht
          simp only [testBit_nd C _ _ t ht, Nat.testBit_and, B.bitP hk' ht, B.bitP hi ht, B.bitP hj ht,
            B.bitT X ht, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
            mem_inter, mem_sdiff]
          try tauto
        rw [← ca, ← cc]; exact hc
    simp only [Cls.q4, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq]
    have fk : ∀ k', k' < 4 → ((k' = i ∨ k' = j) ∨
        ((¬ C.pc (C.P k' &&& (C.P i &&& C.P j)) = 1 ∨ C.P k' &&& (C.P i &&& C.P j) = B.tr X &&& (C.P i &&& C.P j)) ∨
        ((C.nd (B.tr X &&& C.P k') (C.P i ||| C.P j) = 0 ∧ (B.st X).get k' = 0) ∧
          C.clsOk (C.pc (C.nd (B.tr X &&& C.P k' &&& C.P i) (C.P j)))
            (C.pc (C.nd (B.tr X &&& C.P k' &&& C.P j) (C.P i))) = true))) := by
      intro k' hk'
      by_cases h1 : k' = i
      · exact Or.inl (Or.inl h1)
      by_cases h2 : k' = j
      · exact Or.inl (Or.inr h2)
      exact Or.inr (key k' hk' h1 h2)
    exact ⟨fk 0 (by omega), fk 1 (by omega), fk 2 (by omega), fk 3 (by omega)⟩

/-! ### rules at a derived 5-pair `(P_i, X)` -/

/-- `|P_j ∩ (P_i ∪ X)| = |P_j ∧ P_i| + |b ∧ P_j ∖ P_i| + o_j` -/
theorem card_PjPiX (X : Finset V) {i j : ℕ} (hi : i < 4) (hj : j < 4) (hij : i ≠ j) :
    (B.P j ∩ (B.P i ∪ X)).card = C.pc (C.P j &&& C.P i) + C.pc (C.nd (B.tr X &&& C.P j) (C.P i)) +
      (X ∩ B.O j).card := by
  have hU := card_union_add_card_inter (B.P j ∩ B.P i) ((B.P j ∩ X) \ B.P i)
  have e1 : B.P j ∩ B.P i ∪ (B.P j ∩ X) \ B.P i = B.P j ∩ (B.P i ∪ X) := by
    ext x; simp only [mem_union, mem_inter, mem_sdiff]; tauto
  have e2 : B.P j ∩ B.P i ∩ ((B.P j ∩ X) \ B.P i) = ∅ := by
    ext x; simp only [mem_inter, mem_sdiff, Finset.notMem_empty, iff_false]; tauto
  rw [e1, e2, card_empty, add_zero] at hU
  have h1 : (B.P j ∩ B.P i).card = C.pc (C.P j &&& C.P i) := B.card_N hj hi (Ne.symm hij)
  have h2 := Erdos616R21.card_sdiff_eq ((B.P j ∩ X) \ B.P i) B.cs
  have e3 : ((B.P j ∩ X) \ B.P i) \ B.cs = X ∩ B.O j := by
    ext x; simp only [mem_sdiff, mem_inter, O]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, -⟩, h3⟩; exact ⟨h2, h1, h3⟩
    · rintro ⟨h2, h1, h3⟩
      exact ⟨⟨⟨h1, h2⟩, B.O_excl hj hi (by simp [O, h1, h3]) hij⟩, h3⟩
  have e4 : ((B.P j ∩ X) \ B.P i ∩ B.cs).card = C.pc (C.nd (B.tr X &&& C.P j) (C.P i)) := by
    apply B.card_core_only _ inter_subset_right
    intro t ht
    simp only [testBit_nd C _ _ t ht, Nat.testBit_and, B.bitP hi ht, B.bitP hj ht, B.bitT X ht,
      Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not, mem_inter, mem_sdiff,
      B.core_mem_cs ht, and_true]
    try tauto
  rw [e3, e4] at h2
  omega

theorem eDerived_ok (hs : C.clsSane = true) (hC : Counter H) (hcls : CLSHyp C H) {X : Finset V}
    (hX : X ∈ H) {i : ℕ} (hi : i < 4) :
    C.eDerived (B.tr X) (B.st X) i = true := by
  unfold Cls.eDerived
  dsimp only
  rw [Bool.or_eq_true]
  by_cases hx5 : C.xq (B.tr X) (B.st X) i = 5
  swap
  · left; simp [hx5]
  right
  have hM : (B.P i ∩ X).card = 5 := by rw [inter_comm, ← B.xq_eq X hi]; exact hx5
  -- core part of N = P_i ∩ X
  have bitN : ∀ (W : Finset V) (j t : ℕ), j < 4 → j ≠ i → t < C.n →
      (B.core t ∈ W ∩ (B.P i ∩ X) ↔ (B.tr W &&& (B.tr X &&& C.P i)).testBit t = true) := by
    intro W j t hj hji ht
    simp only [Nat.testBit_and, B.bitP hi ht, B.bitT X ht, B.bitT W ht, Bool.and_eq_true, decide_eq_true_eq,
      mem_inter]; tauto
  have trP : ∀ j t, j < 4 → (B.tr (B.P j)).testBit t = (C.P j).testBit t := by
    intro j t hj
    by_cases ht : t < C.n
    · rw [B.bitT _ ht, B.bitP hj ht]
    · rw [B.bitT_big _ ht, Base.bit_big hs hj ht]
  have trPm : ∀ j m, j < 4 → B.tr (B.P j) &&& m = C.P j &&& m := by
    intro j m hj; apply Nat.eq_of_testBit_eq; intro t; rw [Nat.testBit_and, Nat.testBit_and, trP j t hj]
  -- singles of (P_i, X)
  have single : ∀ j, j < 4 → j ≠ i → C.pc (C.P j &&& (B.tr X &&& C.P i)) = 1 →
      ∃ t, t < C.n ∧ (C.P j &&& (B.tr X &&& C.P i)).testBit t = true ∧ B.P j ∩ (B.P i ∩ X) = {B.core t} := by
    intro j hj hji h1
    have := B.single_of_pc (B.P j ∩ (B.P i ∩ X))
      (fun x hx => B.inter_sub_cs hj hi hji (by simp only [mem_inter] at hx ⊢; exact ⟨hx.1, hx.2.1⟩))
      (C.P j &&& (B.tr X &&& C.P i)) (fun t ht => by rw [← trPm j _ hj]; exact bitN _ j t hj hji ht) h1
    exact this
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨?_, ?_⟩
  · intro j hj
    simp only [Cls.q4, List.mem_cons, List.not_mem_nil, or_false] at hj
    have hj4 : j < 4 := by rcases hj with rfl | rfl | rfl | rfl <;> omega
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
    by_cases hji : j = i
    · exact Or.inl hji
    right
    refine ⟨?_, ?_⟩
    · -- D1 with L = P_j
      by_cases hin : (B.st X).get i = 0 ∧ C.nd (B.tr X &&& C.P i) (C.P j) = 0
      · exact Or.inl hin
      right
      have hx : ∃ x, x ∈ B.P i ∩ X ∧ x ∉ B.P j := by
        by_cases ho : (B.st X).get i = 0
        · have hnd : C.nd (B.tr X &&& C.P i) (C.P j) ≠ 0 := fun h => hin ⟨ho, h⟩
          obtain ⟨t, ht⟩ := Nat.exists_testBit_of_ne_zero hnd
          have htn : t < C.n := by
            by_contra htn; simp [Cls.nd, Nat.testBit_and, Nat.testBit_xor, Base.bit_big hs hi htn, B.bitT_big X htn] at ht
          simp only [testBit_nd C _ _ t htn, Nat.testBit_and, B.bitP hi htn, B.bitP hj4 htn, B.bitT X htn,
            Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not] at ht
          exact ⟨B.core t, mem_inter.2 ⟨ht.1.2, ht.1.1⟩, ht.2⟩
        · rw [B.st_get X i hi] at ho
          obtain ⟨x, hx⟩ := card_pos.1 (Nat.pos_of_ne_zero ho)
          rw [mem_inter] at hx
          exact ⟨x, mem_inter.2 ⟨(mem_sdiff.1 hx.2).1, hx.1⟩, B.O_excl hi hj4 hx.2 hji⟩
      obtain ⟨x, hxN, hxj⟩ := hx
      have hD := Erdos616R21.D1 hC (B.P_mem i hi) hX (B.P_mem j hj4) hM hxN hxj
      rw [B.card_PjPiX X hi hj4 (Ne.symm hji)] at hD
      rw [B.st_get X j hj4]; exact hD
    · by_cases h1 : C.pc (C.P j &&& (B.tr X &&& C.P i)) = 1
      · right
        obtain ⟨t, -, -, hy⟩ := single j hj4 hji h1
        obtain ⟨-, hjX, -⟩ := Erdos616R21.single_card hC (B.P_mem i hi) hX (B.P_mem j hj4) hM hy
        rw [B.xq_eq X hj4, inter_comm]; exact hjX
      · exact Or.inl h1
  · intro p hp
    obtain ⟨j, k⟩ := p
    obtain ⟨hj4, hk4, hjk⟩ := pairs4_spec hp
    simp only at hj4 hk4 hjk
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
    by_cases hji : j = i
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hji))))
    by_cases hki : k = i
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hki))))
    by_cases h1 : C.pc (C.P j &&& (B.tr X &&& C.P i)) = 1
    swap
    · exact Or.inl (Or.inl (Or.inl (Or.inr h1)))
    by_cases h2 : C.pc (C.P k &&& (B.tr X &&& C.P i)) = 1
    swap
    · exact Or.inl (Or.inl (Or.inr h2))
    by_cases h3 : C.P j &&& C.P k &&& (B.tr X &&& C.P i) = 0
    swap
    · exact Or.inl (Or.inr h3)
    right
    obtain ⟨t1, ht1n, ht1, hy1⟩ := single j hj4 hji h1
    obtain ⟨t2, ht2n, ht2, hy2⟩ := single k hk4 hki h2
    have ht12 : B.core t1 ≠ B.core t2 := by
      intro he
      have := B.core_inj _ _ ht1n ht2n he
      subst this
      have : (C.P j &&& C.P k &&& (B.tr X &&& C.P i)).testBit t1 = true := by
        simp only [Nat.testBit_and, Bool.and_eq_true] at ht1 ht2 ⊢
        exact ⟨⟨ht1.1, ht2.1⟩, ht1.2⟩
      rw [h3] at this; simp at this
    have hdis := Erdos616R21.S_a_O hC (B.P_mem i hi) hX (B.P_mem j hj4) (B.P_mem k hk4) hM hy1 hy2 ht12
    refine ⟨?_, ?_⟩
    · apply Nat.eq_of_testBit_eq
      intro t
      rw [Nat.zero_testBit]
      by_cases ht : t < C.n
      · simp only [testBit_nd C _ _ t ht, Nat.testBit_and, B.bitP hj4 ht, B.bitP hk4 ht, B.bitP hi ht,
          B.bitT X ht]
        apply Bool.eq_false_iff.2
        intro h
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not] at h
        obtain ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩ := h
        exact Finset.disjoint_left.1 hdis (mem_sdiff.2 ⟨h1', by simp [h3', h4']⟩)
          (mem_sdiff.2 ⟨h2', by simp [h3', h4']⟩)
      · simp [Cls.nd, Nat.testBit_and, Nat.testBit_xor, Cls.full, Nat.testBit_two_pow_sub_one, ht, B.bitT_big X ht, Base.bit_big hs hi ht, Base.bit_big hs hj4 ht, Base.bit_big hs hk4 ht]
    · have hc := hcls _ (B.P_mem i hi) _ hX _ (B.P_mem j hj4) _ (B.P_mem k hk4) hM _ _ hy1 hy2 ht12
      have ca : (B.P j ∩ B.P k ∩ (B.P i \ X)).card = C.pc (C.nd (C.P j &&& C.P k &&& C.P i) (B.tr X)) := by
        apply B.card_core_only _ (fun x hx => B.inter_sub_cs hj4 hk4 hjk (by
          simp only [mem_inter, mem_sdiff] at hx ⊢; exact hx.1))
        intro t ht
        simp only [testBit_nd C _ _ t ht, Nat.testBit_and, B.bitP hj4 ht, B.bitP hk4 ht, B.bitP hi ht,
          B.bitT X ht, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
          mem_inter, mem_sdiff]
        try tauto
      have cc : (B.P j ∩ B.P k ∩ (X \ B.P i)).card = C.pc (C.nd (C.P j &&& C.P k &&& B.tr X) (C.P i)) := by
        apply B.card_core_only _ (fun x hx => B.inter_sub_cs hj4 hk4 hjk (by
          simp only [mem_inter, mem_sdiff] at hx ⊢; exact hx.1))
        intro t ht
        simp only [testBit_nd C _ _ t ht, Nat.testBit_and, B.bitP hj4 ht, B.bitP hk4 ht, B.bitP hi ht,
          B.bitT X ht, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
          mem_inter, mem_sdiff]
        try tauto
      rw [← ca, ← cc]; exact hc

/-- **EdgeSound**: every non-base edge passes all per-edge rules. -/
theorem edgeSound (hs : C.clsSane = true) (hC : Counter H) (hcls : CLSHyp C H) : B.EdgeSound := by
  intro X hX _
  unfold Cls.edgeOk
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨B.eBox_ok hs hC.unif hX, B.eA_ok hC hX⟩, B.eF1_ok hC hX⟩, B.eL_ok hs hC hX⟩, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨hi, hj, hij⟩ := pairs4_spec hp
    exact B.eBasePair_ok hs hC hcls hX hi hj hij
  · intro i hi
    simp only [Cls.q4, List.mem_cons, List.not_mem_nil, or_false] at hi
    exact B.eDerived_ok hs hC hcls hX (by rcases hi with rfl | rfl | rfl | rfl <;> omega)

end Base

end Erdos616R21.NoK4
