import Erdos616.Basic
import Erdos616Checkers.TrCheck

/-!
# Semantics for the trace checker (part 1): bits, base configuration, regions, traces, universe
-/

open Finset

namespace TrCheck

theorem pcK_eq : ∀ (k m : ℕ), pcK k m = ((range k).filter (fun i => m.testBit i = true)).card
  | 0, m => by simp [pcK]
  | k+1, m => by
    rw [pcK, pcK_eq k (m / 2), card_eq_sum_ones, sum_filter, card_eq_sum_ones, sum_filter, sum_range_succ']
    simp only [Nat.testBit_succ, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h] <;> omega

theorem testBit_nd (C : Cls) (a m i : ℕ) (hi : i < C.n) :
    (C.nd a m).testBit i = (a.testBit i && !m.testBit i) := by
  simp [Cls.nd, Cls.full, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, hi]

theorem V4.get_lt (v : V4) : v.get 0 = v.a0 ∧ v.get 1 = v.a1 ∧ v.get 2 = v.a2 ∧ v.get 3 = v.a3 :=
  ⟨rfl, rfl, rfl, rfl⟩

end TrCheck

namespace Erdos616R21.NoK4

open TrCheck

variable {V : Type*} [DecidableEq V]

/-- A labelled base configuration of class `C` inside `H`: core points `core i` (`i < n`), base edges `P q ∈ H`
(`q < 4`) whose core parts are given by the masks `C.P q`, and every point lying in two base edges is a core point. -/
structure Base (C : Cls) (H : Finset (Finset V)) where
  core : ℕ → V
  P : ℕ → Finset V
  core_inj : ∀ i j, i < C.n → j < C.n → core i = core j → i = j
  P_mem : ∀ q, q < 4 → P q ∈ H
  P_core : ∀ q i, q < 4 → i < C.n → (core i ∈ P q ↔ (C.P q).testBit i = true)
  two : ∀ q r x, q < 4 → r < 4 → q ≠ r → x ∈ P q → x ∈ P r → ∃ i, i < C.n ∧ core i = x

namespace Base

variable {C : Cls} {H : Finset (Finset V)} (B : Base C H)

/-- the core points -/
def cs : Finset V := (range C.n).image B.core
/-- private part of base edge `q` -/
def O (q : ℕ) : Finset V := B.P q \ B.cs
/-- the base span -/
def BU : Finset V := B.cs ∪ B.P 0 ∪ B.P 1 ∪ B.P 2 ∪ B.P 3
/-- core indices of `Z` -/
def ci (Z : Finset V) : Finset ℕ := (range C.n).filter (fun i => B.core i ∈ Z)

theorem mem_cs {x : V} : x ∈ B.cs ↔ ∃ i, i < C.n ∧ B.core i = x := by
  simp [cs]

theorem core_mem_cs {i : ℕ} (hi : i < C.n) : B.core i ∈ B.cs := B.mem_cs.2 ⟨i, hi, rfl⟩

theorem not_mem_O_of_core {i q : ℕ} (hi : i < C.n) : B.core i ∉ B.O q := by
  simp [O, B.core_mem_cs hi]

/-- a private point of `P q` lies in no other base edge -/
theorem O_excl {q r : ℕ} {x : V} (hq : q < 4) (hr : r < 4) (hx : x ∈ B.O q) (hrq : r ≠ q) : x ∉ B.P r := by
  intro hxr
  simp only [O, mem_sdiff] at hx
  obtain ⟨i, hi, rfl⟩ := B.two q r x hq hr (Ne.symm hrq) hx.1 hxr
  exact hx.2 (B.core_mem_cs hi)

theorem card_ci (Z : Finset V) : (B.ci Z).card = (Z ∩ B.cs).card := by
  have : Z ∩ B.cs = (B.ci Z).image B.core := by
    ext x; simp only [mem_inter, cs, mem_image, ci, mem_filter, mem_range]
    constructor
    · rintro ⟨hx, i, hi, rfl⟩; exact ⟨i, ⟨hi, hx⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hx⟩, rfl⟩; exact ⟨hx, i, hi, rfl⟩
  rw [this, card_image_of_injOn]
  intro i hi j hj h
  simp only [ci, coe_filter, mem_range, Set.mem_ofPred_eq] at hi hj
  exact B.core_inj i j hi.1 hj.1 h

/-- **Region decomposition**: core part + four private parts + outside part. -/
theorem region (Z : Finset V) :
    Z.card = (B.ci Z).card + (Z ∩ B.O 0).card + (Z ∩ B.O 1).card + (Z ∩ B.O 2).card +
      (Z ∩ B.O 3).card + (Z \ B.BU).card := by
  have h0 := Erdos616R21.card_sdiff_eq Z B.cs
  have h1 := Erdos616R21.card_sdiff_eq (Z \ B.cs) (B.P 0)
  have h2 := Erdos616R21.card_sdiff_eq ((Z \ B.cs) \ B.P 0) (B.P 1)
  have h3 := Erdos616R21.card_sdiff_eq (((Z \ B.cs) \ B.P 0) \ B.P 1) (B.P 2)
  have h4 := Erdos616R21.card_sdiff_eq ((((Z \ B.cs) \ B.P 0) \ B.P 1) \ B.P 2) (B.P 3)
  have e1 : (Z \ B.cs) ∩ B.P 0 = Z ∩ B.O 0 := by ext x; simp [O]; tauto
  have e2 : ((Z \ B.cs) \ B.P 0) ∩ B.P 1 = Z ∩ B.O 1 := by
    ext x; simp only [mem_inter, mem_sdiff, O]
    constructor
    · rintro ⟨⟨⟨hz, hc⟩, -⟩, h⟩; exact ⟨hz, h, hc⟩
    · rintro ⟨hz, h, hc⟩
      exact ⟨⟨⟨hz, hc⟩, B.O_excl (q := 1) (r := 0) (by omega) (by omega) (by simp [O, h, hc]) (by omega)⟩, h⟩
  have e3 : (((Z \ B.cs) \ B.P 0) \ B.P 1) ∩ B.P 2 = Z ∩ B.O 2 := by
    ext x; simp only [mem_inter, mem_sdiff, O]
    constructor
    · rintro ⟨⟨⟨⟨hz, hc⟩, -⟩, -⟩, h⟩; exact ⟨hz, h, hc⟩
    · rintro ⟨hz, h, hc⟩
      have hO : x ∈ B.O 2 := by simp [O, h, hc]
      exact ⟨⟨⟨⟨hz, hc⟩, B.O_excl (r := 0) (by omega) (by omega) hO (by omega)⟩,
        B.O_excl (r := 1) (by omega) (by omega) hO (by omega)⟩, h⟩
  have e4 : ((((Z \ B.cs) \ B.P 0) \ B.P 1) \ B.P 2) ∩ B.P 3 = Z ∩ B.O 3 := by
    ext x; simp only [mem_inter, mem_sdiff, O]
    constructor
    · rintro ⟨⟨⟨⟨⟨hz, hc⟩, -⟩, -⟩, -⟩, h⟩; exact ⟨hz, h, hc⟩
    · rintro ⟨hz, h, hc⟩
      have hO : x ∈ B.O 3 := by simp [O, h, hc]
      exact ⟨⟨⟨⟨⟨hz, hc⟩, B.O_excl (r := 0) (by omega) (by omega) hO (by omega)⟩,
        B.O_excl (r := 1) (by omega) (by omega) hO (by omega)⟩,
        B.O_excl (r := 2) (by omega) (by omega) hO (by omega)⟩, h⟩
  have e5 : (((((Z \ B.cs) \ B.P 0) \ B.P 1) \ B.P 2) \ B.P 3) = Z \ B.BU := by
    ext x; simp [BU]; tauto
  rw [e1] at h1; rw [e2] at h2; rw [e3] at h3; rw [e4] at h4; rw [e5] at h4
  rw [B.card_ci]; omega

/-! ### traces -/

end Base

/-- the trace of `X` on the first `k` points of `core`, as a bitmask -/
def trK (core : ℕ → V) (X : Finset V) : ℕ → ℕ
  | 0 => 0
  | k+1 => trK core X k ||| (if core k ∈ X then 2 ^ k else 0)

theorem testBit_trK (core : ℕ → V) (X : Finset V) :
    ∀ k j, (trK core X k).testBit j = (decide (j < k) && decide (core j ∈ X))
  | 0, j => by simp [trK]
  | k+1, j => by
    rw [trK, Nat.testBit_or, testBit_trK core X k j]
    by_cases hk : core k ∈ X
    · simp only [hk, ite_true, Nat.testBit_two_pow]
      by_cases hjk : j = k
      · subst hjk; simp [hk]
      · have : k ≠ j := fun h => hjk h.symm
        simp only [this, decide_false, Bool.or_false]
        by_cases hj : j < k
        · simp [hj, show j < k + 1 by omega]
        · simp [hj, show ¬ j < k + 1 by omega]
    · simp only [hk, ite_false, Nat.zero_testBit, Bool.or_false]
      by_cases hjk : j = k
      · subst hjk; simp [hk]
      · by_cases hj : j < k
        · simp [hj, show j < k + 1 by omega]
        · simp [hj, show ¬ j < k + 1 by omega]

theorem q4_cases {q : ℕ} (hq : q < 4) : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega

namespace Base
variable {C : Cls} {H : Finset (Finset V)} (B : Base C H)

/-- the core trace of an edge -/
def tr (X : Finset V) : ℕ := trK B.core X C.n

theorem testBit_tr (X : Finset V) (j : ℕ) : (B.tr X).testBit j = true ↔ j < C.n ∧ B.core j ∈ X := by
  simp [tr, testBit_trK]

theorem tr_lt (X : Finset V) : B.tr X < 2 ^ C.n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have := B.testBit_tr X i
  cases h : (B.tr X).testBit i
  · rfl
  · exact absurd (this.1 h).1 (by omega)

/-- the state of an edge: sizes of its private parts -/
def st (X : Finset V) : V4 := ⟨(X ∩ B.O 0).card, (X ∩ B.O 1).card, (X ∩ B.O 2).card, (X ∩ B.O 3).card⟩

theorem st_get (X : Finset V) (q : ℕ) (hq : q < 4) : (B.st X).get q = (X ∩ B.O q).card := by
  rcases q4_cases hq with rfl | rfl | rfl | rfl <;> rfl

/-- card of a core-index set via popcount -/
theorem card_ci_eq_pc (Z : Finset V) (m : ℕ) (h : ∀ i, i < C.n → (B.core i ∈ Z ↔ m.testBit i = true)) :
    (B.ci Z).card = C.pc m := by
  rw [Cls.pc, pcK_eq]
  congr 1
  apply filter_congr
  intro i hi
  exact h i (mem_range.1 hi)

/-- private part sizes from the class data -/
theorem card_O (hs : C.clsSane = true) (q : ℕ) (hq : q < 4) (hH : ∀ e ∈ H, e.card = 21) :
    (B.O q).card = C.OS q := by
  have hr := B.region (B.P q)
  have h21 := hH _ (B.P_mem q hq)
  have hci : (B.ci (B.P q)).card = C.pc (C.P q) :=
    B.card_ci_eq_pc _ _ (fun i hi => B.P_core q i hq hi)
  have hsane : C.OS q + C.pc (C.P q) = 21 := by
    simp only [Cls.clsSane, Cls.q4, List.all_cons, List.all_nil, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hs
    rcases q4_cases hq with rfl | rfl | rfl | rfl <;> simp_all
  -- `P q ∩ O r` is `O q` for `r = q` and empty otherwise; `P q ⊆ BU`
  have hsub : ∀ r, r < 4 → (B.P q ∩ B.O r).card = if r = q then (B.O q).card else 0 := by
    intro r hr
    split_ifs with hrq
    · subst hrq; congr 1; ext x; simp only [mem_inter, O, mem_sdiff]; tauto
    · rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro x hx
      rw [mem_inter] at hx
      exact B.O_excl hr hq hx.2 (Ne.symm hrq) hx.1
  have hU : B.P q \ B.BU = ∅ := by
    rw [sdiff_eq_empty_iff_subset]
    intro x hx; simp only [BU, mem_union]
    rcases q4_cases hq with rfl | rfl | rfl | rfl <;> tauto
  rw [hU, card_empty, hci, hsub 0 (by omega), hsub 1 (by omega), hsub 2 (by omega),
    hsub 3 (by omega)] at hr
  rcases q4_cases hq with rfl | rfl | rfl | rfl <;> simp at hr <;> omega

end Base

end Erdos616R21.NoK4
