import Erdos616.NoK4.Base

/-!
# Semantics for the trace checker (part 2): the assignment, clause soundness, symmetry, leaf theorem
modulo the two rule-soundness statements `EdgeSound` / `PairSound`.
-/

open Finset TrCheck

namespace Erdos616R21.NoK4

variable {V : Type*} [DecidableEq V] {C : Cls} {H : Finset (Finset V)}

/-! ### facts about the executable checker -/

theorem mem_states {b : ℕ} {o : V4} (h : C.edgeOk b o = true) : o ∈ C.states b := by
  obtain ⟨a0, a1, a2, a3⟩ := o
  have h0 := h
  simp only [Cls.edgeOk, Bool.and_eq_true] at h
  have hbox := h.1.1.1.1.1
  have hA := h.1.1.1.1.2
  simp only [Cls.eBox, Cls.q4, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq, V4.get, V4.sum, Cls.OS] at hbox
  simp only [Cls.eA, Cls.q4, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq, V4.get, Cls.xq] at hA
  have hsum := of_decide_eq_true hbox.2
  simp only [Cls.states, Cls.lo, Cls.OS]
  rw [List.mem_flatMap]
  refine ⟨a0, List.mem_range'_1.2 ⟨by omega, by omega⟩, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨a1, List.mem_range'_1.2 ⟨by omega, by omega⟩, ?_⟩
  rw [if_neg (by omega), List.mem_flatMap]
  refine ⟨a2, List.mem_range'_1.2 ⟨by omega, by omega⟩, ?_⟩
  rw [if_neg (by omega), List.mem_filterMap]
  refine ⟨a3, List.mem_range'_1.2 ⟨by omega, by omega⟩, ?_⟩
  rw [if_pos h0]

theorem mem_univ {p : ℕ × List V4} : p ∈ C.univ ↔ p.1 < 2 ^ C.n ∧ p.2 = C.states p.1 ∧ p.2 ≠ [] := by
  obtain ⟨b, l⟩ := p
  simp only [Cls.univ, List.mem_filter, List.mem_map, List.mem_range, Prod.mk.injEq,
    Bool.not_eq_true', List.isEmpty_eq_false_iff]
  constructor
  · rintro ⟨⟨b', hb', rfl, rfl⟩, h⟩; exact ⟨hb', rfl, h⟩
  · rintro ⟨hb, rfl, h⟩; exact ⟨⟨b, hb, rfl, rfl⟩, h⟩

theorem univ_nodup : (C.univ.map Prod.fst).Nodup := by
  simp only [Cls.univ, List.filter_map, List.map_map]
  have : (Prod.fst ∘ fun b => (b, C.states b)) = id := rfl
  rw [this, List.map_id]
  exact (List.nodup_range).filter _

theorem univ_fst_inj {i j : ℕ} (hi : i < C.univ.length) (hj : j < C.univ.length)
    (h : (C.univ[i]).1 = (C.univ[j]).1) : i = j := by
  have hn := univ_nodup (C := C)
  have h' : (C.univ.map Prod.fst)[i]'(by simpa using hi) = (C.univ.map Prod.fst)[j]'(by simpa using hj) := by
    simpa using h
  exact (List.Nodup.getElem_inj_iff hn).1 h'

theorem univ_get_snd {i : ℕ} (hi : i < C.univ.length) : (C.univ[i]).2 = C.states (C.univ[i]).1 :=
  (mem_univ.1 (List.getElem_mem hi)).2.1

theorem exists_univ_idx {b : ℕ} (hb : b < 2 ^ C.n) (hne : C.states b ≠ []) :
    ∃ i, ∃ h : i < C.univ.length, (C.univ[i]).1 = b := by
  have hm : (b, C.states b) ∈ C.univ := mem_univ.2 ⟨hb, rfl, hne⟩
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hm
  exact ⟨i, hi, by rw [he]⟩

theorem getD_toArray {i : ℕ} (hi : i < C.univ.length) (d : ℕ × List V4) :
    C.univ.toArray.getD i d = C.univ[i] := by
  simp [Array.getD, hi]

/-! ### the assignment -/

namespace Base

variable (B : Base C H)

/-- `X` is not one of the four base edges -/
def nonbase (X : Finset V) : Prop := ∀ q, q < 4 → X ≠ B.P q

/-- every non-base edge passes the per-edge rules -/
def EdgeSound : Prop := ∀ X ∈ H, B.nonbase X → C.edgeOk (B.tr X) (B.st X) = true

/-- every pair of distinct non-base edges passes the pair rules at its true overlap vector -/
def PairSound : Prop := ∀ X ∈ H, ∀ Y ∈ H, B.nonbase X → B.nonbase Y → X ≠ Y →
  C.pairRules (B.tr X) (B.st X) (B.tr Y) (B.st Y) (B.st (X ∩ Y)) ((X ∩ Y) \ B.BU).card = true

open Classical in
/-- **the assignment**: atom `i` is true iff some non-base edge has trace `univ[i]`. -/
noncomputable def asg : ℕ → Bool := fun i =>
  decide (∃ X ∈ H, B.nonbase X ∧ ∃ h : i < C.univ.length, B.tr X = (C.univ[i]).1)

theorem asg_true {i : ℕ} {X : Finset V} (hX : X ∈ H) (hnb : B.nonbase X) (hi : i < C.univ.length)
    (ht : B.tr X = (C.univ[i]).1) : B.asg i = true := by
  simp only [asg, decide_eq_true_eq]; exact ⟨X, hX, hnb, hi, ht⟩

theorem asg_spec {i : ℕ} (h : B.asg i = true) :
    ∃ X ∈ H, B.nonbase X ∧ ∃ hi : i < C.univ.length, B.tr X = (C.univ[i]).1 := by
  simpa [asg] using h

/-- the outside count of an edge equals the checker's `21 - (|b| + Σ o)` -/
theorem u_eq (hH : ∀ e ∈ H, e.card = 21) {X : Finset V} (hX : X ∈ H) :
    (X \ B.BU).card = 21 - (C.pc (B.tr X) + (B.st X).sum) ∧ C.pc (B.tr X) + (B.st X).sum ≤ 21 := by
  have hr := B.region X
  have hc := B.card_ci_eq_pc X (B.tr X) (fun i hi => by rw [B.testBit_tr]; tauto)
  rw [hH X hX, hc] at hr
  simp only [st, V4.sum]
  omega

/-! ### COV clauses -/

/-- an edge avoiding the core points of a needed mask `s` (from τ ≥ 5) -/
theorem exists_avoider (hs : C.clsSane = true) (hC : Counter H) (hE : B.EdgeSound) (s : ℕ)
    (hpc : C.pc s ≤ 4) (hP0 : s &&& C.P 0 ≠ 0) (hP1 : s &&& C.P 1 ≠ 0) (hP2 : s &&& C.P 2 ≠ 0)
    (hP3 : s &&& C.P 3 ≠ 0) :
    ∃ X ∈ H, B.nonbase X ∧ ∃ i, ∃ hi : i < C.univ.length, B.tr X = (C.univ[i]).1 ∧
      (C.univ[i]).1 &&& s = 0 := by
  set Bs : Finset V := ((range C.n).filter (fun i => s.testBit i = true)).image B.core with hBs
  have hcard : Bs.card ≤ 4 := by
    calc Bs.card ≤ ((range C.n).filter (fun i => s.testBit i = true)).card := card_image_le
      _ = C.pc s := by rw [Cls.pc, pcK_eq]
      _ ≤ 4 := hpc
  obtain ⟨X, hX, hdis⟩ := hC.avoid Bs hcard
  have hsane : ∀ q, q < 4 → C.P q ≤ C.full := by
    intro q hq
    simp only [Cls.clsSane, Cls.q4, List.all_cons, List.all_nil, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq, Bool.and_true] at hs
    rcases q4_cases hq with rfl | rfl | rfl | rfl <;> omega
  have hnb : B.nonbase X := by
    intro q hq hXq
    have hne : s &&& C.P q ≠ 0 := by
      rcases q4_cases hq with rfl | rfl | rfl | rfl
      · exact hP0
      · exact hP1
      · exact hP2
      · exact hP3
    obtain ⟨k, hk⟩ := Nat.exists_testBit_of_ne_zero hne
    rw [Nat.testBit_and, Bool.and_eq_true] at hk
    have hkn : k < C.n := by
      by_contra hkn
      have hlt : C.P q < 2 ^ k := lt_of_le_of_lt (hsane q hq)
        (lt_of_lt_of_le (by simp only [Cls.full]; exact Nat.sub_lt (Nat.two_pow_pos _) one_pos)
          (Nat.pow_le_pow_right (by omega) (by omega)))
      rw [Nat.testBit_lt_two_pow hlt] at hk; exact Bool.false_ne_true hk.2
    have h1 : B.core k ∈ Bs := mem_image.2 ⟨k, mem_filter.2 ⟨mem_range.2 hkn, hk.1⟩, rfl⟩
    have h2 : B.core k ∈ X := hXq ▸ (B.P_core q k hq hkn).2 hk.2
    exact Finset.disjoint_left.1 hdis h2 h1
  have hok := hE X hX hnb
  obtain ⟨i, hi, hti⟩ := exists_univ_idx (B.tr_lt X) (List.ne_nil_of_mem (mem_states hok))
  refine ⟨X, hX, hnb, i, hi, hti.symm, ?_⟩
  rw [hti]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, Nat.zero_testBit]
  cases h1 : (B.tr X).testBit k
  · rfl
  · cases h2 : s.testBit k
    · rfl
    · obtain ⟨hkn, hkX⟩ := (B.testBit_tr X k).1 h1
      exact absurd hkX (Finset.disjoint_right.1 hdis
        (mem_image.2 ⟨k, mem_filter.2 ⟨mem_range.2 hkn, h2⟩, rfl⟩))

theorem cov_sound (hs : C.clsSane = true) (hC : Counter H) (hE : B.EdgeSound) (cl : List ℕ) (s : ℕ)
    (h : C.covOkB C.univ.toArray cl s = true) : ∃ i ∈ cl, B.asg i = true := by
  simp only [Cls.covOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_filter,
    List.mem_range, beq_iff_eq, List.contains_iff_mem, Cls.q4, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, bne_iff_ne, ne_eq, List.size_toArray] at h
  obtain ⟨⟨hpc, hP0, hP1, hP2, hP3⟩, hall⟩ := h
  obtain ⟨X, hX, hnb, i, hi, hti, hav⟩ := B.exists_avoider hs hC hE s hpc hP0 hP1 hP2 hP3
  have hmem := hall i ⟨hi, by rw [getD_toArray hi]; exact hav⟩
  exact ⟨i, hmem, B.asg_true hX hnb hi hti⟩

end Base

end Erdos616R21.NoK4

namespace Erdos616R21.NoK4
open Finset TrCheck
variable {V : Type*} [DecidableEq V] {C : Cls} {H : Finset (Finset V)}
namespace Base
variable (B : Base C H)

/-! ### CONF clauses -/

theorem pairOk_of_rules (hs : C.clsSane = true) (hH : ∀ e ∈ H, e.card = 21) {X Y : Finset V}
    (hX : X ∈ H) (hY : Y ∈ H)
    (h : C.pairRules (B.tr X) (B.st X) (B.tr Y) (B.st Y) (B.st (X ∩ Y)) ((X ∩ Y) \ B.BU).card = true) :
    C.pairOk (B.tr X) (B.st X) (B.tr Y) (B.st Y) = true := by
  have hO : ∀ q, q < 4 → (X ∩ B.O q).card + (Y ∩ B.O q).card ≤ C.OS q + (X ∩ Y ∩ B.O q).card ∧
      (X ∩ Y ∩ B.O q).card ≤ (X ∩ B.O q).card ∧ (X ∩ Y ∩ B.O q).card ≤ (Y ∩ B.O q).card := by
    intro q hq
    have e1 := card_union_add_card_inter (X ∩ B.O q) (Y ∩ B.O q)
    have e2 : X ∩ B.O q ∩ (Y ∩ B.O q) = X ∩ Y ∩ B.O q := by
      ext x; simp only [mem_inter]; tauto
    have e3 : (X ∩ B.O q ∪ Y ∩ B.O q).card ≤ (B.O q).card :=
      card_le_card (fun x hx => by simp only [mem_inter, mem_union] at hx; tauto)
    rw [e2] at e1
    rw [B.card_O hs q hq hH] at e3
    refine ⟨by omega, card_le_card (fun x hx => by simp only [mem_inter] at hx ⊢; tauto),
      card_le_card (fun x hx => by simp only [mem_inter] at hx ⊢; tauto)⟩
  obtain ⟨u1, -⟩ := B.u_eq hH hX
  obtain ⟨u2, -⟩ := B.u_eq hH hY
  have hzu1 : ((X ∩ Y) \ B.BU).card ≤ (X \ B.BU).card :=
    card_le_card (fun x hx => by simp only [mem_inter, mem_sdiff] at hx ⊢; tauto)
  have hzu2 : ((X ∩ Y) \ B.BU).card ≤ (Y \ B.BU).card :=
    card_le_card (fun x hx => by simp only [mem_inter, mem_sdiff] at hx ⊢; tauto)
  obtain ⟨a0, b0, c0⟩ := hO 0 (by omega)
  obtain ⟨a1, b1, c1⟩ := hO 1 (by omega)
  obtain ⟨a2, b2, c2⟩ := hO 2 (by omega)
  obtain ⟨a3, b3, c3⟩ := hO 3 (by omega)
  simp only [st, V4.get, Cls.OS, V4.sum] at u1 u2 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3
  simp only [Cls.pairOk, Cls.rng, List.any_eq_true, List.mem_range'_1, List.mem_range]
  refine ⟨(X ∩ Y ∩ B.O 0).card, ⟨?_, ?_⟩, (X ∩ Y ∩ B.O 1).card, ⟨?_, ?_⟩, (X ∩ Y ∩ B.O 2).card, ⟨?_, ?_⟩,
    (X ∩ Y ∩ B.O 3).card, ⟨?_, ?_⟩, ((X ∩ Y) \ B.BU).card, ?_, ?_⟩
  all_goals first
    | (simp only [st, V4.get, Cls.OS, V4.sum]; omega)
    | (simp only [st, V4.get, Cls.OS, V4.sum] at h ⊢; convert h using 2)
    | skip

theorem conf_sound (hs : C.clsSane = true) (hH : ∀ e ∈ H, e.card = 21) (hE : B.EdgeSound) (hP : B.PairSound)
    {i j : ℕ} (hij : i ≠ j) (hi : i < C.univ.length) (hj : j < C.univ.length)
    (hc : C.compat (C.univ[i]) (C.univ[j]) = false) : B.asg i = false ∨ B.asg j = false := by
  by_contra hno
  simp only [not_or, Bool.not_eq_false] at hno
  obtain ⟨X, hX, hXnb, hi', hXt⟩ := B.asg_spec hno.1
  obtain ⟨Y, hY, hYnb, hj', hYt⟩ := B.asg_spec hno.2
  have hXY : X ≠ Y := by
    rintro rfl
    exact hij (univ_fst_inj hi hj (hXt.symm.trans hYt))
  have hpr := hP X hX Y hY hXnb hYnb hXY
  have hpo := B.pairOk_of_rules hs hH hX hY hpr
  have hsX : B.st X ∈ (C.univ[i]).2 := by
    rw [univ_get_snd hi, ← hXt]; exact mem_states (hE X hX hXnb)
  have hsY : B.st Y ∈ (C.univ[j]).2 := by
    rw [univ_get_snd hj, ← hYt]; exact mem_states (hE Y hY hYnb)
  have : C.compat (C.univ[i]) (C.univ[j]) = true := by
    simp only [Cls.compat, List.any_eq_true]
    exact ⟨_, hsX, _, hsY, by rw [← hXt, ← hYt]; exact hpo⟩
  rw [this] at hc; exact absurd hc (by decide)

/-! ### every checked clause is satisfied -/

theorem clause_sat (hs : C.clsSane = true) (hC : Counter H) (hE : B.EdgeSound) (hP : B.PairSound) (r : ℕ)
    (hr : ∃ X ∈ H, B.nonbase X ∧ ∃ h : r < C.univ.length, B.tr X = (C.univ[r]).1)
    (l : List (ℕ × Bool)) (hc : C.clauseOk C.univ.toArray r l = true) :
    l.any (fun p => B.asg p.1 == p.2) = true := by
  unfold Cls.clauseOk at hc
  split at hc
  · next hpos =>
    rw [List.all_eq_true] at hpos
    -- reduce to: some atom of `l` is true (all literals are positive)
    suffices hex : ∃ i ∈ l.map Prod.fst, B.asg i = true by
      obtain ⟨i, hi, hai⟩ := hex
      obtain ⟨⟨i', b⟩, hm, rfl⟩ := List.mem_map.1 hi
      have hb : b = true := by simpa using hpos _ hm
      subst hb
      exact List.any_eq_true.2 ⟨_, hm, by simp [hai]⟩
    rcases Bool.or_eq_true_iff.1 hc with hu | hcov
    · simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hu
      obtain ⟨hlen, hall⟩ := hu
      obtain ⟨p, hp⟩ : ∃ p, p ∈ l := List.exists_mem_of_length_pos (by omega)
      have hp1 : p.1 = r := by simpa using hall p hp
      obtain ⟨X, hX, hnb, hrl, ht⟩ := hr
      exact ⟨p.1, List.mem_map_of_mem hp, hp1 ▸ B.asg_true hX hnb hrl ht⟩
    · unfold Cls.covOk at hcov
      rcases Bool.or_eq_true_iff.1 hcov with h1 | h2
      · exact B.cov_sound hs hC hE _ _ h1
      · obtain ⟨s, -, hs'⟩ := List.any_eq_true.1 h2
        simp only [Bool.and_eq_true] at hs'
        exact B.cov_sound hs hC hE _ _ hs'.2
  · next hneg =>
    split at hc
    · next i j =>
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, Bool.not_eq_true',
        List.size_toArray] at hc
      obtain ⟨⟨⟨hij, hi⟩, hj⟩, hcomp⟩ := hc
      have hgi : C.univ.toArray[i]! = C.univ[i] := by
        simp [getElem!_pos C.univ.toArray i (by simpa using hi)]
      have hgj : C.univ.toArray[j]! = C.univ[j] := by
        simp [getElem!_pos C.univ.toArray j (by simpa using hj)]
      rw [hgi, hgj] at hcomp
      rcases B.conf_sound hs hC.unif hE hP hij hi hj hcomp with h | h
      · simp [h]
      · simp [h]
    · exact absurd hc (by decide)

end Base
end Erdos616R21.NoK4

namespace Erdos616R21.NoK4
open Finset TrCheck
variable {V : Type*} [DecidableEq V] {C : Cls} {H : Finset (Finset V)}

/-! ### symmetry: relabelling the base by an automorphism `(g, π)` -/

theorem testBit_permT_aux (t : ℕ) (L : List (ℕ × ℕ)) (init i : ℕ) :
    (L.foldl (fun acc (p : ℕ × ℕ) => if t.testBit p.2 then acc ||| (1 <<< p.1) else acc) init).testBit i =
      (init.testBit i || L.any (fun p => p.1 == i && t.testBit p.2)) := by
  induction L generalizing init with
  | nil => simp
  | cons p L ih =>
    rw [List.foldl_cons, ih]
    obtain ⟨k, gk⟩ := p
    rw [List.any_cons]
    by_cases h : t.testBit gk = true
    · rw [if_pos h, Nat.testBit_or, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, h, Bool.and_true]
      by_cases hk : k = i
      · subst hk; simp
      · have h1 : decide (k = i) = false := by simp [hk]
        have h2 : (k == i) = false := by simp [hk]
        rw [h1, h2]; simp
    · have h' : t.testBit gk = false := by simpa using h
      rw [if_neg h, h', Bool.and_false, Bool.false_or]

theorem testBit_permT (g : List ℕ) (t i : ℕ) :
    (Cls.permT g t).testBit i = true ↔ ∃ h : i < g.length, t.testBit (g[i]) = true := by
  have e : Cls.permT g t = ((List.range g.length).zip g).foldl
      (fun acc (p : ℕ × ℕ) => if t.testBit p.2 then acc ||| (1 <<< p.1) else acc) 0 := by
    unfold Cls.permT; congr 1
  rw [e, testBit_permT_aux]
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨k, gk⟩, hm, rfl, ht⟩
    obtain ⟨m, hm', he⟩ := List.mem_iff_getElem.1 hm
    simp only [List.length_zip, List.length_range, min_self] at hm'
    simp only [List.getElem_zip, List.getElem_range, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨hm', ht⟩
  · rintro ⟨hi, ht⟩
    refine ⟨(i, g[i]), ?_, rfl, ht⟩
    exact List.mem_iff_getElem.2 ⟨i, by simp [hi], by simp [List.getElem_zip, List.getElem_range]⟩

namespace Base
variable (B : Base C H)

/-- the relabelled base `core' i = core (g i)`, `P' q = P (π q)`. -/
def relabel (g π : List ℕ) (h : C.autOk g π = true) : Base C H := by
  simp only [Cls.autOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.or_eq_true, bne_iff_ne, ne_eq, Cls.q4, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hgl, hgn⟩, hginj⟩, hπl⟩, hπ4⟩, hπinj⟩, hPq⟩ := h
  exact {
    core := fun i => B.core (g.getD i 0)
    P := fun q => B.P (π.getD q 0)
    core_inj := by
      intro i j hi hj he
      have := B.core_inj _ _ (hgn i hi) (hgn j hj) he
      by_contra hij
      rcases hginj i hi j hj with h | h
      · exact hij h
      · exact h this
    P_mem := by
      intro q hq
      apply B.P_mem
      rcases q4_cases hq with rfl | rfl | rfl | rfl
      · exact hπ4.1
      · exact hπ4.2.1
      · exact hπ4.2.2.1
      · exact hπ4.2.2.2
    P_core := by
      intro q i hq hi
      have hπq : π.getD q 0 < 4 := by
        rcases q4_cases hq with rfl | rfl | rfl | rfl
        · exact hπ4.1
        · exact hπ4.2.1
        · exact hπ4.2.2.1
        · exact hπ4.2.2.2
      rw [B.P_core _ _ hπq (hgn i hi)]
      have := hPq
      rcases q4_cases hq with rfl | rfl | rfl | rfl
      · rw [(this.1.2 i hi).symm]
      · rw [(this.2.1.2 i hi).symm]
      · rw [(this.2.2.1.2 i hi).symm]
      · rw [(this.2.2.2.2 i hi).symm]
    two := by
      intro q r x hq hr hqr hxq hxr
      have hπ : ∀ q, q < 4 → π.getD q 0 < 4 := by
        intro q hq
        rcases q4_cases hq with rfl | rfl | rfl | rfl
        · exact hπ4.1
        · exact hπ4.2.1
        · exact hπ4.2.2.1
        · exact hπ4.2.2.2
      have hne : π.getD q 0 ≠ π.getD r 0 := by
        intro he
        have := hπinj
        rcases q4_cases hq with rfl | rfl | rfl | rfl <;> rcases q4_cases hr with rfl | rfl | rfl | rfl <;> simp_all
      obtain ⟨k, hk, rfl⟩ := B.two _ _ x (hπ q hq) (hπ r hr) hne hxq hxr
      -- `g` is onto `range n`
      have himg : (range C.n).image (fun i => g.getD i 0) = range C.n := by
        apply eq_of_subset_of_card_le
        · intro y hy; obtain ⟨i, hi, rfl⟩ := mem_image.1 hy; exact mem_range.2 (hgn i (mem_range.1 hi))
        · rw [card_image_of_injOn]
          intro i hi j hj he
          by_contra hij
          rcases hginj i (mem_range.1 hi) j (mem_range.1 hj) with h | h
          · exact hij h
          · exact h he
      have : k ∈ (range C.n).image (fun i => g.getD i 0) := by rw [himg]; exact mem_range.2 hk
      obtain ⟨i, hi, hik⟩ := mem_image.1 this
      exact ⟨i, mem_range.1 hi, congrArg B.core hik⟩ }

theorem relabel_tr (g π : List ℕ) (h : C.autOk g π = true) (X : Finset V) :
    (B.relabel g π h).tr X = Cls.permT g (B.tr X) := by
  have hg : g.length = C.n ∧ ∀ i, i < C.n → g.getD i 0 < C.n := by
    simp only [Cls.autOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
      decide_eq_true_eq] at h
    exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2⟩
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.2
  rw [Base.testBit_tr, testBit_permT]
  simp only [Base.testBit_tr]
  constructor
  · rintro ⟨hi, hx⟩
    have hgi : g.getD i 0 = g[i]'(by omega) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < g.length by omega)]
    refine ⟨by omega, hgi ▸ hg.2 i hi, ?_⟩
    rw [← hgi]; exact hx
  · rintro ⟨hi, hgi', hx⟩
    have hgi : g.getD i 0 = g[i] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    refine ⟨by omega, ?_⟩
    show B.core (g.getD i 0) ∈ X
    rw [hgi]; exact hx

theorem relabel_nonbase (g π : List ℕ) (h : C.autOk g π = true) {X : Finset V}
    (hX : ∀ q, q < 4 → X ≠ B.P q) : (B.relabel g π h).nonbase X := by
  intro q hq
  have hπq : π.getD q 0 < 4 := by
    simp only [Cls.autOk, Bool.and_eq_true, List.all_eq_true, Cls.q4, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, decide_eq_true_eq] at h
    have h4 := h.1.1.2
    rcases q4_cases hq with rfl | rfl | rfl | rfl
    · exact h4.1
    · exact h4.2.1
    · exact h4.2.2.1
    · exact h4.2.2.2
  exact hX _ hπq

end Base
end Erdos616R21.NoK4

namespace Erdos616R21.NoK4
open Finset TrCheck
variable {V : Type*} [DecidableEq V] {C : Cls} {H : Finset (Finset V)}

theorem clause_eval_of_any (a : ℕ → Bool) (c : Std.Sat.CNF.Clause ℕ)
    (h : c.literals.any (fun p => a p.1 == p.2) = true) : c.eval a = true := by
  unfold Std.Sat.CNF.Clause.eval
  rw [List.any_eq_true] at h ⊢
  obtain ⟨⟨i, n⟩, hm, he⟩ := h
  exact ⟨(i, n), hm, he⟩

/-- the assignment of a base satisfies every case CNF accepted by the checker whose unit trace is realised -/
theorem cnf_sat (B : Base C H) (hs : C.clsSane = true) (hC : Counter H) (hE : B.EdgeSound) (hP : B.PairSound)
    (f : Std.Sat.CNF ℕ) (r : ℕ)
    (hr : ∃ X ∈ H, B.nonbase X ∧ ∃ h : r < C.univ.length, B.tr X = (C.univ[r]).1)
    (hf : f.clauses.all (fun c => C.clauseOk C.univ.toArray r c.literals) = true) :
    f.eval B.asg = true := by
  unfold Std.Sat.CNF.eval
  rw [Array.all_eq_true] at hf ⊢
  intro i hi
  exact clause_eval_of_any _ _ (B.clause_sat hs hC hE hP r hr _ (hf i hi))

/-- **Leaf theorem modulo rule soundness.** If the checker accepts the case CNFs of class `C`, each case CNF is UNSAT,
and every base of class `C` in `H` satisfies `EdgeSound` and `PairSound`, then `H` has no base of class `C`. -/
theorem leaf_of_sound (cnfs : List (Std.Sat.CNF ℕ × ℕ)) (Bs : ℕ) (wit : List (ℕ × List ℕ × List ℕ × ℕ))
    (hok : C.checkAll cnfs Bs wit = true) (hunsat : ∀ p ∈ cnfs, ¬ ∃ a : ℕ → Bool, p.1.eval a = true)
    (hC : Counter H) (B : Base C H) (hE : ∀ B' : Base C H, B'.EdgeSound)
    (hP : ∀ B' : Base C H, B'.PairSound) : False := by
  unfold Cls.checkAll at hok
  simp only [Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨hs, horb⟩, hcnf⟩ := hok
  unfold Cls.orbitOk at horb
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    bne_iff_ne, ne_eq, List.any_eq_true, beq_iff_eq, Cls.q4, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.size_toArray] at horb
  obtain ⟨⟨hpc, hP0, hP1, hP2, hP3⟩, hav⟩ := horb
  obtain ⟨X, hX, hnb, i, hi, ht, hz⟩ := B.exists_avoider hs hC (hE B) Bs hpc hP0 hP1 hP2 hP3
  have hw := hav i hi
  rw [getD_toArray hi] at hw
  rcases hw with hne | ⟨w, -, hwp⟩
  · exact hne hz
  obtain ⟨i', g, π, r⟩ := w
  obtain ⟨⟨⟨hi', ⟨r', hr'm, hr'⟩⟩, haut⟩, hperm⟩ := hwp
  subst hi'
  obtain ⟨⟨f, r''⟩, hfm, hfr⟩ := List.mem_map.1 hr'm
  simp only at hfr
  subst hfr; subst hr'
  have hc := hcnf (f, r'') hfm
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.size_toArray] at hc
  obtain ⟨hrl, hcl⟩ := hc
  rw [getD_toArray hrl] at hperm
  set B' := B.relabel g π haut
  have hr : ∃ Y ∈ H, B'.nonbase Y ∧ ∃ h : r'' < C.univ.length, B'.tr Y = (C.univ[r'']).1 :=
    ⟨X, hX, B.relabel_nonbase g π haut hnb, hrl, by rw [B.relabel_tr, ht, hperm]⟩
  exact hunsat (f, r'') hfm ⟨B'.asg, cnf_sat B' hs hC (hE B') (hP B') f r'' hr hcl⟩

end Erdos616R21.NoK4
