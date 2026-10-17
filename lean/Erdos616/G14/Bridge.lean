import Erdos616.Basic
import Erdos616.G14.Root
/-!
# Erdős #616, r = 21: the encoding-soundness bridge for the N-K4 (3,2,1,1) leaf (G14)

Mathlib side. From a counterexample `H` (`Counter H`) with a *labelled* (3,2,1,1)-K4 base (`LBase H`) and Theorem W7-I
(taken as an explicit hypothesis `W7I H`, formalized elsewhere), build the abstract trace model `G14.Model` of the
core-only layer (Erdos616/G14/Glue.lean), whose CNFs are refuted by the LRAT-checked certificates.
-/
open Finset

namespace G14B

/-! ## Part A: bit masks ↔ cardinalities -/

/-- `maskOf f n` = the number whose bit `i < n` is `f i`. -/
def maskOf (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => maskOf f n ||| (if f n then 2 ^ n else 0)

theorem testBit_maskOf (f : ℕ → Bool) : ∀ n j, (maskOf f n).testBit j = (decide (j < n) && f j)
  | 0, j => by simp [maskOf]
  | n + 1, j => by
      rw [maskOf, Nat.testBit_or, testBit_maskOf f n j]
      by_cases hj : j = n
      · subst hj
        cases h : f j <;> simp [Nat.testBit_two_pow]
      · have h2 : (if f n then 2 ^ n else 0).testBit j = false := by
          split <;> simp [Nat.testBit_two_pow, Ne.symm hj]
        rw [h2, Bool.or_false]
        by_cases h : j < n
        · simp [h, show j < n + 1 by omega]
        · simp [h, show ¬ j < n + 1 by omega]

theorem maskOf_lt (f : ℕ → Bool) (n : ℕ) : maskOf f n < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_maskOf]
  simp; omega

/-- `pc` is the cardinality of the set of set bits among the first 16. -/
theorem pc_eq_card (x : ℕ) : G14.pc x = (univ.filter fun i : Fin 16 => x.testBit i = true).card := by
  unfold G14.pc
  rw [List.countP_eq_length_filter]
  rfl

end G14B

/-! ## Part B: the labelled (3,2,1,1)-K4 base and the region calculus -/

namespace Erdos616R21
open G14B

variable {V : Type*} [DecidableEq V]

/-- A labelled (3,2,1,1)-K4 base: four edges `P 0..3` and an injective labelling `c` of the 16 core points with the
membership table `G14.Pm` (bit order v,w,al0,al1,g0,g1,g2,m0,m1,m2,a3_0,a3_1,a4_0,a4_1,c3,c4); every point lying in
two base edges is a core point. -/
structure LBase (H : Finset (Finset V)) where
  P : Fin 4 → Finset V
  c : Fin 16 → V
  hP : ∀ q, P q ∈ H
  cinj : Function.Injective c
  hmem : ∀ (i : Fin 16) (q : Fin 4), c i ∈ P q ↔ (G14.Pm q).testBit i = true
  hcore : ∀ q q' : Fin 4, q ≠ q' → ∀ x, x ∈ P q → x ∈ P q' → ∃ i, c i = x

namespace LBase
variable {H : Finset (Finset V)} (B : LBase H)

def core : Finset V := univ.image B.c
def O (q : Fin 4) : Finset V := B.P q \ B.core
def PU : Finset V := B.P 0 ∪ B.P 1 ∪ B.P 2 ∪ B.P 3

def bit (S : Finset V) (i : ℕ) : Bool := if h : i < 16 then decide (B.c ⟨i, h⟩ ∈ S) else false
/-- the core trace of a set, as a 16-bit mask -/
def tr (S : Finset V) : ℕ := maskOf (B.bit S) 16

theorem testBit_tr (S : Finset V) (i : Fin 16) : (B.tr S).testBit i = decide (B.c i ∈ S) := by
  unfold tr; rw [testBit_maskOf]; simp [bit, i.isLt]

theorem testBit_tr_ge (S : Finset V) {i : ℕ} (hi : 16 ≤ i) : (B.tr S).testBit i = false := by
  unfold tr; rw [testBit_maskOf]; simp; omega

theorem tr_lt (S : Finset V) : B.tr S < 65536 := maskOf_lt _ 16

theorem mem_core {x : V} : x ∈ B.core ↔ ∃ i, B.c i = x := by simp [core]

/-- core count: if `m` describes which core points lie in `S`, then `|S ∩ core| = pc m`. -/
theorem card_core (S : Finset V) (m : ℕ) (hm : ∀ i : Fin 16, B.c i ∈ S ↔ m.testBit i = true) :
    (S ∩ B.core).card = G14.pc m := by
  rw [pc_eq_card]
  have : S ∩ B.core = (univ.filter fun i : Fin 16 => m.testBit i = true).image B.c := by
    ext x
    simp only [mem_inter, mem_core, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hx, i, rfl⟩; exact ⟨i, (hm i).1 hx, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨(hm i).2 hi, i, rfl⟩
  rw [this, card_image_of_injective _ B.cinj]

theorem col_nonzero : ∀ i : Fin 16, ∃ q : Fin 4, (G14.Pm q).testBit i = true := by decide

theorem core_sub_PU : B.core ⊆ B.PU := by
  intro x hx
  obtain ⟨i, rfl⟩ := B.mem_core.1 hx
  obtain ⟨q, hq⟩ := col_nonzero i
  have := (B.hmem i q).2 hq
  unfold PU
  simp only [mem_union]
  rcases q with ⟨_ | _ | _ | _ | _, hq4⟩
  · exact Or.inl (Or.inl (Or.inl this))
  · exact Or.inl (Or.inl (Or.inr this))
  · exact Or.inl (Or.inr this)
  · exact Or.inr this
  · omega

theorem O_disj {q q' : Fin 4} (h : q ≠ q') {x : V} (hx : x ∈ B.O q) (hx' : x ∈ B.P q') : False := by
  unfold O at hx
  rw [mem_sdiff] at hx
  obtain ⟨i, rfl⟩ := B.hcore q q' h x hx.1 hx'
  exact hx.2 (B.mem_core.2 ⟨i, rfl⟩)

/-- partition of any finite set into core, the four outside parts `O q` and the rest -/
theorem card_part (S : Finset V) :
    S.card = (S ∩ B.core).card + (S ∩ B.O 0).card + (S ∩ B.O 1).card + (S ∩ B.O 2).card +
      (S ∩ B.O 3).card + (S \ B.PU).card := by
  have e1 := card_inter_add_card_sdiff S B.core
  have e2 := card_inter_add_card_sdiff (S \ B.core) (B.P 0)
  have e3 := card_inter_add_card_sdiff ((S \ B.core) \ B.P 0) (B.P 1)
  have e4 := card_inter_add_card_sdiff (((S \ B.core) \ B.P 0) \ B.P 1) (B.P 2)
  have e5 := card_inter_add_card_sdiff ((((S \ B.core) \ B.P 0) \ B.P 1) \ B.P 2) (B.P 3)
  have f2 : (S \ B.core) ∩ B.P 0 = S ∩ B.O 0 := by ext x; simp [O]; tauto
  have f3 : (S \ B.core) \ B.P 0 ∩ B.P 1 = S ∩ B.O 1 := by
    ext x; simp only [mem_inter, mem_sdiff, O]; constructor
    · rintro ⟨⟨⟨h1, h2⟩, -⟩, h4⟩; exact ⟨h1, h4, h2⟩
    · rintro ⟨h1, h4, h2⟩
      exact ⟨⟨⟨h1, h2⟩, fun h => B.O_disj (by decide : (1 : Fin 4) ≠ 0) (by simp [O, h4, h2]) h⟩, h4⟩
  have f4 : ((S \ B.core) \ B.P 0) \ B.P 1 ∩ B.P 2 = S ∩ B.O 2 := by
    ext x; simp only [mem_inter, mem_sdiff, O]; constructor
    · rintro ⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, h4⟩; exact ⟨h1, h4, h2⟩
    · rintro ⟨h1, h4, h2⟩
      exact ⟨⟨⟨⟨h1, h2⟩, fun h => B.O_disj (by decide : (2 : Fin 4) ≠ 0) (by simp [O, h4, h2]) h⟩,
        fun h => B.O_disj (by decide : (2 : Fin 4) ≠ 1) (by simp [O, h4, h2]) h⟩, h4⟩
  have f5 : (((S \ B.core) \ B.P 0) \ B.P 1) \ B.P 2 ∩ B.P 3 = S ∩ B.O 3 := by
    ext x; simp only [mem_inter, mem_sdiff, O]; constructor
    · rintro ⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩, h4⟩; exact ⟨h1, h4, h2⟩
    · rintro ⟨h1, h4, h2⟩
      exact ⟨⟨⟨⟨⟨h1, h2⟩, fun h => B.O_disj (by decide : (3 : Fin 4) ≠ 0) (by simp [O, h4, h2]) h⟩,
        fun h => B.O_disj (by decide : (3 : Fin 4) ≠ 1) (by simp [O, h4, h2]) h⟩,
        fun h => B.O_disj (by decide : (3 : Fin 4) ≠ 2) (by simp [O, h4, h2]) h⟩, h4⟩
  have f6 : ((((S \ B.core) \ B.P 0) \ B.P 1) \ B.P 2) \ B.P 3 = S \ B.PU := by
    ext x; simp only [mem_sdiff, PU, mem_union]; constructor
    · rintro ⟨⟨⟨⟨⟨h1, -⟩, h3⟩, h4⟩, h5⟩, h6⟩; exact ⟨h1, by tauto⟩
    · rintro ⟨h1, h2⟩
      have h2' : x ∉ B.core := fun h => h2 (by have := B.core_sub_PU h; simp only [PU, mem_union] at this; tauto)
      refine ⟨⟨⟨⟨⟨h1, h2'⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> intro h <;> exact h2 (by tauto)
  rw [f2] at e2; rw [f3] at e3; rw [f4] at e4; rw [f5, f6] at e5
  omega

end LBase
end Erdos616R21

/-! ## Part C: the trace model of a counterexample with a labelled base -/

namespace Erdos616R21
open G14B

variable {V : Type*} [DecidableEq V]

/-- Theorem W7-I (proved by hand in upper.md §7.4, formalized separately): cross-type singles of any 5-pair meet in
at least two points on each side. Taken here as an explicit hypothesis. -/
def W7I (H : Finset (Finset V)) : Prop :=
  ∀ a ∈ H, ∀ b ∈ H, ∀ G ∈ H, ∀ G' ∈ H, (a ∩ b).card = 5 → ∀ x y : V, G ∩ (a ∩ b) = {x} → G' ∩ (a ∩ b) = {y} →
    x ≠ y → 2 ≤ (G ∩ G' ∩ (a \ b)).card ∧ 2 ≤ (G ∩ G' ∩ (b \ a)).card

namespace LBase
variable {H : Finset (Finset V)} (B : LBase H)

/-- `|F ∩ O_q|` for `q : ℕ` (0 for `q ≥ 4`) -/
def ov (F : Finset V) (q : ℕ) : ℕ := if h : q < 4 then (F ∩ B.O ⟨q, h⟩).card else 0
/-- the outside vector of an edge -/
def st (F : Finset V) : G14.O4 := ⟨B.ov F 0, B.ov F 1, B.ov F 2, B.ov F 3⟩

theorem st_get (F : Finset V) (q : ℕ) : (B.st F).get q = B.ov F q := by
  rcases q with _ | _ | _ | _ | q <;> simp [st, G14.O4.get, ov]

def nonbase (F : Finset V) : Prop := ∀ q, F ≠ B.P q

/-- per-edge soundness: every non-base edge has an admissible state (the S13.1 rules) -/
def EdgeSound : Prop := ∀ F ∈ H, B.nonbase F → G14.ok (B.tr F) (B.st F) = true
/-- pairwise soundness: two distinct non-base edges are compatible (Lemma A, F1, SAME, L, D1) -/
def PairSound : Prop := ∀ F ∈ H, ∀ F' ∈ H, B.nonbase F → B.nonbase F' → F ≠ F' →
  G14.feasible (B.tr F) (B.st F) (B.tr F') (B.st F') = true

/-- the trace model of the base -/
def model (hC : Counter H) (hE : B.EdgeSound) (hP : B.PairSound) : G14.Model where
  occ t := ∃ F ∈ H, B.nonbase F ∧ B.tr F = t
  lt := by rintro t ⟨F, -, -, rfl⟩; exact B.tr_lt F
  univ := by rintro t ⟨F, hF, hnb, rfl⟩; exact G14.states_ne_of_ok (hE F hF hnb)
  cov := by
    intro Bm hBm
    unfold G14.neededB at hBm
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, G14.Q4_all, bne_iff_ne, ne_eq] at hBm
    obtain ⟨⟨hlt, h4⟩, hq0, hq1, hq2, hq3⟩ := hBm
    let S : Finset V := (univ.filter fun i : Fin 16 => Bm.testBit i = true).image B.c
    have hS : S.card ≤ 4 := by
      have := card_image_le (s := univ.filter fun i : Fin 16 => Bm.testBit i = true) (f := B.c)
      rw [← pc_eq_card, h4] at this; exact this
    obtain ⟨e, he, hdis⟩ := hC.avoid S hS
    -- each base edge meets S, so `e` is not a base edge
    have hmeet : ∀ q : Fin 4, Bm &&& G14.Pm q ≠ 0 → ∃ x ∈ S, x ∈ B.P q := by
      intro q hq
      obtain ⟨k, hk⟩ : ∃ k, (Bm &&& G14.Pm q).testBit k = true := by
        by_contra hno
        push Not at hno
        exact hq (Nat.eq_of_testBit_eq (fun k => by simpa using hno k))
      rw [Nat.testBit_and, Bool.and_eq_true] at hk
      have hk16 : k < 16 := by
        by_contra hge
        have := Nat.testBit_lt_two_pow (show Bm < 2 ^ k from lt_of_lt_of_le hlt
          (le_trans (by decide : (65536 : ℕ) ≤ 2 ^ 16) (Nat.pow_le_pow_right (n := 2) (by decide) (by omega))))
        rw [this] at hk; exact Bool.false_ne_true hk.1
      refine ⟨B.c ⟨k, hk16⟩, mem_image.2 ⟨⟨k, hk16⟩, by simpa using hk.1, rfl⟩, (B.hmem _ _).2 hk.2⟩
    refine ⟨B.tr e, ⟨e, he, ?_, rfl⟩, ?_⟩
    · intro q hq
      have hq' : Bm &&& G14.Pm q ≠ 0 := by
        rcases q with ⟨_ | _ | _ | _ | _, h⟩
        · exact hq0
        · exact hq1
        · exact hq2
        · exact hq3
        · omega
      obtain ⟨x, hxS, hxP⟩ := hmeet q hq'
      rw [← hq] at hxP
      exact Finset.disjoint_left.1 hdis hxP hxS
    · apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and, Nat.zero_testBit]
      by_cases hk : k < 16
      · have := B.testBit_tr e ⟨k, hk⟩
        simp only at this
        rw [this]
        cases hb : Bm.testBit k
        · simp
        · have hx : B.c ⟨k, hk⟩ ∈ S := mem_image.2 ⟨⟨k, hk⟩, by simpa using hb, rfl⟩
          have : B.c ⟨k, hk⟩ ∉ e := fun h => Finset.disjoint_left.1 hdis h hx
          simp [this]
      · rw [B.testBit_tr_ge e (by omega)]; simp
  conf := by
    rintro t t' ⟨F, hF, hnb, rfl⟩ ⟨F', hF', hnb', rfl⟩ hne
    exact G14.compatTr_of (hE F hF hnb) (hE F' hF' hnb')
      (hP F hF F' hF' hnb hnb' (fun h => hne (h ▸ rfl)))

end LBase
end Erdos616R21

/-! ## Part D: relabelling the core by a base automorphism, and the root split -/

namespace G14B

theorem foldl_range_eq_maskOf (f : ℕ → Bool) : ∀ n,
    (List.range n).foldl (fun acc i => if f i then acc ||| 2 ^ i else acc) 0 = maskOf f n
  | 0 => rfl
  | n + 1 => by
      rw [List.range_succ, List.foldl_append, foldl_range_eq_maskOf f n]
      simp only [List.foldl_cons, List.foldl_nil, maskOf]
      cases f n <;> simp

theorem pull_eq (s : List ℕ) (t : ℕ) : G14.pull s t = maskOf (fun i => t.testBit s[i]!) 16 := by
  unfold G14.pull
  exact foldl_range_eq_maskOf (fun i => t.testBit s[i]!) 16

theorem validPerm_spec {s : List ℕ} (h : G14.validPerm s = true) :
    s.length = 16 ∧ (∀ x ∈ s, x < 16) ∧ s.Nodup ∧
      ∀ q < 4, ∀ i < 16, (G14.Pm q).testBit s[i]! = (G14.Pm q).testBit i := by
  unfold G14.validPerm at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨⟨⟨hl, hlt⟩, hnd⟩, hq4⟩ := h
  refine ⟨hl, hlt, hnd, ?_⟩
  intro q hq i hi
  exact hq4 q (by simp [G14.Q4]; omega) i hi

end G14B

namespace Erdos616R21
open G14B
variable {V : Type*} [DecidableEq V]

namespace LBase
variable {H : Finset (Finset V)} (B : LBase H)

/-- the relabelling map `i ↦ s[i]` on core labels -/
def sig {s : List ℕ} (hs : G14.validPerm s = true) (i : Fin 16) : Fin 16 :=
  ⟨s[i.val]!, by
    obtain ⟨hl, hlt, -, -⟩ := validPerm_spec hs
    have : i.val < s.length := by rw [hl]; exact i.isLt
    rw [getElem!_pos s i.val this]
    exact hlt _ (List.getElem_mem this)⟩

theorem sig_inj {s : List ℕ} (hs : G14.validPerm s = true) : Function.Injective (sig hs) := by
  intro i j hij
  obtain ⟨hl, -, hnd, -⟩ := validPerm_spec hs
  have hi : i.val < s.length := by rw [hl]; exact i.isLt
  have hj : j.val < s.length := by rw [hl]; exact j.isLt
  simp only [sig, Fin.mk.injEq] at hij
  rw [getElem!_pos s i.val hi, getElem!_pos s j.val hj] at hij
  exact Fin.ext ((hnd.getElem_inj_iff).1 hij)

theorem sig_surj {s : List ℕ} (hs : G14.validPerm s = true) : Function.Surjective (sig hs) :=
  Finite.surjective_of_injective (sig_inj hs)

/-- the base relabelled by a valid permutation `s` (new label `i` = old label `s[i]`) -/
def relabel {s : List ℕ} (hs : G14.validPerm s = true) : LBase H where
  P := B.P
  c := fun i => B.c (sig hs i)
  hP := B.hP
  cinj := B.cinj.comp (sig_inj hs)
  hmem := by
    intro i q
    rw [B.hmem]
    obtain ⟨-, -, -, h⟩ := validPerm_spec hs
    simp only [sig]
    rw [h q.val q.isLt i.val i.isLt]
  hcore := by
    intro q q' hqq' x hx hx'
    obtain ⟨j, rfl⟩ := B.hcore q q' hqq' x hx hx'
    obtain ⟨i, rfl⟩ := sig_surj hs j
    exact ⟨i, rfl⟩

theorem relabel_core {s : List ℕ} (hs : G14.validPerm s = true) : (B.relabel hs).core = B.core := by
  ext x; simp only [mem_core]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨j, rfl⟩; obtain ⟨i, rfl⟩ := sig_surj hs j; exact ⟨i, rfl⟩

theorem relabel_st {s : List ℕ} (hs : G14.validPerm s = true) (F : Finset V) :
    (B.relabel hs).st F = B.st F := by
  unfold st ov O; rw [relabel_core]; rfl

theorem relabel_tr {s : List ℕ} (hs : G14.validPerm s = true) (F : Finset V) :
    (B.relabel hs).tr F = G14.pull s (B.tr F) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [pull_eq, testBit_maskOf]
  by_cases hk : k < 16
  · have h1 := (B.relabel hs).testBit_tr F ⟨k, hk⟩
    have h2 := B.testBit_tr F (sig hs ⟨k, hk⟩)
    simp only at h1 h2
    rw [h1]
    simp only [hk, decide_true, Bool.true_and]
    rw [show s[k]! = (sig hs ⟨k, hk⟩).val from rfl, h2]
    rfl
  · rw [testBit_tr_ge _ F (by omega)]; simp [hk]

end LBase

/-- **The N-K4 leaf, modulo the per-edge and pairwise soundness of the encoding and the certificate facts.**
The relabelled models are fed to `G14.root_split`. -/
theorem NK4_leaf_of {H : Finset (Finset V)} (hC : Counter H) (B : LBase H)
    (hES : ∀ B' : LBase H, B'.EdgeSound) (hPS : ∀ B' : LBase H, B'.PairSound)
    (hu : G14.univOK () = true) (hr : G14.rootOK = true)
    (caseR : ∀ r ∈ G14.reps, ∀ M : G14.Model, M.occ G14.T[r]! → False)
    (caseDead : ∀ M : G14.Model, (G14.deadClause.any fun (i, n) => G14.assign M i == n) = true → False) :
    False := by
  classical
  let M : List ℕ → G14.Model := fun s =>
    if hs : G14.validPerm s = true then (B.relabel hs).model hC (hES _) (hPS _) else B.model hC (hES _) (hPS _)
  have h0 : G14.validPerm [] = false := by decide
  refine G14.root_split hu hr caseR caseDead M [] ?_
  intro s hs t ht
  simp only [M, h0, hs, dite_true] at ht ⊢
  simp only [Bool.false_eq_true, dite_false] at ht
  obtain ⟨F, hF, hnb, rfl⟩ := ht
  exact ⟨F, hF, hnb, B.relabel_tr hs F⟩

end Erdos616R21

/-! ## Part E: region calculus for edges, and the per-edge soundness `EdgeSound` -/

namespace G14B

theorem testBit_65535 : ∀ k : Fin 16, (65535 : ℕ).testBit k = true := by decide

theorem testBit_cmp (y : ℕ) (k : Fin 16) : (G14.cmp y).testBit k = !y.testBit k := by
  unfold G14.cmp; rw [Nat.testBit_xor, testBit_65535 k]; cases y.testBit k <;> rfl

theorem Pm_ge (q : ℕ) (h : 4 ≤ q) : G14.Pm q = 0 := by
  rcases q with _ | _ | _ | _ | q <;> first | omega | rfl

theorem Pm_lt16 (q : ℕ) : G14.Pm q < 2 ^ 16 := by
  rcases q with _ | _ | _ | _ | q <;> first | decide | (rw [Pm_ge _ (by omega)]; decide)

theorem pc_Pm : G14.pc (G14.Pm 0) = 11 ∧ G14.pc (G14.Pm 1) = 10 ∧ G14.pc (G14.Pm 2) = 9 ∧ G14.pc (G14.Pm 3) = 9 := by
  decide

end G14B

namespace Erdos616R21
open G14B
variable {V : Type*} [DecidableEq V]

namespace LBase
variable {H : Finset (Finset V)} (B : LBase H)

/-- union of the base edges selected by the 4-bit mask `X` -/
def UX (X : ℕ) : Finset V :=
  (if X.testBit 0 then B.P 0 else ∅) ∪ (if X.testBit 1 then B.P 1 else ∅) ∪
    (if X.testBit 2 then B.P 2 else ∅) ∪ (if X.testBit 3 then B.P 3 else ∅)

/-- the core selector of `UX X` -/
def selX (X : ℕ) (k : ℕ) : Bool :=
  (X.testBit 0 && (G14.Pm 0).testBit k) || (X.testBit 1 && (G14.Pm 1).testBit k) ||
    (X.testBit 2 && (G14.Pm 2).testBit k) || (X.testBit 3 && (G14.Pm 3).testBit k)

theorem mem_UX_c (X : ℕ) (k : Fin 16) : B.c k ∈ B.UX X ↔ selX X k = true := by
  unfold UX selX
  simp only [mem_union, Bool.or_eq_true, Bool.and_eq_true]
  have h0 := B.hmem k 0; have h1 := B.hmem k 1; have h2 := B.hmem k 2; have h3 := B.hmem k 3
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2 h3
  split <;> split <;> split <;> split <;> simp_all

theorem O_sub_P (q : Fin 4) : B.O q ⊆ B.P q := sdiff_subset

theorem P_sub_PU (q : Fin 4) : B.P q ⊆ B.PU := by
  intro x hx; unfold PU; simp only [mem_union]
  rcases q with ⟨_ | _ | _ | _ | _, h⟩
  · exact Or.inl (Or.inl (Or.inl hx))
  · exact Or.inl (Or.inl (Or.inr hx))
  · exact Or.inl (Or.inr hx)
  · exact Or.inr hx
  · omega

theorem UX_sub_PU (X : ℕ) : B.UX X ⊆ B.PU := by
  intro x hx; unfold UX at hx
  simp only [mem_union] at hx
  rcases hx with ((h | h) | h) | h <;> split at h <;> first
    | exact B.P_sub_PU _ h | simp at h

/-- `(S ∩ UX X) ∩ O q` -/
theorem inter_UX_O (S : Finset V) (X : ℕ) (q : Fin 4) :
    S ∩ B.UX X ∩ B.O q = if X.testBit q then S ∩ B.O q else ∅ := by
  ext x
  constructor
  · intro hx
    simp only [mem_inter] at hx
    obtain ⟨⟨hS, hU⟩, hO⟩ := hx
    unfold UX at hU
    simp only [mem_union] at hU
    have key : ∀ q' : Fin 4, X.testBit q' = true → x ∈ B.P q' → X.testBit q = true := by
      intro q' hq' hx'
      by_cases hqq : q = q'
      · subst hqq; exact hq'
      · exact (B.O_disj hqq hO hx').elim
    have hX : X.testBit q = true := by
      rcases hU with ((h | h) | h) | h <;> split at h <;> first
        | exact key _ (by assumption) h | simp at h
    rw [if_pos hX]; exact mem_inter.2 ⟨hS, hO⟩
  · intro hx
    split at hx
    · rename_i hX
      simp only [mem_inter] at hx ⊢
      refine ⟨⟨hx.1, ?_⟩, hx.2⟩
      have hP := B.O_sub_P q hx.2
      unfold UX; simp only [mem_union]
      rcases q with ⟨_ | _ | _ | _ | _, h⟩
      · left; left; left; simp only [Fin.zero_eta] at hX hP ⊢; rw [if_pos hX]; exact hP
      · left; left; right; rw [if_pos hX]; exact hP
      · left; right; rw [if_pos hX]; exact hP
      · right; rw [if_pos hX]; exact hP
      · omega
    · simp at hx

/-- **Region lemma.** `|S ∩ ⋃_{q ∈ X} P_q|` = core part + the selected outside parts. -/
theorem card_inter_UX (S : Finset V) (X m : ℕ) (hm : ∀ k : Fin 16, m.testBit k = selX X k) :
    (S ∩ B.UX X).card = G14.pc (B.tr S &&& m) +
      ((if X.testBit 0 then (S ∩ B.O 0).card else 0) + (if X.testBit 1 then (S ∩ B.O 1).card else 0) +
       (if X.testBit 2 then (S ∩ B.O 2).card else 0) + (if X.testBit 3 then (S ∩ B.O 3).card else 0)) := by
  have hp := B.card_part (S ∩ B.UX X)
  have hc : (S ∩ B.UX X ∩ B.core).card = G14.pc (B.tr S &&& m) := by
    apply B.card_core
    intro k
    rw [Nat.testBit_and, B.testBit_tr, hm, mem_inter, B.mem_UX_c]
    simp
  have hr : (S ∩ B.UX X) \ B.PU = ∅ := by
    rw [sdiff_eq_empty_iff_subset]; exact inter_subset_right.trans (B.UX_sub_PU X)
  rw [hc, hr, card_empty, B.inter_UX_O S X 0, B.inter_UX_O S X 1, B.inter_UX_O S X 2, B.inter_UX_O S X 3] at hp
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at hp
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [h3] at hp
  simp only [apply_ite Finset.card, card_empty] at hp
  rw [hp]
  omega

/-- whole-set partition with the core part as a popcount -/
theorem card_whole (S : Finset V) :
    S.card = G14.pc (B.tr S) + (S ∩ B.O 0).card + (S ∩ B.O 1).card + (S ∩ B.O 2).card + (S ∩ B.O 3).card +
      (S \ B.PU).card := by
  have := B.card_part S
  rw [B.card_core S (B.tr S) (fun k => by rw [B.testBit_tr]; simp)] at this
  exact this

/-- a subset of the core has cardinality = popcount of any mask describing it -/
theorem card_of_sub_core (S : Finset V) (hS : S ⊆ B.core) (m : ℕ)
    (hm : ∀ k : Fin 16, B.c k ∈ S ↔ m.testBit k = true) : S.card = G14.pc m := by
  rw [← B.card_core S m hm, inter_eq_left.2 hS]

theorem inter2_sub_core {q q' : Fin 4} (h : q ≠ q') : B.P q ∩ B.P q' ⊆ B.core := by
  intro x hx
  rw [mem_inter] at hx
  obtain ⟨i, rfl⟩ := B.hcore q q' h x hx.1 hx.2
  exact B.mem_core.2 ⟨i, rfl⟩

end LBase
end Erdos616R21

namespace Erdos616R21
open G14B
variable {V : Type*} [DecidableEq V]

namespace LBase
variable {H : Finset (Finset V)} (B : LBase H)

theorem UX_single (q : Fin 4) : B.UX (2 ^ (q : ℕ)) = B.P q := by
  rcases q with ⟨_ | _ | _ | _ | _, h⟩
  · simp [UX, show (1 : ℕ).testBit 1 = false by decide, show (1 : ℕ).testBit 2 = false by decide,
      show (1 : ℕ).testBit 3 = false by decide]
  · simp [UX, show (2 : ℕ).testBit 1 = true by decide, show (2 : ℕ).testBit 2 = false by decide,
      show (2 : ℕ).testBit 3 = false by decide]
  · simp [UX, show (4 : ℕ).testBit 1 = false by decide, show (4 : ℕ).testBit 2 = true by decide,
      show (4 : ℕ).testBit 3 = false by decide]
  · simp [UX, show (8 : ℕ).testBit 1 = false by decide, show (8 : ℕ).testBit 2 = false by decide,
      show (8 : ℕ).testBit 3 = true by decide]
  · omega

theorem selX_single : ∀ q : Fin 4, ∀ k : Fin 16, (G14.Pm q).testBit k = selX (2 ^ (q : ℕ)) k := by
  decide

theorem ov_eq (F : Finset V) (q : Fin 4) : B.ov F q = (F ∩ B.O q).card := by
  simp [ov, q.isLt]

theorem st_get_fin (F : Finset V) (q : Fin 4) : (B.st F).get q = (F ∩ B.O q).card := by
  rw [st_get, ov_eq]

/-- `|S ∩ P_q| = |S ∩ P_q ∩ core| + |S ∩ O_q|` -/
theorem card_inter_P (S : Finset V) (q : Fin 4) :
    (S ∩ B.P q).card = G14.pc (B.tr S &&& G14.Pm q) + (S ∩ B.O q).card := by
  have := B.card_inter_UX S (2 ^ (q : ℕ)) (G14.Pm q) (selX_single q)
  rw [UX_single] at this
  rw [this]
  rcases q with ⟨_ | _ | _ | _ | _, h⟩
  · simp [show (1 : ℕ).testBit 1 = false by decide, show (1 : ℕ).testBit 2 = false by decide,
      show (1 : ℕ).testBit 3 = false by decide]
  · simp [show (2 : ℕ).testBit 1 = true by decide, show (2 : ℕ).testBit 2 = false by decide,
      show (2 : ℕ).testBit 3 = false by decide]
  · simp [show (4 : ℕ).testBit 1 = false by decide, show (4 : ℕ).testBit 2 = true by decide,
      show (4 : ℕ).testBit 3 = false by decide]
  · simp [show (8 : ℕ).testBit 1 = false by decide, show (8 : ℕ).testBit 2 = false by decide,
      show (8 : ℕ).testBit 3 = true by decide]
  · omega

theorem tr_P (q : Fin 4) : B.tr (B.P q) = G14.Pm q := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 16
  · have := B.testBit_tr (B.P q) ⟨k, hk⟩
    simp only at this
    rw [this]
    have h2 := B.hmem ⟨k, hk⟩ q
    simp only at h2
    by_cases hm : B.c ⟨k, hk⟩ ∈ B.P q
    · rw [decide_eq_true hm, h2.1 hm]
    · rw [decide_eq_false hm]
      cases h3 : (G14.Pm q).testBit k
      · rfl
      · exact absurd (h2.2 h3) hm
  · rw [B.testBit_tr_ge _ (by omega)]
    have : G14.Pm q < 2 ^ k := lt_of_lt_of_le (Pm_lt16 q)
      (Nat.pow_le_pow_right (n := 2) (by decide) (show 16 ≤ k by omega))
    rw [Nat.testBit_lt_two_pow this]

/-- `|O_q| = 21 - |P_q ∩ core|` -/
theorem card_O (hC : Counter H) (q : Fin 4) : (B.O q).card = G14.OSZ q := by
  have h1 := B.card_inter_P (B.P q) q
  rw [inter_self, B.tr_P, Nat.and_self, hC.unif _ (B.hP q)] at h1
  have h2 : B.P q ∩ B.O q = B.O q := inter_eq_right.2 (B.O_sub_P q)
  rw [h2] at h1
  have e : ∀ q : Fin 4, G14.pc (G14.Pm q) + G14.OSZ q = 21 := by decide
  have := e q
  omega

/-- edge partition: `21 = |F ∩ core| + Σ o_q + u` -/
theorem edge_part (hC : Counter H) {F : Finset V} (hF : F ∈ H) :
    21 = G14.pc (B.tr F) + (F ∩ B.O 0).card + (F ∩ B.O 1).card + (F ∩ B.O 2).card + (F ∩ B.O 3).card +
      (F \ B.PU).card := by
  rw [← hC.unif F hF]; exact B.card_whole F

end LBase
end Erdos616R21

namespace G14B
theorem pc_N : ∀ i j : Fin 4, i ≠ j → G14.pc (G14.Pm i &&& G14.Pm j) = 5 := by decide
end G14B

namespace Erdos616R21
open G14B
variable {V : Type*} [DecidableEq V]

namespace LBase
variable {H : Finset (Finset V)} (B : LBase H)

theorem xq_eq (F : Finset V) (q : Fin 4) : G14.xq (B.tr F) (B.st F) q = (F ∩ B.P q).card := by
  unfold G14.xq; rw [B.st_get_fin, B.card_inter_P]

/-- a mask that differs from another on some bit differs on a core bit -/
theorem exists_bit_of_ne {x y : ℕ} (hx : x < 65536) (hy : y < 65536) (h : x ≠ y) :
    ∃ k : Fin 16, x.testBit k ≠ y.testBit k := by
  by_contra hno
  push Not at hno
  apply h
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 16
  · exact hno ⟨k, hk⟩
  · have h1 : x < 2 ^ k := lt_of_lt_of_le hx (Nat.pow_le_pow_right (n := 2) (by decide) (show 16 ≤ k by omega))
    have h2 : y < 2 ^ k := lt_of_lt_of_le hy (Nat.pow_le_pow_right (n := 2) (by decide) (show 16 ≤ k by omega))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

theorem Pm_lt (q : ℕ) : G14.Pm q < 65536 := by
  rcases q with _ | _ | _ | _ | q <;> first | decide | (rw [Pm_ge _ (by omega)]; decide)

theorem and_lt {x y : ℕ} (hy : y < 65536) : x &&& y < 65536 :=
  lt_of_le_of_lt Nat.and_le_right hy

/-- the F1/D1 rule at a base 5-pair -/
theorem F1D1_edge (hC : Counter H) {F : Finset V} (hF : F ∈ H) (i j : Fin 4) (hij : i ≠ j) :
    (B.tr F &&& (G14.Pm i &&& G14.Pm j) != 0 &&
      (B.tr F &&& (G14.Pm i &&& G14.Pm j) == (G14.Pm i &&& G14.Pm j) ||
        G14.xq (B.tr F) (B.st F) i + G14.xq (B.tr F) (B.st F) j ≤ 9 + G14.pc (B.tr F &&& (G14.Pm i &&& G14.Pm j)))) =
      true := by
  have hcore := B.inter2_sub_core hij
  have hFN : (F ∩ (B.P i ∩ B.P j)).card = G14.pc (B.tr F &&& (G14.Pm i &&& G14.Pm j)) :=
    B.card_of_sub_core _ (inter_subset_right.trans hcore) _ (fun k => by
      simp only [mem_inter, Nat.testBit_and, B.testBit_tr, Bool.and_eq_true, decide_eq_true_eq, B.hmem])
  have hN : (B.P i ∩ B.P j).card = 5 := by
    rw [B.card_of_sub_core _ hcore (G14.Pm i &&& G14.Pm j) (fun k => by
      simp only [mem_inter, Nat.testBit_and, Bool.and_eq_true, B.hmem])]
    exact pc_N i j hij
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h0
    obtain ⟨x, hxi, hxj, hxF⟩ := inter3 hC (B.hP i) (B.hP j) hF
    obtain ⟨k, rfl⟩ := B.hcore i j hij x hxi hxj
    have : (B.tr F &&& (G14.Pm i &&& G14.Pm j)).testBit k = true := by
      rw [Nat.testBit_and, Nat.testBit_and, B.testBit_tr, (B.hmem k i).1 hxi, (B.hmem k j).1 hxj]; simp [hxF]
    rw [h0, Nat.zero_testBit] at this; exact Bool.false_ne_true this
  · by_cases heq : B.tr F &&& (G14.Pm i &&& G14.Pm j) = G14.Pm i &&& G14.Pm j
    · exact Or.inl heq
    · right
      obtain ⟨k, hk⟩ := exists_bit_of_ne (and_lt (and_lt (Pm_lt _))) (and_lt (Pm_lt _)) heq
      rw [Nat.testBit_and, B.testBit_tr] at hk
      have hkN : (G14.Pm i &&& G14.Pm j).testBit k = true := by
        cases h : (G14.Pm i &&& G14.Pm j).testBit k
        · rw [h] at hk; simp at hk
        · rfl
      have hkF : B.c k ∉ F := by
        intro hm; rw [hkN, decide_eq_true hm] at hk; exact hk rfl
      rw [Nat.testBit_and, Bool.and_eq_true, ← B.hmem, ← B.hmem] at hkN
      have hD := D1 hC (B.hP i) (B.hP j) hF hN (mem_inter.2 hkN) hkF
      have hU := card_union_add_card_inter (F ∩ B.P i) (F ∩ B.P j)
      rw [← inter_union_distrib_left, ← inter_inter_distrib_left, hFN] at hU
      rw [B.xq_eq, B.xq_eq]
      omega

end LBase
end Erdos616R21

namespace Erdos616R21
open G14B
variable {V : Type*} [DecidableEq V]

namespace LBase
variable {H : Finset (Finset V)} (B : LBase H)

theorem tr_UX (X m : ℕ) (hm : ∀ k : Fin 16, m.testBit k = selX X k) (hlt : m < 65536) : B.tr (B.UX X) = m := by
  apply Nat.eq_of_testBit_eq; intro k
  by_cases hk : k < 16
  · have := B.testBit_tr (B.UX X) ⟨k, hk⟩
    simp only at this; rw [this, hm ⟨k, hk⟩]
    have h2 := B.mem_UX_c X ⟨k, hk⟩
    by_cases h : B.c ⟨k, hk⟩ ∈ B.UX X
    · rw [decide_eq_true h, h2.1 h]
    · rw [decide_eq_false h]; cases h3 : selX X k
      · rfl
      · exact absurd (h2.2 h3) h
  · rw [B.testBit_tr_ge _ (by omega),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (n := 2) (by decide) (show 16 ≤ k by omega)))]

theorem UX_O (X : ℕ) (q : Fin 4) (hq : X.testBit q = true) : B.UX X ∩ B.O q = B.O q := by
  have h := B.inter_UX_O (B.O q) X q
  simp only [hq, ↓reduceIte, inter_self] at h
  apply inter_eq_right.2
  intro x hx
  have : x ∈ B.O q ∩ B.UX X ∩ B.O q := by rw [h]; exact hx
  exact (mem_inter.1 (mem_inter.1 this).1).2

/-- L on three base edges and an edge missing their common part -/
theorem L3_edge (hC : Counter H) {F : Finset V} (hF : F ∈ H) (a b c : Fin 4) (X : ℕ)
    (hU : B.UX X = B.P a ∪ B.P b ∪ B.P c)
    (hm : ∀ k : Fin 16, (G14.Pm a ||| G14.Pm b ||| G14.Pm c).testBit k = selX X k)
    (hsel : ∀ g : Fin 4 → ℕ, (if X.testBit 0 then g 0 else 0) + (if X.testBit 1 then g 1 else 0) +
      (if X.testBit 2 then g 2 else 0) + (if X.testBit 3 then g 3 else 0) = g a + g b + g c)
    (hnum : G14.pc (G14.Pm a ||| G14.Pm b ||| G14.Pm c) + (G14.OSZ a + G14.OSZ b + G14.OSZ c) =
      48 + G14.pc (G14.Pm a &&& G14.Pm b &&& G14.Pm c))
    (hab : a ≠ b) :
    (B.tr F &&& (G14.Pm a &&& G14.Pm b &&& G14.Pm c) != 0 ||
      G14.pc (B.tr F &&& (G14.Pm a ||| G14.Pm b ||| G14.Pm c)) +
        ((B.st F).get a + (B.st F).get b + (B.st F).get c) ≤ 8 + G14.pc (G14.Pm a &&& G14.Pm b &&& G14.Pm c)) =
      true := by
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
  by_cases h0 : B.tr F &&& (G14.Pm a &&& G14.Pm b &&& G14.Pm c) = 0
  · right
    have hno : ∀ x, x ∈ B.P a → x ∈ B.P b → x ∈ B.P c → x ∈ F → False := by
      intro x ha hb hc hx
      obtain ⟨k, rfl⟩ := B.hcore a b hab x ha hb
      have : (B.tr F &&& (G14.Pm a &&& G14.Pm b &&& G14.Pm c)).testBit k = true := by
        simp only [Nat.testBit_and, B.testBit_tr, (B.hmem k a).1 ha, (B.hmem k b).1 hb, (B.hmem k c).1 hc]
        simp [hx]
      rw [h0, Nat.zero_testBit] at this; exact Bool.false_ne_true this
    have hL := L4 hC (B.hP a) (B.hP b) (B.hP c) hF hno
    have hUF := card_union_add_card_inter (B.P a ∪ B.P b ∪ B.P c) F
    rw [← hU] at hL hUF
    have hFU := B.card_inter_UX F X _ hm
    rw [inter_comm] at hUF
    have hUU := B.card_inter_UX (B.UX X) X _ hm
    have hlt : G14.Pm a ||| G14.Pm b ||| G14.Pm c < 65536 := by
      show _ < 2 ^ 16
      exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (Pm_lt _) (Pm_lt _)) (Pm_lt _)
    rw [inter_self, B.tr_UX X _ hm hlt, Nat.and_self, hsel (fun q => (B.UX X ∩ B.O q).card)] at hUU
    rw [hsel (fun q => (F ∩ B.O q).card)] at hFU
    have eO : ∀ q : Fin 4, B.P q ⊆ B.UX X → (B.UX X ∩ B.O q) = B.O q :=
      fun q hq => inter_eq_right.2 ((B.O_sub_P q).trans hq)
    rw [eO a (by rw [hU]; intro x hx; simp [hx]), eO b (by rw [hU]; intro x hx; simp [hx]),
      eO c (by rw [hU]; intro x hx; simp [hx]), B.card_O hC a, B.card_O hC b, B.card_O hC c] at hUU
    rw [B.st_get_fin, B.st_get_fin, B.st_get_fin]
    have h21 := hC.unif F hF
    omega
  · left; exact h0

end LBase
end Erdos616R21

namespace G14
theorem Q4_all_fin {p : Nat → Bool} : Q4.all p = true ↔ ∀ q : Fin 4, p q = true := by
  rw [Q4_all]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩ ⟨q, hq⟩
    rcases q with _ | _ | _ | _ | q
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · omega
  · intro h; exact ⟨h 0, h 1, h 2, h 3⟩
end G14

namespace Erdos616R21
open G14B
variable {V : Type*} [DecidableEq V]

namespace LBase
variable {H : Finset (Finset V)} (B : LBase H)

/-- card of `S ∩ (P i ∩ P j)` for `S` arbitrary (it lies in the core) -/
theorem card_inter_N (S : Finset V) {i j : Fin 4} (hij : i ≠ j) :
    (S ∩ (B.P i ∩ B.P j)).card = G14.pc (B.tr S &&& (G14.Pm i &&& G14.Pm j)) :=
  B.card_of_sub_core _ (inter_subset_right.trans (B.inter2_sub_core hij)) _ (fun k => by
    simp only [mem_inter, Nat.testBit_and, B.testBit_tr, Bool.and_eq_true, decide_eq_true_eq, B.hmem])

theorem card_PPN {i j : Fin 4} (hij : i ≠ j) : (B.P i ∩ B.P j).card = 5 := by
  rw [B.card_of_sub_core _ (B.inter2_sub_core hij) (G14.Pm i &&& G14.Pm j) (fun k => by
      simp only [mem_inter, Nat.testBit_and, Bool.and_eq_true, B.hmem])]
  exact pc_N i j hij

/-- two core sets with the same core characterization by single bits are equal as masks -/
theorem eq_singleton_of_card_one {S : Finset V} (h : S.card = 1) : ∃ x, S = {x} := card_eq_one.1 h

/-- per-edge NT (W7-I) at a base 5-pair `(P_i, P_j)` with the base single `P_k` -/
theorem NTb_edge (hW : W7I H) {F : Finset V} (hF : F ∈ H) (i j k : Fin 4) (hij : i ≠ j) :
    (G14.pc (B.tr F &&& (G14.Pm i &&& G14.Pm j)) != 1 ||
      ((k : ℕ) == i || (k : ℕ) == j ||
        (G14.pc (G14.Pm k &&& (G14.Pm i &&& G14.Pm j)) != 1 ||
          (G14.Pm k &&& (G14.Pm i &&& G14.Pm j)) == (B.tr F &&& (G14.Pm i &&& G14.Pm j)) ||
          (2 ≤ G14.pc (B.tr F &&& G14.Pm k &&& G14.Pm i &&& G14.cmp (G14.Pm i &&& G14.Pm j)) &&
           2 ≤ G14.pc (B.tr F &&& G14.Pm k &&& G14.Pm j &&& G14.cmp (G14.Pm i &&& G14.Pm j)))))) = true := by
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
  by_cases h1 : G14.pc (B.tr F &&& (G14.Pm i &&& G14.Pm j)) = 1
  · right
    by_cases hki : (k : ℕ) = i
    · exact Or.inl (Or.inl hki)
    by_cases hkj : (k : ℕ) = j
    · exact Or.inl (Or.inr hkj)
    right
    by_cases h2 : G14.pc (G14.Pm k &&& (G14.Pm i &&& G14.Pm j)) = 1
    · by_cases h3 : (G14.Pm k &&& (G14.Pm i &&& G14.Pm j)) = (B.tr F &&& (G14.Pm i &&& G14.Pm j))
      · exact Or.inl (Or.inr h3)
      · right
        have hki' : k ≠ i := fun h => hki (h ▸ rfl)
        have hkj' : k ≠ j := fun h => hkj (h ▸ rfl)
        rw [← B.card_inter_N F hij] at h1
        have hPk : (B.P k ∩ (B.P i ∩ B.P j)).card = 1 := by
          rw [B.card_inter_N (B.P k) hij, B.tr_P]; exact h2
        obtain ⟨x, hx⟩ := card_eq_one.1 h1
        obtain ⟨y, hy⟩ := card_eq_one.1 hPk
        have hxy : x ≠ y := by
          rintro rfl
          apply h3
          apply Nat.eq_of_testBit_eq; intro t
          by_cases ht : t < 16
          · have e1 : B.c ⟨t, ht⟩ ∈ B.P k ∩ (B.P i ∩ B.P j) ↔ B.c ⟨t, ht⟩ ∈ F ∩ (B.P i ∩ B.P j) := by
              rw [hx, hy]
            simp only [mem_inter, B.hmem] at e1
            have e2 := B.testBit_tr F ⟨t, ht⟩
            simp only at e2
            simp only [Nat.testBit_and, e2]
            cases hk : (G14.Pm k).testBit t <;> cases hi : (G14.Pm i).testBit t <;>
              cases hj : (G14.Pm j).testBit t <;> simp_all
          · have hlt : ∀ m : ℕ, m < 65536 → m.testBit t = false := fun m hm =>
              Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (n := 2) (by decide) (show 16 ≤ t by omega)))
            rw [hlt _ (and_lt (and_lt (Pm_lt _))), hlt _ (and_lt (and_lt (Pm_lt _)))]
        obtain ⟨hA, hC'⟩ := hW (B.P i) (B.hP i) (B.P j) (B.hP j) F hF (B.P k) (B.hP k) (B.card_PPN hij)
          x y hx hy hxy
        have eA : (F ∩ B.P k ∩ (B.P i \ B.P j)).card =
            G14.pc (B.tr F &&& G14.Pm k &&& G14.Pm i &&& G14.cmp (G14.Pm i &&& G14.Pm j)) := by
          apply B.card_of_sub_core
          · intro z hz; simp only [mem_inter, mem_sdiff] at hz
            exact B.inter2_sub_core hki' (mem_inter.2 ⟨hz.1.2, hz.2.1⟩)
          · intro t
            simp only [mem_inter, mem_sdiff, Nat.testBit_and, testBit_cmp, B.testBit_tr, B.hmem]
            cases (G14.Pm k).testBit t <;> cases (G14.Pm i).testBit t <;> cases (G14.Pm j).testBit t <;>
              simp
        have eC : (F ∩ B.P k ∩ (B.P j \ B.P i)).card =
            G14.pc (B.tr F &&& G14.Pm k &&& G14.Pm j &&& G14.cmp (G14.Pm i &&& G14.Pm j)) := by
          apply B.card_of_sub_core
          · intro z hz; simp only [mem_inter, mem_sdiff] at hz
            exact B.inter2_sub_core hkj' (mem_inter.2 ⟨hz.1.2, hz.2.1⟩)
          · intro t
            simp only [mem_inter, mem_sdiff, Nat.testBit_and, testBit_cmp, B.testBit_tr, B.hmem]
            cases (G14.Pm k).testBit t <;> cases (G14.Pm i).testBit t <;> cases (G14.Pm j).testBit t <;>
              simp
        rw [← eA, ← eC]; exact ⟨hA, hC'⟩
    · exact Or.inl (Or.inl h2)
  · exact Or.inl h1

end LBase
end Erdos616R21

namespace G14B
/-- popcount splits along any mask -/
theorem pc_split (x y : ℕ) : G14.pc x = G14.pc (x &&& y) + G14.pc (x &&& G14.cmp y) := by
  simp only [pc_eq_card, Nat.testBit_and, testBit_cmp, Bool.and_eq_true, Bool.not_eq_true']
  rw [← filter_filter, ← filter_filter]
  have := card_filter_add_card_filter_not (s := univ.filter fun i : Fin 16 => x.testBit i = true)
    (fun i : Fin 16 => y.testBit i = true)
  rw [← this]
  congr 2
end G14B

namespace Erdos616R21
open G14B
variable {V : Type*} [DecidableEq V]

namespace LBase
variable {H : Finset (Finset V)} (B : LBase H)

/-- two subsets of the core described by different masks are different -/
theorem ne_of_mask_ne {S1 S2 : Finset V} {m1 m2 : ℕ}
    (h1 : ∀ k : Fin 16, B.c k ∈ S1 ↔ m1.testBit k = true) (h2 : ∀ k : Fin 16, B.c k ∈ S2 ↔ m2.testBit k = true)
    (hm1 : m1 < 65536) (hm2 : m2 < 65536) (hne : m1 ≠ m2) : S1 ≠ S2 := by
  intro hS
  obtain ⟨k, hk⟩ := exists_bit_of_ne hm1 hm2 hne
  apply hk
  have := (h1 k).symm.trans (hS ▸ h2 k)
  cases h : m1.testBit k <;> cases h' : m2.testBit k <;> simp_all

/-- derived 5-pair `(P_i, F)`: R.3 for a base single `P_j`, and D1 -/
theorem derivedA (hC : Counter H) {F : Finset V} (hF : F ∈ H) (i j : Fin 4)
    (h5 : (F ∩ B.P i).card = 5) :
    ((j : ℕ) == i ||
      ((G14.pc (G14.Pm j &&& (B.tr F &&& G14.Pm i)) != 1 || G14.xq (B.tr F) (B.st F) j == 5) &&
       (((B.st F).get i == 0 && (B.tr F &&& G14.Pm i &&& G14.cmp (G14.Pm j)) == 0) ||
         G14.pc (G14.Pm j &&& G14.Pm i) + G14.pc (B.tr F &&& G14.Pm j &&& G14.cmp (G14.Pm i)) +
           (B.st F).get j ≤ 9))) = true := by
  simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq]
  by_cases hji : (j : ℕ) = i
  · exact Or.inl hji
  right
  have hji' : j ≠ i := fun h => hji (h ▸ rfl)
  have hM : (B.P i ∩ F).card = 5 := by rw [inter_comm]; exact h5
  have hsub : B.P j ∩ (B.P i ∩ F) ⊆ B.core := fun z hz => B.inter2_sub_core hji'
    (mem_inter.2 ⟨(mem_inter.1 hz).1, (mem_inter.1 (mem_inter.1 hz).2).1⟩)
  constructor
  · by_cases h1 : G14.pc (G14.Pm j &&& (B.tr F &&& G14.Pm i)) = 1
    · right
      have hc : (B.P j ∩ (B.P i ∩ F)).card = 1 := by
        rw [B.card_of_sub_core _ hsub (G14.Pm j &&& (B.tr F &&& G14.Pm i)) (fun k => by
          simp only [mem_inter, Nat.testBit_and, B.testBit_tr, Bool.and_eq_true, decide_eq_true_eq, B.hmem]
          tauto)]
        exact h1
      obtain ⟨x, hx⟩ := card_eq_one.1 hc
      obtain ⟨-, h2, -⟩ := single_card hC (B.hP i) hF (B.hP j) hM hx
      rw [B.xq_eq, inter_comm]; exact h2
    · exact Or.inl h1
  · by_cases hin : (B.st F).get i = 0 ∧ (B.tr F &&& G14.Pm i &&& G14.cmp (G14.Pm j)) = 0
    · exact Or.inl hin
    · right
      obtain ⟨x, hxi, hxF, hxj⟩ : ∃ x, x ∈ B.P i ∧ x ∈ F ∧ x ∉ B.P j := by
        by_cases ho : (B.st F).get i = 0
        · have hm : (B.tr F &&& G14.Pm i &&& G14.cmp (G14.Pm j)) ≠ 0 := fun h => hin ⟨ho, h⟩
          obtain ⟨k, hk⟩ := exists_bit_of_ne (and_lt (show G14.cmp (G14.Pm j) < 65536 by
            unfold G14.cmp; show _ < 2 ^ 16; exact Nat.xor_lt_two_pow (by decide) (Pm_lt _))) (by decide : (0:ℕ) < 65536) hm
          rw [Nat.zero_testBit, Nat.testBit_and, Nat.testBit_and, testBit_cmp, B.testBit_tr] at hk
          refine ⟨B.c k, (B.hmem k i).2 ?_, ?_, fun h => ?_⟩
          · cases h' : (G14.Pm i).testBit k <;> simp_all
          · by_contra h'; simp_all
          · rw [B.hmem] at h; simp_all
        · rw [B.st_get_fin] at ho
          obtain ⟨x, hx⟩ := card_pos.1 (Nat.pos_of_ne_zero ho)
          rw [mem_inter] at hx
          exact ⟨x, B.O_sub_P i hx.2, hx.1, fun h => B.O_disj hji'.symm hx.2 h⟩
      have hD := D1 hC (B.hP i) hF (B.hP j) hM (mem_inter.2 ⟨hxi, hxF⟩) hxj
      -- |P_j ∩ (P_i ∪ F)| = |P_j ∩ P_i| + |P_j ∩ F| - |P_j ∩ P_i ∩ F|
      have hU := card_union_add_card_inter (B.P j ∩ B.P i) (B.P j ∩ F)
      rw [← inter_union_distrib_left] at hU
      have e1 : B.P j ∩ B.P i ∩ (B.P j ∩ F) = F ∩ (B.P j ∩ B.P i) := by
        ext z; simp only [mem_inter]; tauto
      rw [e1, B.card_inter_N F hji'.symm.symm, B.card_PPN hji'] at hU
      have e2 := B.card_inter_P F j
      rw [inter_comm] at e2
      have hsp := pc_split (B.tr F &&& G14.Pm j) (G14.Pm i)
      have e3 : (B.tr F &&& G14.Pm j &&& G14.Pm i) = (B.tr F &&& (G14.Pm j &&& G14.Pm i)) := Nat.and_assoc _ _ _
      rw [e3] at hsp
      rw [B.st_get_fin, pc_N j i hji']
      omega

end LBase
end Erdos616R21

namespace Erdos616R21
open G14B
variable {V : Type*} [DecidableEq V]

namespace LBase
variable {H : Finset (Finset V)} (B : LBase H)

theorem cmp_lt (y : ℕ) (hy : y < 65536) : G14.cmp y < 65536 := by
  unfold G14.cmp; show _ < 2 ^ 16; exact Nat.xor_lt_two_pow (by decide) hy

/-- derived 5-pair `(P_i, F)` with two base singles `P_j`, `P_k` of different types: W7-I and S(a) -/
theorem derivedB (hC : Counter H) (hW : W7I H) {F : Finset V} (hF : F ∈ H) (i j k : Fin 4)
    (h5 : (F ∩ B.P i).card = 5) :
    (!(decide ((j : ℕ) < k)) || (j : ℕ) == i || (k : ℕ) == i ||
      G14.pc (G14.Pm j &&& (B.tr F &&& G14.Pm i)) != 1 || G14.pc (G14.Pm k &&& (B.tr F &&& G14.Pm i)) != 1 ||
      (G14.Pm j &&& (B.tr F &&& G14.Pm i)) == (G14.Pm k &&& (B.tr F &&& G14.Pm i)) ||
      (G14.pc (G14.Pm i &&& G14.Pm j &&& G14.Pm k &&& G14.cmp (B.tr F)) != 1 &&
       G14.pc (B.tr F &&& G14.Pm j &&& G14.Pm k &&& G14.cmp (G14.Pm i)) != 1 &&
       (G14.Pm j &&& G14.Pm k &&& G14.cmp (G14.Pm i) &&& G14.cmp (B.tr F)) == 0)) = true := by
  simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, Nat.not_lt]
  by_cases hjk : (j : ℕ) < k
  swap; · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (by omega))))))
  by_cases hji : (j : ℕ) = i; · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hji)))))
  by_cases hki : (k : ℕ) = i; · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hki))))
  have hji' : j ≠ i := fun h => hji (h ▸ rfl)
  have hki' : k ≠ i := fun h => hki (h ▸ rfl)
  have hjk' : j ≠ k := fun h => by rw [h] at hjk; exact lt_irrefl _ hjk
  by_cases h1 : G14.pc (G14.Pm j &&& (B.tr F &&& G14.Pm i)) = 1
  swap; · exact Or.inl (Or.inl (Or.inl (Or.inr h1)))
  by_cases h2 : G14.pc (G14.Pm k &&& (B.tr F &&& G14.Pm i)) = 1
  swap; · exact Or.inl (Or.inl (Or.inr h2))
  by_cases h3 : (G14.Pm j &&& (B.tr F &&& G14.Pm i)) = (G14.Pm k &&& (B.tr F &&& G14.Pm i))
  · exact Or.inl (Or.inr h3)
  right
  have hM : (B.P i ∩ F).card = 5 := by rw [inter_comm]; exact h5
  have chJ : ∀ t : Fin 16, B.c t ∈ B.P j ∩ (B.P i ∩ F) ↔ (G14.Pm j &&& (B.tr F &&& G14.Pm i)).testBit t = true := by
    intro t; simp only [mem_inter, Nat.testBit_and, B.testBit_tr, Bool.and_eq_true, decide_eq_true_eq, B.hmem]; tauto
  have chK : ∀ t : Fin 16, B.c t ∈ B.P k ∩ (B.P i ∩ F) ↔ (G14.Pm k &&& (B.tr F &&& G14.Pm i)).testBit t = true := by
    intro t; simp only [mem_inter, Nat.testBit_and, B.testBit_tr, Bool.and_eq_true, decide_eq_true_eq, B.hmem]; tauto
  have sJ : B.P j ∩ (B.P i ∩ F) ⊆ B.core := fun z hz => B.inter2_sub_core hji'
    (mem_inter.2 ⟨(mem_inter.1 hz).1, (mem_inter.1 (mem_inter.1 hz).2).1⟩)
  have sK : B.P k ∩ (B.P i ∩ F) ⊆ B.core := fun z hz => B.inter2_sub_core hki'
    (mem_inter.2 ⟨(mem_inter.1 hz).1, (mem_inter.1 (mem_inter.1 hz).2).1⟩)
  obtain ⟨x, hx⟩ := card_eq_one.1 ((B.card_of_sub_core _ sJ _ chJ).trans h1)
  obtain ⟨y, hy⟩ := card_eq_one.1 ((B.card_of_sub_core _ sK _ chK).trans h2)
  have hxy : x ≠ y := by
    rintro rfl
    exact B.ne_of_mask_ne chJ chK (and_lt (and_lt (Pm_lt _))) (and_lt (and_lt (Pm_lt _))) h3 (hx.trans hy.symm)
  obtain ⟨hA, hC'⟩ := hW (B.P i) (B.hP i) F hF (B.P j) (B.hP j) (B.P k) (B.hP k) hM x y hx hy hxy
  have sjk : B.P j ∩ B.P k ⊆ B.core := B.inter2_sub_core hjk'
  have eA : (B.P j ∩ B.P k ∩ (B.P i \ F)).card = G14.pc (G14.Pm i &&& G14.Pm j &&& G14.Pm k &&& G14.cmp (B.tr F)) := by
    apply B.card_of_sub_core _ (inter_subset_left.trans sjk)
    intro t
    simp only [mem_inter, mem_sdiff, Nat.testBit_and, testBit_cmp, B.testBit_tr, B.hmem]
    by_cases hF' : B.c t ∈ F <;> simp [hF'] <;> tauto
  have eC : (B.P j ∩ B.P k ∩ (F \ B.P i)).card = G14.pc (B.tr F &&& G14.Pm j &&& G14.Pm k &&& G14.cmp (G14.Pm i)) := by
    apply B.card_of_sub_core _ (inter_subset_left.trans sjk)
    intro t
    simp only [mem_inter, mem_sdiff, Nat.testBit_and, testBit_cmp, B.testBit_tr, B.hmem]
    by_cases hF' : B.c t ∈ F <;> simp [hF'] <;> tauto
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  have hdis := S_a_O hC (B.hP i) hF (B.hP j) (B.hP k) hM hx hy hxy
  by_contra hne
  obtain ⟨t, ht⟩ := exists_bit_of_ne
    (and_lt (cmp_lt _ (B.tr_lt F))) (by decide : (0 : ℕ) < 65536) hne
  rw [Nat.zero_testBit, Nat.testBit_and, Nat.testBit_and, Nat.testBit_and, testBit_cmp, testBit_cmp,
    B.testBit_tr] at ht
  have hj : (G14.Pm j).testBit t = true := by cases h : (G14.Pm j).testBit t <;> simp_all
  have hk : (G14.Pm k).testBit t = true := by cases h : (G14.Pm k).testBit t <;> simp_all
  have hi : (G14.Pm i).testBit t = false := by cases h : (G14.Pm i).testBit t <;> simp_all
  have hf : B.c t ∉ F := by intro hm; simp_all
  have hi' : B.c t ∉ B.P i := by rw [B.hmem]; simp [hi]
  exact Finset.disjoint_left.1 hdis (by simp [(B.hmem t j).2 hj, hi', hf] : B.c t ∈ B.P j \ (B.P i ∪ F))
    (by simp [(B.hmem t k).2 hk, hi', hf])

end LBase
end Erdos616R21

namespace G14B
theorem band_of {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by simp [ha, hb]
theorem bor_right {a b : Bool} (hb : b = true) : (a || b) = true := by simp [hb]
end G14B

namespace Erdos616R21
open G14B
variable {V : Type*} [DecidableEq V]

namespace LBase
variable {H : Finset (Finset V)} (B : LBase H)

theorem okBasic_edge (hC : Counter H) {F : Finset V} (hF : F ∈ H) :
    G14.okBasic (B.tr F) (B.st F) = true := by
  unfold G14.okBasic
  refine band_of (band_of ?_ ?_) ?_
  · rw [G14.Q4_all_fin]; intro q
    rw [decide_eq_true_eq, B.st_get_fin, ← B.card_O hC q]
    exact card_le_card inter_subset_right
  · rw [decide_eq_true_eq]
    have hp := B.edge_part hC hF
    have hs : (B.st F).sum = (F ∩ B.O 0).card + (F ∩ B.O 1).card + (F ∩ B.O 2).card + (F ∩ B.O 3).card := by
      have h0 : B.ov F 0 = (F ∩ B.O 0).card := B.ov_eq F 0
      have h1 : B.ov F 1 = (F ∩ B.O 1).card := B.ov_eq F 1
      have h2 : B.ov F 2 = (F ∩ B.O 2).card := B.ov_eq F 2
      have h3 : B.ov F 3 = (F ∩ B.O 3).card := B.ov_eq F 3
      show B.ov F 0 + B.ov F 1 + B.ov F 2 + B.ov F 3 = _
      rw [h0, h1, h2, h3]
    rw [hs]; omega
  · rw [G14.Q4_all_fin]; intro q
    rw [decide_eq_true_eq, B.xq_eq]
    exact inter_ge5 hC hF (B.hP q)

theorem okF1D1_edge (hC : Counter H) {F : Finset V} (hF : F ∈ H) :
    G14.okF1D1 (B.tr F) (B.st F) = true := by
  unfold G14.okF1D1
  rw [List.all_eq_true]
  intro p hp
  simp only [G14.PR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B.F1D1_edge hC hF 0 1 (by decide)
  · exact B.F1D1_edge hC hF 0 2 (by decide)
  · exact B.F1D1_edge hC hF 0 3 (by decide)
  · exact B.F1D1_edge hC hF 1 2 (by decide)
  · exact B.F1D1_edge hC hF 1 3 (by decide)
  · exact B.F1D1_edge hC hF 2 3 (by decide)

theorem okNTb_edge (hW : W7I H) {F : Finset V} (hF : F ∈ H) : G14.okNTb (B.tr F) = true := by
  unfold G14.okNTb
  rw [List.all_eq_true]
  intro p hp
  have key : ∀ i j : Fin 4, i ≠ j →
      (G14.pc (B.tr F &&& (G14.Pm i &&& G14.Pm j)) != 1 ||
        G14.Q4.all (fun k => k == (i : ℕ) || k == (j : ℕ) ||
          (G14.pc (G14.Pm k &&& (G14.Pm i &&& G14.Pm j)) != 1 ||
            (G14.Pm k &&& (G14.Pm i &&& G14.Pm j)) == (B.tr F &&& (G14.Pm i &&& G14.Pm j)) ||
            (2 ≤ G14.pc (B.tr F &&& G14.Pm k &&& G14.Pm i &&& G14.cmp (G14.Pm i &&& G14.Pm j)) &&
             2 ≤ G14.pc (B.tr F &&& G14.Pm k &&& G14.Pm j &&& G14.cmp (G14.Pm i &&& G14.Pm j)))))) = true := by
    intro i j hij
    by_cases h1 : G14.pc (B.tr F &&& (G14.Pm i &&& G14.Pm j)) = 1
    · apply bor_right
      rw [G14.Q4_all_fin]; intro k
      have h := B.NTb_edge hW hF i j k hij
      have hf : (G14.pc (B.tr F &&& (G14.Pm i &&& G14.Pm j)) != 1) = false := by simp [h1]
      rw [hf, Bool.false_or] at h
      exact h
    · simp [h1]
  simp only [G14.PR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact key 0 1 (by decide)
  · exact key 0 2 (by decide)
  · exact key 0 3 (by decide)
  · exact key 1 2 (by decide)
  · exact key 1 3 (by decide)
  · exact key 2 3 (by decide)

theorem okDer_edge (hC : Counter H) (hW : W7I H) {F : Finset V} (hF : F ∈ H) :
    G14.Q4.all (fun i => G14.xq (B.tr F) (B.st F) i != 5 || G14.okDerived (B.tr F) (B.st F) i) = true := by
  rw [G14.Q4_all_fin]; intro i
  by_cases h5 : G14.xq (B.tr F) (B.st F) i = 5
  · apply bor_right
    rw [B.xq_eq] at h5
    unfold G14.okDerived
    refine band_of ?_ ?_
    · rw [G14.Q4_all_fin]; intro j; exact B.derivedA hC hF i j h5
    · rw [G14.Q4_all_fin]; intro j; rw [G14.Q4_all_fin]; intro k; exact B.derivedB hC hW hF i j k h5
  · simp [h5]

end LBase
end Erdos616R21

namespace Erdos616R21
open G14B
variable {V : Type*} [DecidableEq V]

namespace LBase
variable {H : Finset (Finset V)} (B : LBase H)

theorem okL3_edge (hC : Counter H) {F : Finset V} (hF : F ∈ H) : G14.okL3 (B.tr F) (B.st F) = true := by
  unfold G14.okL3
  rw [List.all_eq_true]
  intro T hT
  simp only [G14.TR, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl
  · refine B.L3_edge hC hF 0 1 2 7 ?_ (by decide) ?_ (by decide) (by decide)
    · unfold UX; rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_neg (by decide), union_empty]
    · intro g; rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_neg (by decide)]; rfl
  · refine B.L3_edge hC hF 0 1 3 11 ?_ (by decide) ?_ (by decide) (by decide)
    · unfold UX; rw [if_pos (by decide), if_pos (by decide), if_neg (by decide), if_pos (by decide), union_empty]
    · intro g; rw [if_pos (by decide), if_pos (by decide), if_neg (by decide), if_pos (by decide)]; rfl
  · refine B.L3_edge hC hF 0 2 3 13 ?_ (by decide) ?_ (by decide) (by decide)
    · unfold UX; rw [if_pos (by decide), if_neg (by decide), if_pos (by decide), if_pos (by decide), union_empty]
    · intro g; rw [if_pos (by decide), if_neg (by decide), if_pos (by decide), if_pos (by decide)]; rfl
  · refine B.L3_edge hC hF 1 2 3 14 ?_ (by decide) ?_ (by decide) (by decide)
    · unfold UX; rw [if_neg (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide), empty_union]
    · intro g; rw [if_neg (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)]; simp

/-- **Per-edge soundness (S13.1 rules) — proved.** -/
theorem edgeSound (hC : Counter H) (hW : W7I H) : B.EdgeSound := by
  intro F hF _
  unfold G14.ok
  exact band_of (band_of (band_of (band_of (B.okBasic_edge hC hF) (B.okF1D1_edge hC hF)) (B.okL3_edge hC hF))
    (B.okNTb_edge hW hF)) (B.okDer_edge hC hW hF)

end LBase
end Erdos616R21
