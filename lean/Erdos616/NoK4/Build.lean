import Erdos616.NoK4.Base

/-!
# Upstream lemma: a cross pair of class `(a, c)` yields a labelled `Base` of the matching class

For a 5-pair `(X, Y)` with cross-type singles `G` (type `v`), `G'` (type `w ≠ v`) the Venn regions of
`(X, Y, G, G')` are forced (single_card, cross_class): `X∩Y∖(G∪G')` has 3 points, `{v}`, `{w}`,
`G∩G'∩(X∖Y)` has `a`, `G∩(X∖Y)` only and `G'∩(X∖Y)` only have `4-a`, symmetrically `c`, `4-c` on `Y∖X`,
and the regions `G∩G'∖(X∪Y)` and `X∩Y∩G∩G'` are empty. Given that the masks of a class `C` have exactly these
region counts (checked by `decide`), we enumerate each region and label the core points accordingly.
Base edges: `P 0 = X`, `P 1 = Y`, `P 2 = G`, `P 3 = G'`.
-/

open Finset TrCheck

namespace Erdos616R21.NoK4

theorem getD_eq' {α : Type*} {l : List α} {d : α} {n : ℕ} (h : n < l.length) : l.getD n d = l[n] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- the 4-bit pattern of four Booleans -/
def pat4 (b0 b1 b2 b3 : Bool) : ℕ :=
  (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) + (if b3 then 8 else 0)

theorem pat4_lt (b0 b1 b2 b3 : Bool) : pat4 b0 b1 b2 b3 < 16 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem testBit_pat4 (b0 b1 b2 b3 : Bool) :
    (pat4 b0 b1 b2 b3).testBit 0 = b0 ∧ (pat4 b0 b1 b2 b3).testBit 1 = b1 ∧
    (pat4 b0 b1 b2 b3).testBit 2 = b2 ∧ (pat4 b0 b1 b2 b3).testBit 3 = b3 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

def sel (b0 b1 b2 b3 : Bool) : ℕ → Bool
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | _ => b3

theorem testBit_pat4' (b0 b1 b2 b3 : Bool) {q : ℕ} (hq : q < 4) :
    (pat4 b0 b1 b2 b3).testBit q = sel b0 b1 b2 b3 q := by
  obtain ⟨h0, h1, h2, h3⟩ := testBit_pat4 b0 b1 b2 b3
  rcases q4_cases hq with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- a pattern with at least two bits -/
def multi (p : ℕ) : Bool := !(p == 0 || p == 1 || p == 2 || p == 4 || p == 8)

theorem multi_of_two_fin : ∀ p : Fin 16, ∀ q : Fin 4, ∀ r : Fin 4, q ≠ r → (p : ℕ).testBit q = true →
    (p : ℕ).testBit r = true → multi p = true := by decide

theorem multi_of_two (p : ℕ) (hp : p < 16) (q : ℕ) (hq : q < 4) (r : ℕ) (hr : r < 4) (hqr : q ≠ r)
    (h1 : p.testBit q = true) (h2 : p.testBit r = true) : multi p = true :=
  multi_of_two_fin ⟨p, hp⟩ ⟨q, hq⟩ ⟨r, hr⟩ (fun h => hqr (congrArg Fin.val h)) h1 h2

/-- forced region sizes, indexed by pattern (bit 0 `X`, bit 1 `Y`, bit 2 `G`, bit 3 `G'`) -/
def regf (a c : ℕ) : ℕ → ℕ
  | 3 => 3
  | 5 => 4 - a
  | 6 => 4 - c
  | 7 => 1
  | 9 => 4 - a
  | 10 => 4 - c
  | 11 => 1
  | 13 => a
  | 14 => c
  | _ => 0

/-- pattern of core index `i` in class `C` -/
def patC (C : Cls) (i : ℕ) : ℕ :=
  pat4 ((C.P 0).testBit i) ((C.P 1).testBit i) ((C.P 2).testBit i) ((C.P 3).testBit i)

theorem testBit_patC (C : Cls) (i : ℕ) {q : ℕ} (hq : q < 4) : (patC C i).testBit q = (C.P q).testBit i := by
  rw [patC, testBit_pat4' _ _ _ _ hq]
  rcases q4_cases hq with rfl | rfl | rfl | rfl <;> rfl

def cnt (C : Cls) (p : ℕ) : ℕ := ((range C.n).filter (fun i => patC C i = p)).card
def rank (C : Cls) (i : ℕ) : ℕ := ((range i).filter (fun j => patC C j = patC C i)).card

theorem rank_lt_cnt (C : Cls) {i : ℕ} (hi : i < C.n) : rank C i < cnt C (patC C i) := by
  apply card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨i, by simp [hi], by simp⟩
  · intro j; simp only [mem_filter, mem_range]; omega

theorem rank_strict (C : Cls) {i j : ℕ} (hij : i < j) (hp : patC C i = patC C j) : rank C i < rank C j := by
  unfold rank
  rw [hp]
  apply card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨i, by simp [hij, hp], by simp⟩
  · intro k; simp only [mem_filter, mem_range]; omega

theorem rank_inj (C : Cls) {i j : ℕ} (hp : patC C i = patC C j) (hr : rank C i = rank C j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := rank_strict C h hp; omega
  · exact h
  · have := rank_strict C h hp.symm; omega

theorem rank_surj (C : Cls) (p : ℕ) {k : ℕ} (hk : k < cnt C p) :
    ∃ i, i < C.n ∧ patC C i = p ∧ rank C i = k := by
  set S := (range C.n).filter (fun i => patC C i = p) with hS
  have hsub : S.image (rank C) ⊆ range (cnt C p) := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hr
    simp only [hS, mem_filter, mem_range] at hi
    have := rank_lt_cnt C hi.1
    rw [hi.2] at this
    exact mem_range.2 this
  have hcard : (S.image (rank C)).card = cnt C p := by
    rw [card_image_of_injOn]
    · rfl
    · intro i hi j hj h
      simp only [Finset.mem_coe, hS, mem_filter, mem_range] at hi hj
      exact rank_inj C (hi.2.trans hj.2.symm) h
  have heq : S.image (rank C) = range (cnt C p) :=
    eq_of_subset_of_card_le hsub (le_of_eq (by rw [hcard, card_range]))
  have : k ∈ S.image (rank C) := by rw [heq]; exact mem_range.2 hk
  obtain ⟨i, hi, rfl⟩ := mem_image.1 this
  simp only [hS, mem_filter, mem_range] at hi
  exact ⟨i, hi.1, hi.2, rfl⟩

variable {V : Type*} [DecidableEq V]

/-- membership pattern of `x` in `E 0, …, E 3` -/
def pat (E : ℕ → Finset V) (x : V) : ℕ :=
  pat4 (decide (x ∈ E 0)) (decide (x ∈ E 1)) (decide (x ∈ E 2)) (decide (x ∈ E 3))

theorem testBit_pat (E : ℕ → Finset V) (x : V) {q : ℕ} (hq : q < 4) :
    (pat E x).testBit q = true ↔ x ∈ E q := by
  rw [pat, testBit_pat4' _ _ _ _ hq]
  rcases q4_cases hq with rfl | rfl | rfl | rfl <;> simp [sel]

def UU (E : ℕ → Finset V) : Finset V := E 0 ∪ E 1 ∪ E 2 ∪ E 3

/-- the region of pattern `p` -/
def R (E : ℕ → Finset V) (p : ℕ) : Finset V := (UU E).filter (fun x => pat E x = p)

theorem mem_UU (E : ℕ → Finset V) {x : V} {q : ℕ} (hq : q < 4) (hx : x ∈ E q) : x ∈ UU E := by
  simp only [UU, mem_union]
  rcases q4_cases hq with rfl | rfl | rfl | rfl <;> tauto

/-- the labelling: core index `i` is the `rank i`-th point of the region of its pattern -/
noncomputable def coreOf (C : Cls) (E : ℕ → Finset V) (x0 : V) (i : ℕ) : V :=
  (R E (patC C i)).toList.getD (rank C i) x0

section mk
variable (C : Cls) (E : ℕ → Finset V) (x0 : V)
  (hm : ∀ i, i < C.n → multi (patC C i) = true)
  (hcnt : ∀ p, p < 16 → multi p = true → (R E p).card = cnt C p)
include hm hcnt

theorem rank_lt_len {i : ℕ} (hi : i < C.n) : rank C i < (R E (patC C i)).toList.length := by
  rw [length_toList, hcnt (patC C i) (pat4_lt _ _ _ _) (hm i hi)]
  exact rank_lt_cnt C hi

theorem coreOf_mem {i : ℕ} (hi : i < C.n) : coreOf C E x0 i ∈ R E (patC C i) := by
  have hl := rank_lt_len C E hm hcnt hi
  unfold coreOf
  rw [getD_eq' hl]
  exact mem_toList.1 (List.getElem_mem hl)

theorem coreOf_pat {i : ℕ} (hi : i < C.n) : pat E (coreOf C E x0 i) = patC C i :=
  (mem_filter.1 (coreOf_mem C E x0 hm hcnt hi)).2

/-- the base built from the labelling -/
noncomputable def mkBase {H : Finset (Finset V)} (hE : ∀ q, q < 4 → E q ∈ H) : Base C H where
  core := coreOf C E x0
  P := E
  core_inj := by
    intro i j hi hj h
    have hpi := coreOf_pat C E x0 hm hcnt hi
    have hpj := coreOf_pat C E x0 hm hcnt hj
    have hp : patC C i = patC C j := by rw [← hpi, ← hpj, h]
    have hli := rank_lt_len C E hm hcnt hi
    have hlj := rank_lt_len C E hm hcnt hj
    rw [← hp] at hlj
    have h' : (R E (patC C i)).toList[rank C i] = (R E (patC C i)).toList[rank C j] := by
      have e1 : coreOf C E x0 i = (R E (patC C i)).toList[rank C i] := by
        unfold coreOf; rw [getD_eq' hli]
      have e2 : coreOf C E x0 j = (R E (patC C i)).toList[rank C j] := by
        unfold coreOf; rw [← hp, getD_eq' hlj]
      rw [← e1, ← e2, h]
    rw [(nodup_toList _).getElem_inj_iff] at h'
    exact rank_inj C hp h'
  P_mem := hE
  P_core := by
    intro q i hq hi
    rw [← testBit_pat E _ hq, coreOf_pat C E x0 hm hcnt hi, testBit_patC C i hq]
  two := by
    intro q r x hq hr hqr hxq hxr
    have hp16 : pat E x < 16 := pat4_lt _ _ _ _
    have hmul : multi (pat E x) = true :=
      multi_of_two _ hp16 q hq r hr hqr ((testBit_pat E x hq).2 hxq) ((testBit_pat E x hr).2 hxr)
    have hxR : x ∈ (R E (pat E x)).toList := mem_toList.2 (mem_filter.2 ⟨mem_UU E hq hxq, rfl⟩)
    obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.1 hxR
    have hk' : k < cnt C (pat E x) := by
      rw [← hcnt _ hp16 hmul, ← length_toList]; exact hk
    obtain ⟨i, hi, hpi, hri⟩ := rank_surj C _ hk'
    refine ⟨i, hi, ?_⟩
    have hl := rank_lt_len C E hm hcnt hi
    have hfin : (R E (patC C i)).toList.getD (rank C i) x0 = x := by
      rw [hpi, hri, getD_eq' hk]; exact hkx
    exact hfin

end mk

/-! ### the forced regions of a cross pair -/

def E4 (X Y G G' : Finset V) : ℕ → Finset V
  | 0 => X
  | 1 => Y
  | 2 => G
  | 3 => G'
  | _ => ∅

theorem card_eq_sum_R (E : ℕ → Finset V) (s : Finset V) (T : Finset ℕ)
    (hs : ∀ x, x ∈ s ↔ x ∈ UU E ∧ pat E x ∈ T) : s.card = ∑ p ∈ T, (R E p).card := by
  rw [card_eq_sum_card_fiberwise (f := pat E) (t := T) (fun x hx => ((hs x).1 hx).2)]
  apply sum_congr rfl
  intro p hp
  congr 1
  ext x
  simp only [mem_filter, R]
  constructor
  · rintro ⟨hx, rfl⟩; exact ⟨((hs x).1 hx).1, rfl⟩
  · rintro ⟨hx, rfl⟩; exact ⟨(hs x).2 ⟨hx, hp⟩, rfl⟩

section regions
variable {H : Finset (Finset V)}

theorem regions (hC : Counter H) {X Y G G' : Finset V} (hX : X ∈ H) (hY : Y ∈ H) (hG : G ∈ H)
    (hG' : G' ∈ H) (hM : (X ∩ Y).card = 5) {v w : V} (hv : G ∩ (X ∩ Y) = {v}) (hw : G' ∩ (X ∩ Y) = {w})
    (hvw : v ≠ w) :
    ∀ p, p < 16 → multi p = true →
      (R (E4 X Y G G') p).card = regf (G ∩ G' ∩ (X \ Y)).card (G ∩ G' ∩ (Y \ X)).card p := by
  set E := E4 X Y G G' with hE
  obtain ⟨hGX, hGY, -⟩ := Erdos616R21.single_card hC hX hY hG hM hv
  obtain ⟨hG'X, hG'Y, -⟩ := Erdos616R21.single_card hC hX hY hG' hM hw
  have hcc := Erdos616R21.cross_class hC hX hY hG hG' hM hv hw hvw
  have hGG' := hcc.2.2.2.2.2
  have hv1 : (G ∩ (X ∩ Y)).card = 1 := by rw [hv, card_singleton]
  have hw1 : (G' ∩ (X ∩ Y)).card = 1 := by rw [hw, card_singleton]
  have h0 : (G ∩ G' ∩ (X ∩ Y)).card = 0 := by
    rw [card_eq_zero, eq_empty_iff_forall_notMem]
    intro x hx
    have h1 : x ∈ G ∩ (X ∩ Y) := by simp only [mem_inter] at hx ⊢; tauto
    have h2 : x ∈ G' ∩ (X ∩ Y) := by simp only [mem_inter] at hx ⊢; tauto
    rw [hv, mem_singleton] at h1; rw [hw, mem_singleton] at h2
    exact hvw (h1.symm.trans h2)
  have s1 := card_eq_sum_R E (X ∩ Y) {3, 7, 11, 15} (by
    intro x; by_cases h0 : x ∈ X <;> by_cases h1 : x ∈ Y <;> by_cases h2 : x ∈ G <;>
      by_cases h3 : x ∈ G' <;> simp [hE, UU, E4, pat, pat4, h0, h1, h2, h3])
  have s2 := card_eq_sum_R E (G ∩ X) {5, 7, 13, 15} (by
    intro x; by_cases h0 : x ∈ X <;> by_cases h1 : x ∈ Y <;> by_cases h2 : x ∈ G <;>
      by_cases h3 : x ∈ G' <;> simp [hE, UU, E4, pat, pat4, h0, h1, h2, h3])
  have s3 := card_eq_sum_R E (G' ∩ X) {9, 11, 13, 15} (by
    intro x; by_cases h0 : x ∈ X <;> by_cases h1 : x ∈ Y <;> by_cases h2 : x ∈ G <;>
      by_cases h3 : x ∈ G' <;> simp [hE, UU, E4, pat, pat4, h0, h1, h2, h3])
  have s4 := card_eq_sum_R E (G ∩ Y) {6, 7, 14, 15} (by
    intro x; by_cases h0 : x ∈ X <;> by_cases h1 : x ∈ Y <;> by_cases h2 : x ∈ G <;>
      by_cases h3 : x ∈ G' <;> simp [hE, UU, E4, pat, pat4, h0, h1, h2, h3])
  have s5 := card_eq_sum_R E (G' ∩ Y) {10, 11, 14, 15} (by
    intro x; by_cases h0 : x ∈ X <;> by_cases h1 : x ∈ Y <;> by_cases h2 : x ∈ G <;>
      by_cases h3 : x ∈ G' <;> simp [hE, UU, E4, pat, pat4, h0, h1, h2, h3])
  have s6 := card_eq_sum_R E (G ∩ G') {12, 13, 14, 15} (by
    intro x; by_cases h0 : x ∈ X <;> by_cases h1 : x ∈ Y <;> by_cases h2 : x ∈ G <;>
      by_cases h3 : x ∈ G' <;> simp [hE, UU, E4, pat, pat4, h0, h1, h2, h3])
  have s7 := card_eq_sum_R E (G ∩ (X ∩ Y)) {7, 15} (by
    intro x; by_cases h0 : x ∈ X <;> by_cases h1 : x ∈ Y <;> by_cases h2 : x ∈ G <;>
      by_cases h3 : x ∈ G' <;> simp [hE, UU, E4, pat, pat4, h0, h1, h2, h3])
  have s8 := card_eq_sum_R E (G' ∩ (X ∩ Y)) {11, 15} (by
    intro x; by_cases h0 : x ∈ X <;> by_cases h1 : x ∈ Y <;> by_cases h2 : x ∈ G <;>
      by_cases h3 : x ∈ G' <;> simp [hE, UU, E4, pat, pat4, h0, h1, h2, h3])
  have s9 := card_eq_sum_R E (G ∩ G' ∩ (X \ Y)) {13} (by
    intro x; by_cases h0 : x ∈ X <;> by_cases h1 : x ∈ Y <;> by_cases h2 : x ∈ G <;>
      by_cases h3 : x ∈ G' <;> simp [hE, UU, E4, pat, pat4, h0, h1, h2, h3])
  have s10 := card_eq_sum_R E (G ∩ G' ∩ (Y \ X)) {14} (by
    intro x; by_cases h0 : x ∈ X <;> by_cases h1 : x ∈ Y <;> by_cases h2 : x ∈ G <;>
      by_cases h3 : x ∈ G' <;> simp [hE, UU, E4, pat, pat4, h0, h1, h2, h3])
  have s11 := card_eq_sum_R E (G ∩ G' ∩ (X ∩ Y)) {15} (by
    intro x; by_cases h0 : x ∈ X <;> by_cases h1 : x ∈ Y <;> by_cases h2 : x ∈ G <;>
      by_cases h3 : x ∈ G' <;> simp [hE, UU, E4, pat, pat4, h0, h1, h2, h3])
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at s1
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at s2
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at s3
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at s4
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at s5
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at s6
  rw [Finset.sum_insert (by decide), Finset.sum_singleton] at s7
  rw [Finset.sum_insert (by decide), Finset.sum_singleton] at s8
  rw [Finset.sum_singleton] at s9
  rw [Finset.sum_singleton] at s10
  rw [Finset.sum_singleton] at s11
  intro p hp hmul
  have hp' : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨
      p = 11 ∨ p = 12 ∨ p = 13 ∨ p = 14 ∨ p = 15 := by omega
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd hmul (by decide) | (simp only [regf]; omega)

end regions

/-- **Upstream lemma.** A cross pair `(X, Y; G, G')` whose class `(a, c)` has the region counts of class `C`
(`regf a c p = cnt C p` for every multi-bit pattern, and every core index of `C` has a multi-bit pattern) gives a
labelled base of class `C` with `P 0 = X`, `P 1 = Y`, `P 2 = G`, `P 3 = G'`. -/
theorem base_of_cross (C : Cls) {H : Finset (Finset V)} (hC : Counter H) {X Y G G' : Finset V} (hX : X ∈ H)
    (hY : Y ∈ H) (hG : G ∈ H) (hG' : G' ∈ H) (hM : (X ∩ Y).card = 5) {v w : V} (hv : G ∩ (X ∩ Y) = {v})
    (hw : G' ∩ (X ∩ Y) = {w}) (hvw : v ≠ w)
    (hm : ∀ i, i < C.n → multi (patC C i) = true)
    (hcnt : ∀ p, p < 16 → multi p = true →
      regf (G ∩ G' ∩ (X \ Y)).card (G ∩ G' ∩ (Y \ X)).card p = cnt C p) :
    Nonempty (Base C H) := by
  have hreg := regions hC hX hY hG hG' hM hv hw hvw
  refine ⟨mkBase C (E4 X Y G G') v hm (fun p hp hmul => (hreg p hp hmul).trans (hcnt p hp hmul)) ?_⟩
  intro q hq
  rcases q4_cases hq with rfl | rfl | rfl | rfl
  · exact hX
  · exact hY
  · exact hG
  · exact hG'

theorem multi34 : ∀ i : ℕ, i < cls34.n → multi (patC cls34 i) = true := by decide
theorem multi33 : ∀ i : ℕ, i < cls33.n → multi (patC cls33 i) = true := by decide
theorem multi24x : ∀ i : ℕ, i < cls24x.n → multi (patC cls24x i) = true := by decide
theorem cnt34 : ∀ p : ℕ, p < 16 → multi p = true → regf 3 4 p = cnt cls34 p := by decide
theorem cnt33 : ∀ p : ℕ, p < 16 → multi p = true → regf 3 3 p = cnt cls33 p := by decide
theorem cnt24x : ∀ p : ℕ, p < 16 → multi p = true → regf 2 4 p = cnt cls24x p := by decide

end Erdos616R21.NoK4
