import Erdos616.Basic

/-!
# Theorem W7-I (Erdős #616, r = 21): the triangle case is impossible

Hand proof: docs/proof-notes.md §6.1 (Tri-0, Tri-2), §7.1 (W7-2), §7.3 (W7-5 = CP'),
§7.4 (Steps 0–4); refereed SOUND in docs/referee/t21-referee.md §6.

`E616Full` is Erdos616/Basic.lean compiled as a module (unchanged copy); it provides `Counter`,
`L4`, `inter_ge5`, `R2`, `R3`, `single_card`, `S_b`, `S_c`, `cross_class`, `CP`.

No SAT certificate is used: the finite step of §7.3 is replaced by the hand Steps 0–4 of §7.4.

Notation (upper.md → Lean): apex `Q`; base `P_a, P_b, P_k` → `A, B, K`;
`x_ab, x_ak, x_bk` → `xab, xak, xbk`; `C0 = A ∩ B ∩ K`; `Q_a = Qs Q A B K`; `O_a = Os Q A B K`;
`U_k = U H Q A B K` (defined as the union of the traces on `Q_a ∪ Q_b` of ALL `(A,B)`-singles of a type
in `C0`, so no choice of one `Y` per type is needed); `W^a_q` is any edge `W` with `W ∩ (Q ∩ A) = {q}`.
-/

namespace Erdos616R21
open Finset
variable {V : Type*} [DecidableEq V]

theorem eq_of_mem_singleton' {s : Finset V} {x z : V} (h : s = {x}) (hz : z ∈ s) : z = x := by
  rw [h] at hz; exact mem_singleton.1 hz

theorem mem_of_eq_singleton' {s : Finset V} {x : V} (h : s = {x}) : x ∈ s := by
  rw [h]; exact mem_singleton_self x

/-- The triangle configuration of Tri-0: apex `Q`, base `A, B, K`, all six pairs meet in exactly 5,
`Q ∩ A ∩ B = {xab}` etc., `C0 = A ∩ B ∩ K` has 4 points and misses `Q`. -/
structure Tri (H : Finset (Finset V)) (Q A B K : Finset V) (xab xak xbk : V) : Prop where
  hQ : Q ∈ H
  hA : A ∈ H
  hB : B ∈ H
  hK : K ∈ H
  QA : (Q ∩ A).card = 5
  QB : (Q ∩ B).card = 5
  QK : (Q ∩ K).card = 5
  AB : (A ∩ B).card = 5
  AK : (A ∩ K).card = 5
  BK : (B ∩ K).card = 5
  tAB : Q ∩ A ∩ B = {xab}
  tAK : Q ∩ A ∩ K = {xak}
  tBK : Q ∩ B ∩ K = {xbk}
  C4 : (A ∩ B ∩ K).card = 4
  QC : Disjoint Q (A ∩ B ∩ K)

/-- `Q_a`: the private part of the trace `Q ∩ A`. -/
def Qs (Q A B K : Finset V) : Finset V := (Q ∩ A) \ (B ∪ K)

/-- `O_a`: the private part of `A` outside `Q ∪ B ∪ K`. -/
def Os (Q A B K : Finset V) : Finset V := A \ (Q ∪ B ∪ K)

theorem mem_Qs {Q A B K : Finset V} {z : V} :
    z ∈ Qs Q A B K ↔ z ∈ Q ∧ z ∈ A ∧ z ∉ B ∧ z ∉ K := by
  unfold Qs; simp only [mem_sdiff, mem_inter, mem_union, not_or]; tauto

theorem mem_Os {Q A B K : Finset V} {z : V} :
    z ∈ Os Q A B K ↔ z ∈ A ∧ z ∉ Q ∧ z ∉ B ∧ z ∉ K := by
  unfold Os; simp only [mem_sdiff, mem_union, not_or]; tauto

theorem Qs_swap (Q A B K : Finset V) : Qs Q A B K = Qs Q A K B := by
  ext z; simp only [mem_Qs]; tauto

theorem Qs_sub_Q {Q A B K : Finset V} : Qs Q A B K ⊆ Q := fun z hz => (mem_Qs.1 hz).1

/-- `U_k` (for the base pair `(A, B)` with third edge `K`): the points of `Q_a ∪ Q_b` lying in some
edge `Y` with `Y ∩ (A ∩ B) = {c}`, `c ∈ C0`. -/
noncomputable def U (H : Finset (Finset V)) (Q A B K : Finset V) : Finset V := by
  classical
  exact (Qs Q A B K ∪ Qs Q B A K).filter
    (fun z => ∃ Y ∈ H, (∃ c ∈ A ∩ B ∩ K, Y ∩ (A ∩ B) = {c}) ∧ z ∈ Y)

theorem mem_U {H : Finset (Finset V)} {Q A B K : Finset V} {z : V} :
    z ∈ U H Q A B K ↔ z ∈ Qs Q A B K ∪ Qs Q B A K ∧
      ∃ Y ∈ H, (∃ c ∈ A ∩ B ∩ K, Y ∩ (A ∩ B) = {c}) ∧ z ∈ Y := by
  unfold U; simp only [mem_filter]

theorem U_symm (H : Finset (Finset V)) (Q A B K : Finset V) : U H Q A B K = U H Q B A K := by
  ext z
  rw [mem_U, mem_U, union_comm (Qs Q A B K) (Qs Q B A K), inter_comm A B]

theorem U_sub {H : Finset (Finset V)} {Q A B K : Finset V} :
    U H Q A B K ⊆ Qs Q A B K ∪ Qs Q B A K := fun z hz => (mem_U.1 hz).1

theorem trace_sub_U {H : Finset (Finset V)} {Q A B K Y : Finset V} {c : V} (hY : Y ∈ H)
    (hc : c ∈ A ∩ B ∩ K) (hYc : Y ∩ (A ∩ B) = {c}) :
    Y ∩ (Qs Q A B K ∪ Qs Q B A K) ⊆ U H Q A B K := by
  intro z hz
  rw [mem_inter] at hz
  exact mem_U.2 ⟨hz.2, Y, hY, ⟨c, hc, hYc⟩, hz.1⟩

namespace Tri
variable {H : Finset (Finset V)} {Q A B K : Finset V} {xab xak xbk : V}

theorem swapAB (T : Tri H Q A B K xab xak xbk) : Tri H Q B A K xab xbk xak where
  hQ := T.hQ
  hA := T.hB
  hB := T.hA
  hK := T.hK
  QA := T.QB
  QB := T.QA
  QK := T.QK
  AB := by rw [inter_comm]; exact T.AB
  AK := T.BK
  BK := T.AK
  tAB := by rw [inter_right_comm]; exact T.tAB
  tAK := T.tBK
  tBK := T.tAK
  C4 := by rw [inter_comm B A]; exact T.C4
  QC := by rw [inter_comm B A]; exact T.QC

theorem swapBK (T : Tri H Q A B K xab xak xbk) : Tri H Q A K B xak xab xbk where
  hQ := T.hQ
  hA := T.hA
  hB := T.hK
  hK := T.hB
  QA := T.QA
  QB := T.QK
  QK := T.QB
  AB := T.AK
  AK := T.AB
  BK := by rw [inter_comm]; exact T.BK
  tAB := T.tAK
  tAK := T.tAB
  tBK := by rw [inter_right_comm]; exact T.tBK
  C4 := by rw [inter_right_comm]; exact T.C4
  QC := by rw [inter_right_comm]; exact T.QC

theorem memAB (T : Tri H Q A B K xab xak xbk) {z : V} (hQ : z ∈ Q) (hA : z ∈ A) (hB : z ∈ B) :
    z = xab := eq_of_mem_singleton' T.tAB (mem_inter.2 ⟨mem_inter.2 ⟨hQ, hA⟩, hB⟩)

theorem memAK (T : Tri H Q A B K xab xak xbk) {z : V} (hQ : z ∈ Q) (hA : z ∈ A) (hK : z ∈ K) :
    z = xak := eq_of_mem_singleton' T.tAK (mem_inter.2 ⟨mem_inter.2 ⟨hQ, hA⟩, hK⟩)

theorem memBK (T : Tri H Q A B K xab xak xbk) {z : V} (hQ : z ∈ Q) (hB : z ∈ B) (hK : z ∈ K) :
    z = xbk := eq_of_mem_singleton' T.tBK (mem_inter.2 ⟨mem_inter.2 ⟨hQ, hB⟩, hK⟩)

theorem noC (T : Tri H Q A B K xab xak xbk) {z : V} (hQ : z ∈ Q) (hA : z ∈ A) (hB : z ∈ B)
    (hK : z ∈ K) : False :=
  Finset.disjoint_left.1 T.QC hQ (mem_inter.2 ⟨mem_inter.2 ⟨hA, hB⟩, hK⟩)

theorem C_notQ (T : Tri H Q A B K xab xak xbk) {c : V} (hc : c ∈ A ∩ B ∩ K) : c ∉ Q :=
  fun hQ => Finset.disjoint_left.1 T.QC hQ hc

theorem xab_mem (T : Tri H Q A B K xab xak xbk) : xab ∈ Q ∧ xab ∈ A ∧ xab ∈ B := by
  have h := mem_of_eq_singleton' T.tAB
  simp only [mem_inter] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem xak_mem (T : Tri H Q A B K xab xak xbk) : xak ∈ Q ∧ xak ∈ A ∧ xak ∈ K :=
  T.swapBK.xab_mem

theorem xbk_mem (T : Tri H Q A B K xab xak xbk) : xbk ∈ Q ∧ xbk ∈ B ∧ xbk ∈ K :=
  T.swapAB.swapBK.xab_mem

theorem xab_notK (T : Tri H Q A B K xab xak xbk) : xab ∉ K :=
  fun h => T.noC T.xab_mem.1 T.xab_mem.2.1 T.xab_mem.2.2 h

theorem xak_notB (T : Tri H Q A B K xab xak xbk) : xak ∉ B := T.swapBK.xab_notK

theorem xbk_notA (T : Tri H Q A B K xab xak xbk) : xbk ∉ A := T.swapAB.swapBK.xab_notK

theorem L_AB (T : Tri H Q A B K xab xak xbk) : A ∩ B = insert xab (A ∩ B ∩ K) := by
  have hn : xab ∉ A ∩ B ∩ K := fun h => T.C_notQ h T.xab_mem.1
  have hsub : insert xab (A ∩ B ∩ K) ⊆ A ∩ B := by
    intro z hz
    rcases mem_insert.1 hz with h | h
    · rw [h]; exact mem_inter.2 ⟨T.xab_mem.2.1, T.xab_mem.2.2⟩
    · exact (mem_inter.1 h).1
  refine (eq_of_subset_of_card_le hsub ?_).symm
  rw [card_insert_of_notMem hn, T.C4, T.AB]

theorem sub_C (T : Tri H Q A B K xab xak xbk) {z : V} (hA : z ∈ A) (hB : z ∈ B) (hQ : z ∉ Q) :
    z ∈ A ∩ B ∩ K := by
  have h : z ∈ insert xab (A ∩ B ∩ K) := by rw [← T.L_AB]; exact mem_inter.2 ⟨hA, hB⟩
  rcases mem_insert.1 h with h | h
  · exact absurd (h ▸ T.xab_mem.1) hQ
  · exact h

theorem sub_CK (T : Tri H Q A B K xab xak xbk) {z : V} (hA : z ∈ A) (hK : z ∈ K) (hQ : z ∉ Q) :
    z ∈ A ∩ B ∩ K := by
  have := T.swapBK.sub_C hA hK hQ
  simp only [mem_inter] at this ⊢
  exact ⟨⟨this.1.1, this.2⟩, this.1.2⟩

theorem decompA (T : Tri H Q A B K xab xak xbk) {z : V} (hA : z ∈ A) (hQ : z ∉ Q) :
    z ∈ A ∩ B ∩ K ∨ z ∈ Os Q A B K := by
  by_cases hB : z ∈ B
  · exact Or.inl (T.sub_C hA hB hQ)
  by_cases hK : z ∈ K
  · exact Or.inl (T.sub_CK hA hK hQ)
  exact Or.inr (mem_Os.2 ⟨hA, hQ, hB, hK⟩)

theorem xab_ne_xak (T : Tri H Q A B K xab xak xbk) : xab ≠ xak := by
  intro h; exact T.xab_notK (h ▸ T.xak_mem.2.2)

theorem Qs_card (T : Tri H Q A B K xab xak xbk) : (Qs Q A B K).card = 3 := by
  have e : (Q ∩ A) ∩ (B ∪ K) = {xab, xak} := by
    ext z
    simp only [mem_inter, mem_union, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨hQ, hA⟩, hB | hK⟩
      · exact Or.inl (T.memAB hQ hA hB)
      · exact Or.inr (T.memAK hQ hA hK)
    · rintro (h | h)
      · rw [h]; exact ⟨⟨T.xab_mem.1, T.xab_mem.2.1⟩, Or.inl T.xab_mem.2.2⟩
      · rw [h]; exact ⟨⟨T.xak_mem.1, T.xak_mem.2.1⟩, Or.inr T.xak_mem.2.2⟩
  have h := card_sdiff_add_card_inter (Q ∩ A) (B ∪ K)
  rw [e, card_pair T.xab_ne_xak, T.QA] at h
  unfold Qs; omega

end Tri

/-! ## Lemmas needing `Counter` -/

section Counter
variable {H : Finset (Finset V)} (hC : Counter H)
include hC
variable {Q A B K : Finset V} {xab xak xbk : V}

/-! ### Tri-2: the `(A,B)`-singles `Y` of a type `c ∈ C0` -/

theorem Y_C (T : Tri H Q A B K xab xak xbk) {Y : Finset V} {c : V}
    (hYc : Y ∩ (A ∩ B) = {c}) : Y ∩ (A ∩ B ∩ K) ⊆ {c} := by
  intro z hz
  simp only [mem_inter] at hz
  rw [← hYc]; exact mem_inter.2 ⟨hz.1, mem_inter.2 hz.2.1⟩

theorem Y_xab (T : Tri H Q A B K xab xak xbk) {Y : Finset V} {c : V} (hc : c ∈ A ∩ B ∩ K)
    (hYc : Y ∩ (A ∩ B) = {c}) : xab ∉ Y := by
  intro h
  have : xab = c := eq_of_mem_singleton' hYc
    (mem_inter.2 ⟨h, mem_inter.2 ⟨T.xab_mem.2.1, T.xab_mem.2.2⟩⟩)
  exact T.C_notQ hc (this ▸ T.xab_mem.1)

/-- Tri-2 (first part): `Y ∩ Q ⊆ A ∪ B` (R.3 against the type-`xab` single `Q`). -/
theorem Y_sub (T : Tri H Q A B K xab xak xbk) {Y : Finset V} {c : V} (hY : Y ∈ H)
    (hc : c ∈ A ∩ B ∩ K) (hYc : Y ∩ (A ∩ B) = {c}) : Y ∩ Q ⊆ A ∪ B := by
  have hx : Q ∩ (A ∩ B) = {xab} := by rw [← inter_assoc]; exact T.tAB
  have hne : xab ≠ c := fun h => T.C_notQ hc (h ▸ T.xab_mem.1)
  have hdis := (R3 hC T.hA T.hB T.hQ hY T.AB hx hYc hne).2.2.2.2.1
  intro z hz
  rw [mem_inter] at hz
  by_contra hzAB
  exact Finset.disjoint_left.1 hdis (mem_sdiff.2 ⟨hz.2, hzAB⟩) (mem_sdiff.2 ⟨hz.1, hzAB⟩)

/-- Tri-2: `xak ∈ Y` (CP' at the 49-triple `(Q, A, K)`). -/
theorem Y_xak (T : Tri H Q A B K xab xak xbk) {Y : Finset V} {c : V} (hY : Y ∈ H)
    (hc : c ∈ A ∩ B ∩ K) (hYc : Y ∩ (A ∩ B) = {c}) : xak ∈ Y := by
  by_contra hx
  have hcp := CP hC T.hQ T.hA T.hK hY T.QA T.QK T.AK T.tAK hx
  have hr : Y ∩ ((A ∩ K) \ Q) ⊆ {c} := by
    intro z hz
    simp only [mem_inter, mem_sdiff] at hz
    exact Y_C hC T hYc (mem_inter.2 ⟨hz.1, T.sub_CK hz.2.1.1 hz.2.1.2 hz.2.2⟩)
  have hr' := card_le_card hr
  rw [card_singleton] at hr'
  have h0 : (Y ∩ Q) \ (A ∪ K) = ∅ := card_eq_zero.1 (by omega)
  have hsub : Y ∩ Q ⊆ insert xbk (Qs Q A B K) := by
    intro z hz
    have hzAK : z ∈ A ∪ K := by
      by_contra h
      have : z ∈ (Y ∩ Q) \ (A ∪ K) := mem_sdiff.2 ⟨hz, h⟩
      rw [h0] at this; exact Finset.notMem_empty z this
    have hzAB := Y_sub hC T hY hc hYc hz
    rw [mem_inter] at hz
    rw [mem_insert, mem_Qs]
    by_cases hA : z ∈ A
    · right
      refine ⟨hz.2, hA, fun hB => ?_, fun hK => ?_⟩
      · exact Y_xab hC T hc hYc (T.memAB hz.2 hA hB ▸ hz.1)
      · exact hx (T.memAK hz.2 hA hK ▸ hz.1)
    · left
      have hB : z ∈ B := (mem_union.1 hzAB).resolve_left hA
      have hK : z ∈ K := (mem_union.1 hzAK).resolve_left hA
      exact T.memBK hz.2 hB hK
  have h1 := card_le_card hsub
  have h2 := card_insert_le xbk (Qs Q A B K)
  have h3 := inter_ge5 hC hY T.hQ
  rw [T.Qs_card] at h2
  omega

theorem Y_xbk (T : Tri H Q A B K xab xak xbk) {Y : Finset V} {c : V} (hY : Y ∈ H)
    (hc : c ∈ A ∩ B ∩ K) (hYc : Y ∩ (A ∩ B) = {c}) : xbk ∈ Y := by
  have hc' : c ∈ B ∩ A ∩ K := by rw [inter_comm B A]; exact hc
  have hYc' : Y ∩ (B ∩ A) = {c} := by rw [inter_comm B A]; exact hYc
  exact Y_xak hC T.swapAB hY hc' hYc'

/-- Tri-2 + Lemma A: `|Y ∩ Q_a| + |Y ∩ Q_b| ≥ 3`. -/
theorem Y_three (T : Tri H Q A B K xab xak xbk) {Y : Finset V} {c : V} (hY : Y ∈ H)
    (hc : c ∈ A ∩ B ∩ K) (hYc : Y ∩ (A ∩ B) = {c}) :
    3 ≤ (Y ∩ (Qs Q A B K ∪ Qs Q B A K)).card := by
  have hsub : Y ∩ Q ⊆ insert xak (insert xbk (Y ∩ (Qs Q A B K ∪ Qs Q B A K))) := by
    intro z hz
    have hzAB := Y_sub hC T hY hc hYc hz
    rw [mem_inter] at hz
    simp only [mem_insert, mem_inter, mem_union, mem_Qs]
    by_cases hA : z ∈ A
    · by_cases hB : z ∈ B
      · exact absurd (T.memAB hz.2 hA hB ▸ hz.1) (Y_xab hC T hc hYc)
      by_cases hK : z ∈ K
      · exact Or.inl (T.memAK hz.2 hA hK)
      · exact Or.inr (Or.inr ⟨hz.1, Or.inl ⟨hz.2, hA, hB, hK⟩⟩)
    · have hB : z ∈ B := (mem_union.1 hzAB).resolve_left hA
      by_cases hK : z ∈ K
      · exact Or.inr (Or.inl (T.memBK hz.2 hB hK))
      · exact Or.inr (Or.inr ⟨hz.1, Or.inr ⟨hz.2, hB, hA, hK⟩⟩)
  have h1 := card_le_card hsub
  have h2 := card_insert_le xak (insert xbk (Y ∩ (Qs Q A B K ∪ Qs Q B A K)))
  have h3 := card_insert_le xbk (Y ∩ (Qs Q A B K ∪ Qs Q B A K))
  have h4 := inter_ge5 hC hY T.hQ
  omega

theorem Y_notQK (T : Tri H Q A B K xab xak xbk) {Y : Finset V} {c : V} (hY : Y ∈ H)
    (hc : c ∈ A ∩ B ∩ K) (hYc : Y ∩ (A ∩ B) = {c}) {q : V} (hq : q ∈ Qs Q K A B) : q ∉ Y := by
  intro hqY
  rw [mem_Qs] at hq
  have := Y_sub hC T hY hc hYc (mem_inter.2 ⟨hqY, hq.1⟩)
  rcases mem_union.1 this with h | h
  · exact hq.2.2.1 h
  · exact hq.2.2.2 h

/-! ### W7-2: the `(Q,A)`-singles `W` of a type `q ∈ Q_a` -/

theorem W_card (T : Tri H Q A B K xab xak xbk) {W : Finset V} {q : V} (hW : W ∈ H)
    (hWq : W ∩ (Q ∩ A) = {q}) : (Q ∩ W).card = 5 ∧ (A ∩ W).card = 5 := by
  obtain ⟨h1, h2, -⟩ := single_card hC T.hQ T.hA hW T.QA hWq
  rw [inter_comm Q W, inter_comm A W]
  exact ⟨h1, h2⟩

theorem W_QAW {W : Finset V} {q : V} (hWq : W ∩ (Q ∩ A) = {q}) : Q ∩ A ∩ W = {q} := by
  rw [inter_comm]; exact hWq

/-- W7-2: `|W ∩ C0| ≥ 3` (Lemma S(b) against `B` and `K`). -/
theorem W_e3 (T : Tri H Q A B K xab xak xbk) {W : Finset V} {q : V} (hq : q ∈ Qs Q A B K)
    (hW : W ∈ H) (hWq : W ∩ (Q ∩ A) = {q}) : 3 ≤ (W ∩ (A ∩ B ∩ K)).card := by
  rw [mem_Qs] at hq
  have hqb : q ≠ xab := fun h => hq.2.2.1 (h ▸ T.xab_mem.2.2)
  have hqk : q ≠ xak := fun h => hq.2.2.2 (h ▸ T.xak_mem.2.2)
  have hB : B ∩ (Q ∩ A) = {xab} := by rw [inter_comm]; exact T.tAB
  have hK : K ∩ (Q ∩ A) = {xak} := by rw [inter_comm]; exact T.tAK
  have sB := S_b hC T.hQ T.hA hW T.hB T.QA hWq hB hqb
  have sK := S_b hC T.hQ T.hA hW T.hK T.QA hWq hK hqk
  have h1 : W ∩ B ∩ (A \ Q) ⊆ W ∩ (A ∩ B ∩ K) := by
    intro z hz
    simp only [mem_inter, mem_sdiff] at hz
    exact mem_inter.2 ⟨hz.1.1, T.sub_C hz.2.1 hz.1.2 hz.2.2⟩
  have h2 : W ∩ K ∩ (A \ Q) ⊆ W ∩ (A ∩ B ∩ K) := by
    intro z hz
    simp only [mem_inter, mem_sdiff] at hz
    exact mem_inter.2 ⟨hz.1.1, T.sub_CK hz.2.1 hz.1.2 hz.2.2⟩
  have h3 : (W ∩ B ∩ (Q \ A)) ∪ (W ∩ K ∩ (Q \ A)) ⊆ (W ∩ Q) \ A := by
    intro z hz
    simp only [mem_union, mem_inter, mem_sdiff] at hz ⊢
    tauto
  have h4 : (W ∩ B ∩ (Q \ A)) ∩ (W ∩ K ∩ (Q \ A)) ⊆ {xbk} := by
    intro z hz
    simp only [mem_inter, mem_sdiff] at hz
    exact mem_singleton.2 (T.memBK hz.1.2.1 hz.1.1.2 hz.2.1.2)
  have c1 := card_le_card h1
  have c2 := card_le_card h2
  have c3 := card_le_card h3
  have c4 := card_le_card h4
  rw [card_singleton] at c4
  have c5 := card_union_add_card_inter (W ∩ B ∩ (Q \ A)) (W ∩ K ∩ (Q \ A))
  have c6 := card_sdiff_add_card_inter (W ∩ Q) A
  have e : W ∩ Q ∩ A = W ∩ (Q ∩ A) := inter_assoc W Q A
  rw [e, hWq, card_singleton] at c6
  obtain ⟨hWQ, -⟩ := W_card hC T hW hWq
  rw [inter_comm] at hWQ
  omega

/-- W7-2: `|W ∩ C0| + |W ∩ O_a| = 4`. -/
theorem W_split (T : Tri H Q A B K xab xak xbk) {W : Finset V} {q : V} (hW : W ∈ H)
    (hWq : W ∩ (Q ∩ A) = {q}) :
    (W ∩ (A ∩ B ∩ K)).card + (W ∩ Os Q A B K).card = 4 := by
  have h := card_split_left W A Q
  have e1 : W ∩ (A ∩ Q) = {q} := by rw [inter_comm A Q]; exact hWq
  rw [e1, card_singleton] at h
  have e2 : W ∩ (A \ Q) = (W ∩ (A ∩ B ∩ K)) ∪ (W ∩ Os Q A B K) := by
    ext z
    simp only [mem_inter, mem_sdiff, mem_union]
    constructor
    · rintro ⟨hzW, hzA, hzQ⟩
      rcases T.decompA hzA hzQ with h | h
      · exact Or.inl ⟨hzW, by simpa only [mem_inter] using h⟩
      · exact Or.inr ⟨hzW, h⟩
    · rintro (⟨hzW, ⟨hzA, hzB⟩, hzK⟩ | ⟨hzW, hzO⟩)
      · exact ⟨hzW, hzA, fun hzQ => T.noC hzQ hzA hzB hzK⟩
      · exact ⟨hzW, (mem_Os.1 hzO).1, (mem_Os.1 hzO).2.1⟩
  have e3 : (W ∩ (A ∩ B ∩ K)) ∩ (W ∩ Os Q A B K) = ∅ := by
    ext z
    simp only [mem_inter, Finset.notMem_empty, iff_false, mem_Os]
    tauto
  have h2 := card_union_add_card_inter (W ∩ (A ∩ B ∩ K)) (W ∩ Os Q A B K)
  rw [e3, card_empty, ← e2] at h2
  obtain ⟨-, hWA⟩ := W_card hC T hW hWq
  rw [inter_comm] at hWA
  omega

theorem W_rhs (T : Tri H Q A B K xab xak xbk) {W : Finset V} :
    (A ∩ W) \ Q ⊆ (W ∩ (A ∩ B ∩ K)) ∪ (W ∩ Os Q A B K) := by
  intro z hz
  simp only [mem_sdiff, mem_inter] at hz
  rcases T.decompA hz.1.1 hz.2 with h | h
  · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hz.1.2, h⟩))
  · exact mem_union.2 (Or.inr (mem_inter.2 ⟨hz.1.2, h⟩))

/-- The point `c*(q)`: some `c ∈ C0` with `[c ∈ W] + |W ∩ O_a| ≤ 1`, in the form used by CP'. -/
theorem W_cstar (T : Tri H Q A B K xab xak xbk) {W : Finset V} {q : V} (hq : q ∈ Qs Q A B K)
    (hW : W ∈ H) (hWq : W ∩ (Q ∩ A) = {q}) :
    ∃ c ∈ A ∩ B ∩ K, ∀ Y : Finset V, Y ∩ (A ∩ B ∩ K) ⊆ {c} → (Y ∩ ((A ∩ W) \ Q)).card ≤ 1 := by
  have he := W_e3 hC T hq hW hWq
  have hs := W_split hC T hW hWq
  by_cases hsub : A ∩ B ∩ K ⊆ W
  · have e : W ∩ (A ∩ B ∩ K) = A ∩ B ∩ K := inter_eq_right.2 hsub
    rw [e, T.C4] at hs
    have hO : W ∩ Os Q A B K = ∅ := card_eq_zero.1 (by omega)
    obtain ⟨c, hc⟩ := card_pos.1 (by rw [T.C4]; omega : 0 < (A ∩ B ∩ K).card)
    refine ⟨c, hc, fun Y hY => ?_⟩
    have : Y ∩ ((A ∩ W) \ Q) ⊆ {c} := by
      intro z hz
      rw [mem_inter] at hz
      have h := W_rhs hC T hz.2
      rw [hO, union_empty] at h
      exact hY (mem_inter.2 ⟨hz.1, (mem_inter.1 h).2⟩)
    simpa using card_le_card this
  · obtain ⟨m, hm, hmW⟩ := not_subset.1 hsub
    have hlt : (W ∩ (A ∩ B ∩ K)).card ≤ 3 := by
      have : W ∩ (A ∩ B ∩ K) ⊆ (A ∩ B ∩ K).erase m := by
        intro z hz
        rw [mem_inter] at hz
        exact mem_erase.2 ⟨fun h => hmW (h ▸ hz.1), hz.2⟩
      have h2 := card_le_card this
      rw [card_erase_of_mem hm, T.C4] at h2
      exact h2
    refine ⟨m, hm, fun Y hY => ?_⟩
    have : Y ∩ ((A ∩ W) \ Q) ⊆ W ∩ Os Q A B K := by
      intro z hz
      rw [mem_inter] at hz
      rcases mem_union.1 (W_rhs hC T hz.2) with h | h
      · exfalso
        rw [mem_inter] at h
        have := hY (mem_inter.2 ⟨hz.1, h.2⟩)
        rw [mem_singleton] at this
        exact hmW (this ▸ h.1)
      · exact h
    have h3 := card_le_card this
    omega

/-- The CP' "hit": with `c = c*(q)`, any `Y ∌ q` with `Y ∩ C0 ⊆ {c}` has `Y ∩ Q ⊆ A ∪ W`. -/
theorem hit (T : Tri H Q A B K xab xak xbk) {W : Finset V} {q c : V}
    (hW : W ∈ H) (hWq : W ∩ (Q ∩ A) = {q})
    (hcP : ∀ Y : Finset V, Y ∩ (A ∩ B ∩ K) ⊆ {c} → (Y ∩ ((A ∩ W) \ Q)).card ≤ 1)
    {Y : Finset V} (hY : Y ∈ H) (hYc : Y ∩ (A ∩ B ∩ K) ⊆ {c}) (hqY : q ∉ Y) :
    Y ∩ Q ⊆ A ∪ W := by
  obtain ⟨h1, h2⟩ := W_card hC T hW hWq
  have hcp := CP hC T.hQ T.hA hW hY T.QA h1 h2 (W_QAW hC hWq) hqY
  have := hcP Y hYc
  have h0 : (Y ∩ Q) \ (A ∪ W) = ∅ := card_eq_zero.1 (by omega)
  intro z hz
  by_contra h
  have : z ∈ (Y ∩ Q) \ (A ∪ W) := mem_sdiff.2 ⟨hz, h⟩
  rw [h0] at this; exact Finset.notMem_empty z this

/-! ### Step 0 (= hand step (I), uses Lemma S(a)/R.3 disjointness, "(A)") -/

theorem U_sub_W (T : Tri H Q A B K xab xak xbk) {W : Finset V} {q : V} (hq : q ∈ Qs Q K A B)
    (hW : W ∈ H) (hWq : W ∩ (Q ∩ K) = {q}) : U H Q A B K ⊆ W := by
  intro z hz
  obtain ⟨hzQs, Y, hY, ⟨c, hc, hYc⟩, hzY⟩ := mem_U.1 hz
  by_contra hzW
  have T' := T.swapBK.swapAB   -- Tri H Q K A B xak xbk xab
  have hqY := Y_notQK hC T hY hc hYc hq
  obtain ⟨h1, h2⟩ := W_card hC T' hW hWq
  have hcp := CP hC T.hQ T.hK hW hY T.QK h1 h2 (W_QAW hC hWq) hqY
  have hzQ : z ∈ Q ∧ z ∉ K := by
    rcases mem_union.1 hzQs with h | h
    · exact ⟨(mem_Qs.1 h).1, (mem_Qs.1 h).2.2.2⟩
    · exact ⟨(mem_Qs.1 h).1, (mem_Qs.1 h).2.2.2⟩
  have hz1 : z ∈ (Y ∩ Q) \ (K ∪ W) :=
    mem_sdiff.2 ⟨mem_inter.2 ⟨hzY, hzQ.1⟩, fun h => (mem_union.1 h).elim hzQ.2 hzW⟩
  have hpos : 1 ≤ ((Y ∩ Q) \ (K ∪ W)).card := card_pos.2 ⟨z, hz1⟩
  have hsp := W_split hC T' hW hWq
  have he3 := W_e3 hC T' hq hW hWq
  -- C0 in the `K A B` order
  have eC : K ∩ A ∩ B = A ∩ B ∩ K := by ext; simp only [mem_inter]; tauto
  rw [eC] at hsp he3
  have hrhs : ∀ Y' : Finset V, Y' ∩ ((K ∩ W) \ Q) ⊆ (Y' ∩ (W ∩ (A ∩ B ∩ K))) ∪ (Y' ∩ (W ∩ Os Q K A B)) := by
    intro Y' x hx
    rw [mem_inter] at hx
    have := W_rhs hC T' hx.2
    rw [eC] at this
    rcases mem_union.1 this with h | h
    · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hx.1, h⟩))
    · exact mem_union.2 (Or.inr (mem_inter.2 ⟨hx.1, h⟩))
  have hYC1 : Y ∩ (W ∩ (A ∩ B ∩ K)) ⊆ {c} := by
    intro x hx
    simp only [mem_inter] at hx
    exact Y_C hC T hYc (mem_inter.2 ⟨hx.1, mem_inter.2 ⟨mem_inter.2 hx.2.2.1, hx.2.2.2⟩⟩)
  have c1 := card_le_card (hrhs Y)
  have c2 := card_union_le (Y ∩ (W ∩ (A ∩ B ∩ K))) (Y ∩ (W ∩ Os Q K A B))
  have c3 := card_le_card hYC1
  rw [card_singleton] at c3
  have c4 : (Y ∩ (W ∩ Os Q K A B)).card ≤ (W ∩ Os Q K A B).card := card_le_card inter_subset_right
  -- so |O| = 1, |W ∩ C0| = 3, and `c ∈ W`, `Y ∩ O ≠ ∅`
  have hO1 : (W ∩ Os Q K A B).card = 1 := by omega
  have hYO : (Y ∩ (W ∩ Os Q K A B)).Nonempty := card_pos.1 (by omega)
  obtain ⟨o, ho⟩ := hYO
  have hcW : c ∈ W := by
    obtain ⟨x, hx⟩ := card_pos.1 (by omega : 0 < (Y ∩ (W ∩ (A ∩ B ∩ K))).card)
    have := hYC1 hx
    rw [mem_singleton] at this
    rw [← this]; simp only [mem_inter] at hx; exact hx.2.1
  have hnsub : ¬ (A ∩ B ∩ K ⊆ W) := by
    intro hs
    have : W ∩ (A ∩ B ∩ K) = A ∩ B ∩ K := inter_eq_right.2 hs
    rw [this, T.C4] at hsp; omega
  obtain ⟨m, hm, hmW⟩ := not_subset.1 hnsub
  have hmAB : m ∈ A ∩ B := by simp only [mem_inter] at hm ⊢; exact hm.1
  obtain ⟨Y', hY', hY'm⟩ := R2 hC T.hA T.hB T.AB hmAB
  have hqY' := Y_notQK hC T hY' hm hY'm hq
  have hcp' := CP hC T.hQ T.hK hW hY' T.QK h1 h2 (W_QAW hC hWq) hqY'
  obtain ⟨z', hz'⟩ := card_pos.1 (by omega : 0 < (Y' ∩ ((K ∩ W) \ Q)).card)
  have hz'O : z' ∈ Y' ∩ (W ∩ Os Q K A B) := by
    rcases mem_union.1 (hrhs Y' hz') with h | h
    · exfalso
      simp only [mem_inter] at h
      have := Y_C hC T hY'm (mem_inter.2 ⟨h.1, mem_inter.2 ⟨mem_inter.2 h.2.2.1, h.2.2.2⟩⟩)
      rw [mem_singleton] at this
      exact hmW (this ▸ h.2.1)
    · exact h
  have hoeq : z' = o := card_le_one.1 (le_of_eq hO1) z' (mem_inter.1 hz'O).2 o (mem_inter.1 ho).2
  have hcm : c ≠ m := fun h => hmW (h ▸ hcW)
  have hdis := (R3 hC T.hA T.hB hY hY' T.AB hYc hY'm hcm).2.2.2.2.1
  have hoOs := mem_Os.1 (mem_inter.1 (mem_inter.1 ho).2).2
  have hoAB : o ∉ A ∪ B := fun h => (mem_union.1 h).elim hoOs.2.2.1 hoOs.2.2.2
  have hoY' : o ∈ Y' := hoeq ▸ (mem_inter.1 hz'O).1
  exact Finset.disjoint_left.1 hdis (mem_sdiff.2 ⟨(mem_inter.1 ho).1, hoAB⟩)
    (mem_sdiff.2 ⟨hoY', hoAB⟩)

theorem U_le4 (T : Tri H Q A B K xab xak xbk) : (U H Q A B K).card ≤ 4 := by
  have T' := T.swapBK.swapAB
  obtain ⟨q, hq⟩ := card_pos.1 (by rw [T'.Qs_card]; omega : 0 < (Qs Q K A B).card)
  have hq' := mem_Qs.1 hq
  obtain ⟨W, hW, hWq⟩ := R2 hC T.hQ T.hK T.QK (mem_inter.2 ⟨hq'.1, hq'.2.1⟩)
  have hsub := U_sub_W hC T hq hW hWq
  have : U H Q A B K ⊆ (W ∩ Q).erase q := by
    intro z hz
    have hzQs := U_sub hz
    have hzQ : z ∈ Q ∧ (z ∈ A ∨ z ∈ B) := by
      rcases mem_union.1 hzQs with h | h
      · exact ⟨(mem_Qs.1 h).1, Or.inl (mem_Qs.1 h).2.1⟩
      · exact ⟨(mem_Qs.1 h).1, Or.inr (mem_Qs.1 h).2.1⟩
    refine mem_erase.2 ⟨fun h => ?_, mem_inter.2 ⟨hsub hz, hzQ.1⟩⟩
    rw [h] at hzQ
    exact hzQ.2.elim hq'.2.2.1 hq'.2.2.2
  have h1 := card_le_card this
  obtain ⟨h2, -⟩ := W_card hC T' hW hWq
  rw [inter_comm] at h2
  have hqWQ : q ∈ W ∩ Q := mem_inter.2 ⟨(mem_inter.1 (mem_of_eq_singleton' hWq)).1, hq'.1⟩
  rw [card_erase_of_mem hqWQ, h2] at h1
  exact h1

theorem U_ge3 (T : Tri H Q A B K xab xak xbk) : 3 ≤ (U H Q A B K).card := by
  obtain ⟨c, hc⟩ := card_pos.1 (by rw [T.C4]; omega : 0 < (A ∩ B ∩ K).card)
  have hcAB : c ∈ A ∩ B := by simp only [mem_inter] at hc ⊢; exact hc.1
  obtain ⟨Y, hY, hYc⟩ := R2 hC T.hA T.hB T.AB hcAB
  have h1 := Y_three hC T hY hc hYc
  have h2 := card_le_card (trace_sub_U (Q := Q) hY hc hYc)
  omega

theorem tight_trace (T : Tri H Q A B K xab xak xbk) (h3 : (U H Q A B K).card = 3)
    {Y : Finset V} {c : V} (hY : Y ∈ H) (hc : c ∈ A ∩ B ∩ K) (hYc : Y ∩ (A ∩ B) = {c}) :
    Y ∩ (Qs Q A B K ∪ Qs Q B A K) = U H Q A B K :=
  eq_of_subset_of_card_le (trace_sub_U hY hc hYc) (by have := Y_three hC T hY hc hYc; omega)

/-! ### Step 1 (hard hit) -/

theorem step1 (T : Tri H Q A B K xab xak xbk) {W : Finset V} {q c : V} (hq : q ∈ Qs Q A B K)
    (hW : W ∈ H) (hWq : W ∩ (Q ∩ A) = {q})
    (hcP : ∀ Y : Finset V, Y ∩ (A ∩ B ∩ K) ⊆ {c} → (Y ∩ ((A ∩ W) \ Q)).card ≤ 1)
    {Y : Finset V} (hY : Y ∈ H) (hc : c ∈ A ∩ B ∩ K) (hYc : Y ∩ (A ∩ B) = {c}) (hqY : q ∉ Y) :
    (U H Q B K A).card = 3 ∧ Y ∩ Qs Q B A K ⊆ U H Q B K A := by
  have Tr := T.swapAB.swapBK   -- Tri H Q B K A xbk xab xak
  have hh := hit hC T hW hWq hcP hY (Y_C hC T hYc) hqY
  have hxY := Y_xbk hC T hY hc hYc
  have hxW : xbk ∈ W := by
    rcases mem_union.1 (hh (mem_inter.2 ⟨hxY, T.xbk_mem.1⟩)) with h | h
    · exact absurd h T.xbk_notA
    · exact h
  have hYW : Y ∩ Qs Q B A K ⊆ W := by
    intro z hz
    rw [mem_inter, mem_Qs] at hz
    rcases mem_union.1 (hh (mem_inter.2 ⟨hz.1, hz.2.1⟩)) with h | h
    · exact absurd h hz.2.2.2.1
    · exact h
  have hUW := U_sub_W hC Tr hq hW hWq
  have hSsub : insert q (insert xbk (U H Q B K A ∪ (Y ∩ Qs Q B A K))) ⊆ W ∩ Q := by
    intro z hz
    rcases mem_insert.1 hz with h | h
    · rw [h]; exact mem_inter.2 ⟨(mem_inter.1 (mem_of_eq_singleton' hWq)).1, (mem_Qs.1 hq).1⟩
    rcases mem_insert.1 h with h | h
    · rw [h]; exact mem_inter.2 ⟨hxW, T.xbk_mem.1⟩
    rcases mem_union.1 h with h | h
    · refine mem_inter.2 ⟨hUW h, ?_⟩
      rcases mem_union.1 (U_sub h) with h' | h'
      · exact (mem_Qs.1 h').1
      · exact (mem_Qs.1 h').1
    · exact mem_inter.2 ⟨hYW h, (mem_Qs.1 (mem_inter.1 h).2).1⟩
  -- every point of `S` lies in `B` or `K` but not both
  have hSBK : ∀ z ∈ U H Q B K A ∪ (Y ∩ Qs Q B A K), (z ∈ B ∨ z ∈ K) ∧ ¬ (z ∈ B ∧ z ∈ K) := by
    intro z hz
    rcases mem_union.1 hz with h | h
    · rcases mem_union.1 (U_sub h) with h' | h'
      · have := mem_Qs.1 h'; exact ⟨Or.inl this.2.1, fun h'' => this.2.2.1 h''.2⟩
      · have := mem_Qs.1 h'; exact ⟨Or.inr this.2.1, fun h'' => this.2.2.1 h''.1⟩
    · have := mem_Qs.1 (mem_inter.1 h).2
      exact ⟨Or.inl this.2.1, fun h'' => this.2.2.2 h''.2⟩
  have hqS : q ∉ insert xbk (U H Q B K A ∪ (Y ∩ Qs Q B A K)) := by
    rw [mem_insert]
    rintro (h | h)
    · exact T.xbk_notA (h ▸ (mem_Qs.1 hq).2.1)
    · have := mem_Qs.1 hq
      exact ((hSBK q h).1).elim this.2.2.1 this.2.2.2
  have hxS : xbk ∉ U H Q B K A ∪ (Y ∩ Qs Q B A K) := fun h => (hSBK xbk h).2 ⟨T.xbk_mem.2.1, T.xbk_mem.2.2⟩
  have c1 := card_le_card hSsub
  rw [card_insert_of_notMem hqS, card_insert_of_notMem hxS] at c1
  obtain ⟨hWQ, -⟩ := W_card hC T hW hWq
  rw [inter_comm] at hWQ
  rw [hWQ] at c1
  have c2 := U_ge3 hC Tr
  have c3 : (U H Q B K A).card ≤ (U H Q B K A ∪ (Y ∩ Qs Q B A K)).card := card_le_card subset_union_left
  have heq : U H Q B K A = U H Q B K A ∪ (Y ∩ Qs Q B A K) := eq_of_subset_of_card_le subset_union_left (by omega)
  refine ⟨by omega, ?_⟩
  intro z hz
  rw [heq]; exact subset_union_right hz

/-! ### Step 2 (non-tight index) -/

theorem step2 (T : Tri H Q A B K xab xak xbk) (hU4 : (U H Q A B K).card = 4) {W : Finset V}
    {q c : V} (hq : q ∈ Qs Q K B A) (hW : W ∈ H) (hWq : W ∩ (Q ∩ K) = {q})
    (hcP : ∀ Y : Finset V, Y ∩ (K ∩ B ∩ A) ⊆ {c} → (Y ∩ ((K ∩ W) \ Q)).card ≤ 1)
    {Y : Finset V} (hY : Y ∈ H) (hc : c ∈ K ∩ B ∩ A) (hYc : Y ∩ (K ∩ B) = {c}) : q ∈ Y := by
  by_contra hqY
  have T2 := T.swapBK.swapAB.swapBK   -- Tri H Q K B A xbk xak xab
  have hh := hit hC T2 hW hWq hcP hY (Y_C hC T2 hYc) hqY
  have hxY : xab ∈ Y := Y_xbk hC T2 hY hc hYc
  have hxW : xab ∈ W := by
    rcases mem_union.1 (hh (mem_inter.2 ⟨hxY, T.xab_mem.1⟩)) with h | h
    · exact absurd h T.xab_notK
    · exact h
  have hq' : q ∈ Qs Q K A B := by rw [Qs_swap]; exact hq
  have hUW := U_sub_W hC T hq' hW hWq
  have hqm := mem_Qs.1 hq
  have hUAB : ∀ z ∈ U H Q A B K, z ∈ Q ∧ (z ∈ A ∨ z ∈ B) ∧ ¬ (z ∈ A ∧ z ∈ B) := by
    intro z hz
    rcases mem_union.1 (U_sub hz) with h | h
    · have := mem_Qs.1 h; exact ⟨this.1, Or.inl this.2.1, fun h' => this.2.2.1 h'.2⟩
    · have := mem_Qs.1 h; exact ⟨this.1, Or.inr this.2.1, fun h' => this.2.2.1 h'.1⟩
  have hqU : q ∉ U H Q A B K := fun h => (hUAB q h).2.1.elim hqm.2.2.2 hqm.2.2.1
  have hxU : xab ∉ insert q (U H Q A B K) := by
    rw [mem_insert]
    rintro (h | h)
    · exact hqm.2.2.2 (h ▸ T.xab_mem.2.1)
    · exact (hUAB xab h).2.2 ⟨T.xab_mem.2.1, T.xab_mem.2.2⟩
  have hsub : insert xab (insert q (U H Q A B K)) ⊆ W ∩ Q := by
    intro z hz
    rcases mem_insert.1 hz with h | h
    · rw [h]; exact mem_inter.2 ⟨hxW, T.xab_mem.1⟩
    rcases mem_insert.1 h with h | h
    · rw [h]; exact mem_inter.2 ⟨(mem_inter.1 (mem_of_eq_singleton' hWq)).1, hqm.1⟩
    · exact mem_inter.2 ⟨hUW h, (hUAB z h).1⟩
  have c1 := card_le_card hsub
  rw [card_insert_of_notMem hxU, card_insert_of_notMem hqU, hU4] at c1
  obtain ⟨hWQ, -⟩ := W_card hC T2 hW hWq
  rw [inter_comm] at hWQ
  omega

/-! ### Step 3 (no index is non-tight) -/

theorem step3_core (T : Tri H Q A B K xab xak xbk) (hU4 : (U H Q A B K).card = 4)
    (hle : (U H Q A B K ∩ Qs Q A B K).card ≤ 2) : False := by
  have Tr := T.swapAB.swapBK          -- Tri H Q B K A xbk xab xak
  have T2 := T.swapBK.swapAB.swapBK   -- Tri H Q K B A xbk xak xab
  -- (i) a point q ∈ Q_a ∖ U_k
  obtain ⟨q, hq, hqU⟩ : ∃ q ∈ Qs Q A B K, q ∉ U H Q A B K := by
    by_contra hno
    push Not at hno
    have : Qs Q A B K ⊆ U H Q A B K ∩ Qs Q A B K := fun z hz => mem_inter.2 ⟨hno z hz, hz⟩
    have := card_le_card this
    rw [T.Qs_card] at this; omega
  have hqm := mem_Qs.1 hq
  obtain ⟨W, hW, hWq⟩ := R2 hC T.hQ T.hA T.QA (mem_inter.2 ⟨hqm.1, hqm.2.1⟩)
  obtain ⟨c, hc, hcP⟩ := W_cstar hC T hq hW hWq
  have hcAB : c ∈ A ∩ B := by simp only [mem_inter] at hc ⊢; exact hc.1
  obtain ⟨Y, hY, hYc⟩ := R2 hC T.hA T.hB T.AB hcAB
  have hqY : q ∉ Y := fun h =>
    hqU (trace_sub_U hY hc hYc (mem_inter.2 ⟨h, mem_union.2 (Or.inl hq)⟩))
  obtain ⟨hUa3, hYsub⟩ := step1 hC T hq hW hWq hcP hY hc hYc hqY
  -- (ii) Q_k ⊆ U_a, hence U_a = Q_k
  have hQk : Qs Q K B A ⊆ U H Q B K A := by
    intro q' hq'
    have hq'm := mem_Qs.1 hq'
    obtain ⟨W', hW', hW'q⟩ := R2 hC T.hQ T.hK T.QK (mem_inter.2 ⟨hq'm.1, hq'm.2.1⟩)
    obtain ⟨c', hc', hcP'⟩ := W_cstar hC T2 hq' hW' hW'q
    have hc'KB : c' ∈ K ∩ B := by simp only [mem_inter] at hc' ⊢; exact hc'.1
    obtain ⟨Y', hY', hY'c⟩ := R2 hC T.hK T.hB T2.AB hc'KB
    have hq'Y' := step2 hC T hU4 hq' hW' hW'q hcP' hY' hc' hY'c
    have hc'' : c' ∈ B ∩ K ∩ A := by simp only [mem_inter] at hc' ⊢; tauto
    have hY'c' : Y' ∩ (B ∩ K) = {c'} := by rw [inter_comm B K]; exact hY'c
    exact trace_sub_U hY' hc'' hY'c' (mem_inter.2 ⟨hq'Y', mem_union.2 (Or.inr hq')⟩)
  have hUa : U H Q B K A = Qs Q K B A :=
    (eq_of_subset_of_card_le hQk (le_of_eq (by rw [hUa3, T2.Qs_card]))).symm
  -- (iii) contradiction
  have hYb : ∀ z, z ∈ Y → z ∉ Qs Q B A K := by
    intro z hzY hzb
    have := hYsub (mem_inter.2 ⟨hzY, hzb⟩)
    rw [hUa] at this
    exact (mem_Qs.1 hzb).2.2.2 (mem_Qs.1 this).2.1
  have hsub : Y ∩ (Qs Q A B K ∪ Qs Q B A K) ⊆ U H Q A B K ∩ Qs Q A B K := by
    intro z hz
    refine mem_inter.2 ⟨trace_sub_U hY hc hYc hz, ?_⟩
    rw [mem_inter] at hz
    rcases mem_union.1 hz.2 with h | h
    · exact h
    · exact absurd h (hYb z hz.1)
  have h1 := card_le_card hsub
  have h2 := Y_three hC T hY hc hYc
  omega

theorem U_split (T : Tri H Q A B K xab xak xbk) :
    (U H Q A B K ∩ Qs Q A B K).card + (U H Q A B K ∩ Qs Q B A K).card = (U H Q A B K).card := by
  have e : U H Q A B K = (U H Q A B K ∩ Qs Q A B K) ∪ (U H Q A B K ∩ Qs Q B A K) := by
    rw [← inter_union_distrib_left]
    exact (inter_eq_left.2 U_sub).symm
  have e2 : (U H Q A B K ∩ Qs Q A B K) ∩ (U H Q A B K ∩ Qs Q B A K) = ∅ := by
    ext z
    simp only [mem_inter, mem_Qs, Finset.notMem_empty, iff_false]
    tauto
  have h := card_union_add_card_inter (U H Q A B K ∩ Qs Q A B K) (U H Q A B K ∩ Qs Q B A K)
  rw [e2, card_empty, ← e] at h
  omega

theorem step3 (T : Tri H Q A B K xab xak xbk) : (U H Q A B K).card = 3 := by
  have h3 := U_ge3 hC T
  have h4 := U_le4 hC T
  by_contra hne
  have hU4 : (U H Q A B K).card = 4 := by omega
  have hs := U_split hC T
  by_cases hle : (U H Q A B K ∩ Qs Q A B K).card ≤ 2
  · exact step3_core hC T hU4 hle
  · have hU4' : (U H Q B A K).card = 4 := by rw [← U_symm]; exact hU4
    have hle' : (U H Q B A K ∩ Qs Q B A K).card ≤ 2 := by rw [← U_symm]; omega
    exact step3_core hC T.swapAB hU4' hle'

/-! ### Step 4 (not all indices tight) -/

/-- (★): `u_{ka} ≤ 2 ⇒ U_k ∩ Q_b ⊆ U_a ∩ Q_b`, stated as a disjunction of card facts. -/
theorem star (T : Tri H Q A B K xab xak xbk) :
    2 < (U H Q A B K ∩ Qs Q A B K).card ∨
      (U H Q A B K ∩ Qs Q B A K).card ≤ (U H Q B K A ∩ Qs Q B A K).card := by
  rcases Nat.lt_or_ge 2 (U H Q A B K ∩ Qs Q A B K).card with hgt | hle
  · exact Or.inl hgt
  right
  have h3 := step3 hC T
  obtain ⟨q, hq, hqU⟩ : ∃ q ∈ Qs Q A B K, q ∉ U H Q A B K := by
    by_contra hno
    push Not at hno
    have : Qs Q A B K ⊆ U H Q A B K ∩ Qs Q A B K := fun z hz => mem_inter.2 ⟨hno z hz, hz⟩
    have := card_le_card this
    rw [T.Qs_card] at this; omega
  have hqm := mem_Qs.1 hq
  obtain ⟨W, hW, hWq⟩ := R2 hC T.hQ T.hA T.QA (mem_inter.2 ⟨hqm.1, hqm.2.1⟩)
  obtain ⟨c, hc, hcP⟩ := W_cstar hC T hq hW hWq
  have hcAB : c ∈ A ∩ B := by simp only [mem_inter] at hc ⊢; exact hc.1
  obtain ⟨Y, hY, hYc⟩ := R2 hC T.hA T.hB T.AB hcAB
  have hYU := tight_trace hC T h3 hY hc hYc
  have hqY : q ∉ Y := by
    intro h
    apply hqU
    rw [← hYU]; exact mem_inter.2 ⟨h, mem_union.2 (Or.inl hq)⟩
  obtain ⟨-, hYsub⟩ := step1 hC T hq hW hWq hcP hY hc hYc hqY
  apply card_le_card
  intro z hz
  rw [mem_inter] at hz
  have hzY : z ∈ Y := by
    rw [← hYU] at hz; exact (mem_inter.1 hz.1).1
  exact mem_inter.2 ⟨hYsub (mem_inter.2 ⟨hzY, hz.2⟩), hz.2⟩

/-- Theorem W7-I in triangle form: no triangle configuration exists in a counterexample. -/
theorem tri_false (T : Tri H Q A B K xab xak xbk) : False := by
  -- the six orderings of the base
  have T1 := T                          -- (A,B,K)
  have T2 := T.swapAB                   -- (B,A,K)
  have T3 := T.swapBK                   -- (A,K,B)
  have T4 := T.swapBK.swapAB            -- (K,A,B)
  have T5 := T.swapAB.swapBK            -- (B,K,A)
  have T6 := T.swapBK.swapAB.swapBK     -- (K,B,A)
  have s1 := star hC T1
  have s2 := star hC T2
  have s3 := star hC T3
  have s4 := star hC T4
  have s5 := star hC T5
  have s6 := star hC T6
  have u1 := U_split hC T1
  have u3 := U_split hC T3
  have u5 := U_split hC T5
  have t1 := step3 hC T1
  have t3 := step3 hC T3
  have t5 := step3 hC T5
  -- canonical names
  have e1 : U H Q B A K = U H Q A B K := (U_symm H Q A B K).symm
  have e2 : U H Q K B A = U H Q B K A := (U_symm H Q B K A).symm
  have e3 : U H Q K A B = U H Q A K B := (U_symm H Q A K B).symm
  have f1 : Qs Q A K B = Qs Q A B K := (Qs_swap Q A B K).symm
  have f2 : Qs Q B K A = Qs Q B A K := (Qs_swap Q B A K).symm
  have f3 : Qs Q K B A = Qs Q K A B := (Qs_swap Q K A B).symm
  rw [e1] at s2
  rw [f1, e2] at s3
  rw [e3, f1] at s4
  rw [f2, f3, e3] at s5
  rw [e2, f3, f2, e1] at s6
  rw [f1] at u3
  rw [f2, f3] at u5
  omega

end Counter

/-! ## The leaf theorem in the original 5-pair language -/

section Leaf
variable {H : Finset (Finset V)} (hC : Counter H)
include hC

/-- From a 5-pair `(a, b)` and cross-type singles `G` (type `v`), `G'` (type `w`) with
`A_G ∩ A_G' = {p}` we get the triangle `Tri H a b G G' v w p` (Tri-0). -/
theorem mkTri {a b G G' : Finset V} (ha : a ∈ H) (hb : b ∈ H) (hG : G ∈ H) (hG' : G' ∈ H)
    (hM : (a ∩ b).card = 5) {v w : V} (hv : G ∩ (a ∩ b) = {v}) (hw : G' ∩ (a ∩ b) = {w})
    (hvw : v ≠ w) {p : V} (hp : G ∩ G' ∩ (a \ b) = {p}) : Tri H a b G G' v w p := by
  obtain ⟨hGa, hGb, -⟩ := single_card hC ha hb hG hM hv
  obtain ⟨hG'a, hG'b, -⟩ := single_card hC ha hb hG' hM hw
  have h1 : (G ∩ G' ∩ (a \ b)).card = 1 := by rw [hp, card_singleton]
  have hSc := S_c hC ha hb hG hG' hM hv hw hvw h1
  have key : ∀ z, z ∈ a → z ∈ b → z ∈ G → z ∈ G' → False := by
    intro z hza hzb hzG hzG'
    have e1 := eq_of_mem_singleton' hv (mem_inter.2 ⟨hzG, mem_inter.2 ⟨hza, hzb⟩⟩)
    have e2 := eq_of_mem_singleton' hw (mem_inter.2 ⟨hzG', mem_inter.2 ⟨hza, hzb⟩⟩)
    exact hvw (e1 ▸ e2)
  have eC : b ∩ G ∩ G' = G ∩ (b \ a) := by
    ext z
    simp only [mem_inter, mem_sdiff]
    constructor
    · rintro ⟨⟨hzb, hzG⟩, hzG'⟩
      exact ⟨hzG, hzb, fun hza => key z hza hzb hzG hzG'⟩
    · rintro ⟨hzG, hzb, hza⟩
      have : z ∈ G' ∩ (b \ a) := by rw [← hSc]; simp [hzG, hzb, hza]
      simp only [mem_inter, mem_sdiff] at this
      exact ⟨⟨hzb, hzG⟩, this.1⟩
  have hC4 : (G ∩ (b \ a)).card = 4 := by
    have r1 := card_split_right G a b
    rw [hv, card_singleton] at r1
    omega
  have hGG' : (G ∩ G').card = 5 := by
    have := (cross_class hC ha hb hG hG' hM hv hw hvw).2.2.2.2.2
    have e : G ∩ G' ∩ (b \ a) = G ∩ (b \ a) := by
      ext z
      simp only [mem_inter, mem_sdiff]
      constructor
      · rintro ⟨⟨hzG, -⟩, hzb, hza⟩; exact ⟨hzG, hzb, hza⟩
      · rintro ⟨hzG, hzb, hza⟩
        have : z ∈ G' ∩ (b \ a) := by rw [← hSc]; simp [hzG, hzb, hza]
        simp only [mem_inter, mem_sdiff] at this
        exact ⟨⟨hzG, this.1⟩, hzb, hza⟩
    rw [e, hC4, h1] at this
    exact this
  exact {
    hQ := ha
    hA := hb
    hB := hG
    hK := hG'
    QA := hM
    QB := by rw [inter_comm]; exact hGa
    QK := by rw [inter_comm]; exact hG'a
    AB := by rw [inter_comm]; exact hGb
    AK := by rw [inter_comm]; exact hG'b
    BK := hGG'
    tAB := by rw [inter_comm]; exact hv
    tAK := by rw [inter_comm]; exact hw
    tBK := by
      ext z
      simp only [mem_inter, mem_singleton]
      constructor
      · rintro ⟨⟨hza, hzG⟩, hzG'⟩
        have hzb : z ∉ b := fun hzb => key z hza hzb hzG hzG'
        exact eq_of_mem_singleton' hp (by simp [hza, hzG, hzG', hzb])
      · rintro rfl
        have := mem_of_eq_singleton' hp
        simp only [mem_inter, mem_sdiff] at this
        exact ⟨⟨this.2.1, this.1.1⟩, this.1.2⟩
    C4 := by rw [eC]; exact hC4
    QC := by
      rw [Finset.disjoint_left]
      intro z hza hz
      simp only [mem_inter] at hz
      exact key z hza hz.1.1 hz.1.2 hz.2 }

/-- **Theorem W7-I** (upper.md §7.4, refereed): in a counterexample no 5-pair has cross-type singles
in a triangle class, i.e. with `|A_G ∩ A_G'| = 1` or `|C_G ∩ C_G'| = 1`. -/
theorem W7I_cross {a b G G' : Finset V} (ha : a ∈ H) (hb : b ∈ H) (hG : G ∈ H) (hG' : G' ∈ H)
    (hM : (a ∩ b).card = 5) {v w : V} (hv : G ∩ (a ∩ b) = {v}) (hw : G' ∩ (a ∩ b) = {w})
    (hvw : v ≠ w) :
    (G ∩ G' ∩ (a \ b)).card ≠ 1 ∧ (G ∩ G' ∩ (b \ a)).card ≠ 1 := by
  constructor
  · intro h1
    obtain ⟨p, hp⟩ := card_eq_one.1 h1
    exact tri_false hC (mkTri hC ha hb hG hG' hM hv hw hvw hp)
  · intro h1
    obtain ⟨p, hp⟩ := card_eq_one.1 h1
    have hM' : (b ∩ a).card = 5 := by rw [inter_comm]; exact hM
    have hv' : G ∩ (b ∩ a) = {v} := by rw [inter_comm b a]; exact hv
    have hw' : G' ∩ (b ∩ a) = {w} := by rw [inter_comm b a]; exact hw
    exact tri_false hC (mkTri hC hb ha hG hG' hM' hv' hw' hvw hp)

end Leaf

namespace W7I

/-- **`W7I_leaf`**: the body of HandA.lean's `def W7I_leaf : Prop`, with `W7I_prop` and `CrossPair`
unfolded verbatim. (Named in the sub-namespace `W7I` to avoid clashing with HandA's `def`; the
assembly closes HandA's hypothesis with `exact W7I.W7I_leaf`, which is accepted by unfolding.) -/
theorem W7I_leaf : ∀ (n : ℕ) (H : Finset (Finset (Fin n))), Counter H →
    ∀ X Y G G' : Finset (Fin n),
      (X ∈ H ∧ Y ∈ H ∧ G ∈ H ∧ G' ∈ H ∧ (X ∩ Y).card = 5 ∧
        ∃ v w : Fin n, v ≠ w ∧ G ∩ (X ∩ Y) = {v} ∧ G' ∩ (X ∩ Y) = {w}) →
      (G ∩ G' ∩ (X \ Y)).card ≠ 1 ∧ (G ∩ G' ∩ (Y \ X)).card ≠ 1 := by
  intro n H hC X Y G G' ⟨hX, hY, hG, hG', h5, v, w, hvw, hv, hw⟩
  exact W7I_cross hC hX hY hG hG' h5 hv hw hvw

end W7I

end Erdos616R21
