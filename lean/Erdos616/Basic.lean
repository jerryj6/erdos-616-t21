import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Erdős #616 at r = 21: statement, reduction, and the §1 lemmas of the hand proof

Definitions copied verbatim from google-deepmind/formal-conjectures
(FormalConjecturesForMathlib/Combinatorics/Hypergraph/{Finite,Extremal}.lean), same namespaces.
-/

namespace Set

/-- A family of finite sets has a transversal with at most `k` vertices. -/
def HasFiniteTransversal {V : Type*} (F : Set (Finset V)) (k : ℕ) : Prop :=
  ∃ S : Finset V, S.card ≤ k ∧ ∀ e ∈ F, ∃ v ∈ S, v ∈ e

end Set

namespace Finset

variable {V : Type*} [DecidableEq V]

/-- Every edge has exactly `r` vertices. -/
def IsUniform (H : Finset (Finset V)) (r : ℕ) : Prop := ∀ e ∈ H, e.card = r

/-- The edges induced on a vertex set. -/
def hypergraphInduce (H : Finset (Finset V)) (S : Finset V) : Finset (Finset V) :=
  H.filter (· ⊆ S)

end Finset

namespace Hypergraph

/-- Maximum global transversal size under a local vertex-set constraint.
Infinity records that no finite bound works. -/
noncomputable def localTransversalBound (r v a : ℕ) : ℕ∞ :=
  ⨅ (b : ℕ) (_ : ∀ (n : ℕ) (H : Finset (Finset (Fin n))), H.IsUniform r →
    (∀ S : Finset (Fin n), S.card ≤ v →
      (H.hypergraphInduce S : Set (Finset (Fin n))).HasFiniteTransversal a) →
    (H : Set (Finset (Fin n))).HasFiniteTransversal b), (b : ℕ∞)

end Hypergraph

namespace Erdos616R21

open Finset

/-- The r = 21 instance of `erdos_616` (3·21 − 3 = 60). -/
def Statement : Prop := Hypergraph.localTransversalBound 21 60 1 = 4

variable {V : Type*} [DecidableEq V]

/-! ## Property L -/

/-- Property L_v: every nonempty subfamily whose union has at most `v` vertices has a common vertex. -/
def PropL (H : Finset (Finset V)) (v : ℕ) : Prop :=
  ∀ F ⊆ H, F.Nonempty → (F.biUnion id).card ≤ v → ∃ x, ∀ e ∈ F, x ∈ e

/-- The formal-conjectures local hypothesis (with `a = 1`) is exactly property L. -/
theorem local_iff_propL (H : Finset (Finset V)) (v : ℕ) :
    (∀ S : Finset V, S.card ≤ v →
      (H.hypergraphInduce S : Set (Finset V)).HasFiniteTransversal 1) ↔ PropL H v := by
  constructor
  · intro h F hF hne hcard
    obtain ⟨T, hT, hTe⟩ := h (F.biUnion id) hcard
    obtain ⟨e0, he0⟩ := hne
    have mem_ind : ∀ e ∈ F, e ∈ H.hypergraphInduce (F.biUnion id) := by
      intro e he
      simp only [hypergraphInduce, mem_filter]
      exact ⟨hF he, fun y hy => mem_biUnion.2 ⟨e, he, hy⟩⟩
    obtain ⟨x, hxT, hxe0⟩ := hTe e0 (by exact_mod_cast mem_ind e0 he0)
    refine ⟨x, fun e he => ?_⟩
    obtain ⟨y, hyT, hye⟩ := hTe e (by exact_mod_cast mem_ind e he)
    have : y = x := Finset.card_le_one.1 hT y hyT x hxT
    exact this ▸ hye
  · intro h S hS
    by_cases hne : (H.hypergraphInduce S).Nonempty
    · have hsub : H.hypergraphInduce S ⊆ H := filter_subset _ _
      have hU : ((H.hypergraphInduce S).biUnion id).card ≤ v := by
        refine le_trans (card_le_card ?_) hS
        intro y hy
        obtain ⟨e, he, hye⟩ := mem_biUnion.1 hy
        simp only [hypergraphInduce, mem_filter] at he
        exact he.2 hye
      obtain ⟨x, hx⟩ := h _ hsub hne hU
      refine ⟨{x}, by simp, fun e he => ⟨x, by simp, hx e (by exact_mod_cast he)⟩⟩
    · refine ⟨∅, by simp, fun e he => ?_⟩
      exact absurd ⟨e, by exact_mod_cast he⟩ hne

/-! ## Reduction of the statement to the two directions -/

theorem le_four_of
    (h : ∀ (n : ℕ) (H : Finset (Finset (Fin n))), H.IsUniform 21 → PropL H 60 →
      (H : Set (Finset (Fin n))).HasFiniteTransversal 4) :
    Hypergraph.localTransversalBound 21 60 1 ≤ 4 := by
  unfold Hypergraph.localTransversalBound
  exact iInf₂_le_of_le 4 (fun n H hu hl => h n H hu ((local_iff_propL H 60).1 hl)) (by simp)

theorem transversal_mono {W : Type*} {F : Set (Finset W)} {a b : ℕ} (hab : a ≤ b)
    (h : F.HasFiniteTransversal a) : F.HasFiniteTransversal b := by
  obtain ⟨S, hS, hSe⟩ := h
  exact ⟨S, le_trans hS hab, hSe⟩

theorem four_le_of (n : ℕ) (H : Finset (Finset (Fin n))) (hu : H.IsUniform 21)
    (hl : PropL H 60) (hτ : ¬ (H : Set (Finset (Fin n))).HasFiniteTransversal 3) :
    4 ≤ Hypergraph.localTransversalBound 21 60 1 := by
  unfold Hypergraph.localTransversalBound
  refine le_iInf₂ fun b hb => ?_
  have hT := hb n H hu ((local_iff_propL H 60).2 hl)
  have : 4 ≤ b := by
    by_contra hlt
    exact hτ (transversal_mono (by omega) hT)
  exact_mod_cast this

/-- The counterexample predicate for the upper bound: 21-uniform, property L_60, and τ ≥ 5
(every set of at most 4 vertices is avoided by some edge). -/
structure Counter (H : Finset (Finset V)) : Prop where
  unif : ∀ e ∈ H, e.card = 21
  propL : PropL H 60
  avoid : ∀ B : Finset V, B.card ≤ 4 → ∃ e ∈ H, Disjoint e B

theorem counter_of_not_transversal {H : Finset (Finset V)} (hu : H.IsUniform 21)
    (hl : PropL H 60) (hτ : ¬ (H : Set (Finset V)).HasFiniteTransversal 4) : Counter H := by
  refine ⟨hu, hl, fun B hB => ?_⟩
  by_contra hno
  push Not at hno
  apply hτ
  refine ⟨B, hB, fun e he => ?_⟩
  have := hno e (by exact_mod_cast he)
  rw [Finset.not_disjoint_iff] at this
  obtain ⟨x, hxe, hxB⟩ := this
  exact ⟨x, hxB, hxe⟩

/-- Upper bound reduction: if no counterexample exists, `t(21) ≤ 4`. -/
theorem le_four_of_noCounter (h : ∀ (n : ℕ) (H : Finset (Finset (Fin n))), ¬ Counter H) :
    Hypergraph.localTransversalBound 21 60 1 ≤ 4 :=
  le_four_of fun n H hu hl => by
    by_contra hτ
    exact h n H (counter_of_not_transversal hu hl hτ)

/-- The statement follows from "no counterexample" and one lower-bound example. -/
theorem statement_of (hub : ∀ (n : ℕ) (H : Finset (Finset (Fin n))), ¬ Counter H)
    (hlb : ∃ (n : ℕ) (H : Finset (Finset (Fin n))), H.IsUniform 21 ∧ PropL H 60 ∧
      ¬ (H : Set (Finset (Fin n))).HasFiniteTransversal 3) : Statement := by
  obtain ⟨n, H, hu, hl, hτ⟩ := hlb
  exact le_antisymm (le_four_of_noCounter hub) (four_le_of n H hu hl hτ)

/-! ## Reduction to minimal empty-intersection families -/

/-- Property L in "span" form: a nonempty subfamily with no common vertex spans more than `v`. -/
theorem propL_iff_span (H : Finset (Finset V)) (v : ℕ) :
    PropL H v ↔ ∀ F ⊆ H, F.Nonempty → (∀ x, ∃ e ∈ F, x ∉ e) → v < (F.biUnion id).card := by
  constructor
  · intro h F hF hne hno
    by_contra hle
    obtain ⟨x, hx⟩ := h F hF hne (by omega)
    obtain ⟨e, he, hxe⟩ := hno x
    exact hxe (hx e he)
  · intro h F hF hne hcard
    by_contra hno
    push Not at hno
    have := h F hF hne hno
    omega

/-- It suffices to check *minimal* families with empty intersection: every family with empty
intersection contains one that is minimal for inclusion, and its union is no larger. -/
theorem propL_of_minimal (H : Finset (Finset V)) (v : ℕ)
    (hmin : ∀ F ⊆ H, F.Nonempty → (∀ x, ∃ e ∈ F, x ∉ e) →
      (∀ F' ⊂ F, F'.Nonempty → ∃ x, ∀ e ∈ F', x ∈ e) → v < (F.biUnion id).card) :
    PropL H v := by
  rw [propL_iff_span]
  intro F
  induction F using Finset.strongInduction with
  | H F ih =>
    intro hF hne hno
    by_cases hm : ∀ F' ⊂ F, F'.Nonempty → ∃ x, ∀ e ∈ F', x ∈ e
    · exact hmin F hF hne hno hm
    · push Not at hm
      obtain ⟨F', hF'F, hF'ne, hF'no⟩ := hm
      have h1 := ih F' hF'F (hF'F.subset.trans hF) hF'ne hF'no
      exact lt_of_lt_of_le h1 (card_le_card (biUnion_subset_biUnion_of_subset_left _ hF'F.subset))

/-! ## Finset counting helpers -/

theorem card_split (X a b : Finset V) :
    (X ∩ (a ∪ b)).card = (X ∩ (a \ b)).card + (X ∩ (b \ a)).card + (X ∩ (a ∩ b)).card := by
  have h1 := card_sdiff_add_card_inter (X ∩ (a ∪ b)) b
  have h2 := card_sdiff_add_card_inter (X ∩ b) a
  have e1 : (X ∩ (a ∪ b)) \ b = X ∩ (a \ b) := by ext; simp <;> tauto
  have e2 : X ∩ (a ∪ b) ∩ b = X ∩ b := by ext; simp <;> tauto
  have e3 : (X ∩ b) \ a = X ∩ (b \ a) := by ext; simp <;> tauto
  have e4 : X ∩ b ∩ a = X ∩ (a ∩ b) := by ext; simp <;> tauto
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  omega

theorem card_split_left (X a b : Finset V) :
    (X ∩ a).card = (X ∩ (a \ b)).card + (X ∩ (a ∩ b)).card := by
  have h := card_sdiff_add_card_inter (X ∩ a) b
  have e1 : (X ∩ a) \ b = X ∩ (a \ b) := by ext; simp <;> tauto
  have e2 : X ∩ a ∩ b = X ∩ (a ∩ b) := by ext; simp <;> tauto
  rw [e1, e2] at h
  omega

theorem card_split_right (X a b : Finset V) :
    (X ∩ b).card = (X ∩ (b \ a)).card + (X ∩ (a ∩ b)).card := by
  rw [card_split_left X b a, inter_comm b a]

theorem card_sdiff_eq (X U : Finset V) : (X \ U).card + (X ∩ U).card = X.card :=
  card_sdiff_add_card_inter X U

theorem card_biUnion_le_mul {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → Finset V) (n : ℕ)
    (h : ∀ i ∈ s, (t i).card ≤ n) : (s.biUnion t).card ≤ s.card * n := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [biUnion_insert, card_insert_of_notMem ha, add_mul, one_mul]
    have h1 := card_union_le (t a) (s.biUnion t)
    have h2 := ih (fun i hi => h i (mem_insert_of_mem hi))
    have h3 := h a (mem_insert_self a s)
    omega

/-- Union of four sets, counted over the first two. -/
theorem card_union4_le (a b c d : Finset V) :
    (a ∪ b ∪ c ∪ d).card + ((c \ (a ∪ b)) ∩ (d \ (a ∪ b))).card ≤
      (a ∪ b).card + (c \ (a ∪ b)).card + (d \ (a ∪ b)).card := by
  have e : a ∪ b ∪ c ∪ d = (a ∪ b) ∪ ((c \ (a ∪ b)) ∪ (d \ (a ∪ b))) := by
    ext; simp <;> tauto
  rw [e]
  have h1 := card_union_le (a ∪ b) ((c \ (a ∪ b)) ∪ (d \ (a ∪ b)))
  have h2 := card_union_add_card_inter (c \ (a ∪ b)) (d \ (a ∪ b))
  omega

/-- Three sets with no common point: union = sum − pairwise intersections. -/
theorem card_union3_of_empty (a b c : Finset V) (h : ∀ x, x ∈ a → x ∈ b → x ∈ c → False) :
    (a ∪ b ∪ c).card + (a ∩ b).card + (a ∩ c).card + (b ∩ c).card = a.card + b.card + c.card := by
  have h1 := card_union_add_card_inter a b
  have h2 := card_union_add_card_inter (a ∪ b) c
  have e3 : (a ∪ b) ∩ c = (a ∩ c) ∪ (b ∩ c) := by ext; simp <;> tauto
  have h4 := card_union_add_card_inter (a ∩ c) (b ∩ c)
  have e5 : (a ∩ c) ∩ (b ∩ c) = ∅ := by
    ext x; simp only [mem_inter, Finset.notMem_empty, iff_false]; intro hx
    exact h x hx.1.1 hx.2.1 hx.1.2
  rw [e3] at h2
  rw [e5, card_empty] at h4
  omega

/-! ## Basic consequences of `Counter` (upper.md §1: F1, F2, L1) -/

section Counter

variable {H : Finset (Finset V)} (hC : Counter H)
include hC

/-- L on an explicit family of four edges. -/
theorem L4 {a b c d : Finset V} (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) (hd : d ∈ H)
    (h : ∀ x, x ∈ a → x ∈ b → x ∈ c → x ∈ d → False) : 61 ≤ (a ∪ b ∪ c ∪ d).card := by
  have := (propL_iff_span H 60).1 hC.propL {a, b, c, d}
    (by simp [insert_subset_iff, ha, hb, hc, hd]) (by simp)
    (fun x => by
      by_contra hx; push Not at hx
      exact h x (hx a (by simp)) (hx b (by simp)) (hx c (by simp)) (hx d (by simp)))
  have e : ({a, b, c, d} : Finset (Finset V)).biUnion id = a ∪ b ∪ c ∪ d := by
    ext; simp <;> tauto
  rw [e] at this; omega

theorem L3 {a b c : Finset V} (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H)
    (h : ∀ x, x ∈ a → x ∈ b → x ∈ c → False) : 61 ≤ (a ∪ b ∪ c).card := by
  have := L4 hC ha hb hc hc (fun x h1 h2 h3 _ => h x h1 h2 h3)
  simpa [union_assoc] using this

theorem L2 {a b : Finset V} (ha : a ∈ H) (hb : b ∈ H)
    (h : ∀ x, x ∈ a → x ∈ b → False) : 61 ≤ (a ∪ b).card := by
  have := L4 hC ha hb hb hb (fun x h1 h2 _ _ => h x h1 h2)
  simpa [union_assoc] using this

/-- F1, pairwise part. -/
theorem inter2 {a b : Finset V} (ha : a ∈ H) (hb : b ∈ H) : ∃ x, x ∈ a ∧ x ∈ b := by
  by_contra hno; push Not at hno
  have h1 := L2 hC ha hb (fun x h1 h2 => hno x h1 h2)
  have h2 := card_union_le a b
  rw [hC.unif a ha, hC.unif b hb] at h2
  omega

/-- F1: the hypergraph is 3-wise intersecting. -/
theorem inter3 {a b c : Finset V} (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) :
    ∃ x, x ∈ a ∧ x ∈ b ∧ x ∈ c := by
  by_contra hno; push Not at hno
  have hno' : ∀ x, x ∈ a → x ∈ b → x ∈ c → False := fun x h1 h2 h3 => hno x h1 h2 h3
  have h1 := L3 hC ha hb hc hno'
  have h2 := card_union3_of_empty a b c hno'
  have pos : ∀ {s t : Finset V}, s ∈ H → t ∈ H → 1 ≤ (s ∩ t).card := by
    intro s t hs ht
    obtain ⟨x, hxs, hxt⟩ := inter2 hC hs ht
    exact card_pos.2 ⟨x, mem_inter.2 ⟨hxs, hxt⟩⟩
  have := pos ha hb; have := pos ha hc; have := pos hb hc
  rw [hC.unif a ha, hC.unif b hb, hC.unif c hc] at h2
  omega

/-- L1 = first half of Lemma A: any two edges meet in at least 5 vertices. -/
theorem inter_ge5 {a b : Finset V} (ha : a ∈ H) (hb : b ∈ H) : 5 ≤ (a ∩ b).card := by
  by_contra hlt
  obtain ⟨e, he, hdis⟩ := hC.avoid (a ∩ b) (by omega)
  obtain ⟨x, hxa, hxb, hxe⟩ := inter3 hC ha hb he
  exact Finset.disjoint_left.1 hdis hxe (mem_inter.2 ⟨hxa, hxb⟩)

/-! ## Lemma R (rigidity at a 5-pair) -/

/-- R.1: the intersection of two edges is a transversal (F1). -/
theorem R1 {a b F : Finset V} (ha : a ∈ H) (hb : b ∈ H) (hF : F ∈ H) :
    (F ∩ (a ∩ b)).Nonempty := by
  obtain ⟨x, hxa, hxb, hxF⟩ := inter3 hC ha hb hF
  exact ⟨x, by simp [hxa, hxb, hxF]⟩

/-- R.2: at a 5-pair, every point of `M` is the type of some single. -/
theorem R2 {a b : Finset V} (ha : a ∈ H) (hb : b ∈ H) (hM : (a ∩ b).card = 5)
    {x : V} (hx : x ∈ a ∩ b) : ∃ F ∈ H, F ∩ (a ∩ b) = {x} := by
  obtain ⟨F, hF, hdis⟩ := hC.avoid ((a ∩ b).erase x) (by rw [card_erase_of_mem hx]; omega)
  refine ⟨F, hF, ?_⟩
  have key : ∀ z ∈ F ∩ (a ∩ b), z = x := by
    intro z hz
    by_contra hzx
    rw [mem_inter] at hz
    exact Finset.disjoint_left.1 hdis hz.1 (mem_erase.2 ⟨hzx, hz.2⟩)
  obtain ⟨y, hy⟩ := R1 hC ha hb hF
  have hyx := key y hy
  ext z
  simp only [mem_singleton]
  constructor
  · exact key z
  · rintro rfl; exact hyx ▸ hy

/-- R.3: two singles of different types at a 5-pair. -/
theorem R3 {a b F F' : Finset V} (ha : a ∈ H) (hb : b ∈ H) (hF : F ∈ H) (hF' : F' ∈ H)
    (hM : (a ∩ b).card = 5) {x y : V} (hx : F ∩ (a ∩ b) = {x}) (hy : F' ∩ (a ∩ b) = {y})
    (hxy : x ≠ y) :
    (F ∩ a).card = 5 ∧ (F ∩ b).card = 5 ∧ (F' ∩ a).card = 5 ∧ (F' ∩ b).card = 5 ∧
    Disjoint (F \ (a ∪ b)) (F' \ (a ∪ b)) ∧
    (F \ (a ∪ b)).card = 12 ∧ (F' \ (a ∪ b)).card = 12 := by
  have hL := L4 hC ha hb hF hF' (fun z hza hzb hzF hzF' => by
    have h1 : z ∈ F ∩ (a ∩ b) := by simp [hza, hzb, hzF]
    have h2 : z ∈ F' ∩ (a ∩ b) := by simp [hza, hzb, hzF']
    rw [hx, mem_singleton] at h1
    rw [hy, mem_singleton] at h2
    exact hxy (h1 ▸ h2))
  have hU := card_union4_le a b F F'
  have hab := card_union_add_card_inter a b
  have i1 := inter_ge5 hC hF ha
  have i2 := inter_ge5 hC hF hb
  have i3 := inter_ge5 hC hF' ha
  have i4 := inter_ge5 hC hF' hb
  have s1 := card_sdiff_eq F (a ∪ b)
  have s2 := card_sdiff_eq F' (a ∪ b)
  have c1 := card_split F a b
  have c2 := card_split F' a b
  have l1 := card_split_left F a b
  have l2 := card_split_left F' a b
  have r1 := card_split_right F a b
  have r2 := card_split_right F' a b
  rw [hx, card_singleton] at c1 l1 r1
  rw [hy, card_singleton] at c2 l2 r2
  rw [hC.unif a ha, hC.unif b hb] at hab
  rw [hC.unif F hF] at s1
  rw [hC.unif F' hF'] at s2
  have hint : ((F \ (a ∪ b)) ∩ (F' \ (a ∪ b))).card = 0 := by omega
  refine ⟨by omega, by omega, by omega, by omega, ?_, by omega, by omega⟩
  rw [card_eq_zero] at hint
  exact disjoint_iff_inter_eq_empty.2 hint

/-- Cor R1 / R.3 for one single: every single at a 5-pair meets both edges in exactly 5
and has exactly 12 points outside their union. -/
theorem single_card {a b F : Finset V} (ha : a ∈ H) (hb : b ∈ H) (hF : F ∈ H)
    (hM : (a ∩ b).card = 5) {x : V} (hx : F ∩ (a ∩ b) = {x}) :
    (F ∩ a).card = 5 ∧ (F ∩ b).card = 5 ∧ (F \ (a ∪ b)).card = 12 := by
  have hxM : x ∈ a ∩ b := by
    have : x ∈ F ∩ (a ∩ b) := by rw [hx]; exact mem_singleton_self x
    exact (mem_inter.1 this).2
  obtain ⟨y, hyM, hyx⟩ : ∃ y ∈ a ∩ b, y ≠ x := by
    by_contra hno; push Not at hno
    have : a ∩ b ⊆ {x} := fun z hz => mem_singleton.2 (hno z hz)
    have := card_le_card this
    rw [card_singleton] at this; omega
  obtain ⟨F', hF', hy⟩ := R2 hC ha hb hM hyM
  obtain ⟨h1, h2, -, -, -, h3, -⟩ := R3 hC ha hb hF hF' hM hx hy hyx.symm
  exact ⟨h1, h2, h3⟩

/-- D1: an edge not containing `M` has at most 9 points in `a ∪ b`. -/
theorem D1 {a b L : Finset V} (ha : a ∈ H) (hb : b ∈ H) (hL : L ∈ H)
    (hM : (a ∩ b).card = 5) {x : V} (hxM : x ∈ a ∩ b) (hxL : x ∉ L) :
    (L ∩ (a ∪ b)).card ≤ 9 := by
  obtain ⟨F, hF, hx⟩ := R2 hC ha hb hM hxM
  obtain ⟨-, -, hO⟩ := single_card hC ha hb hF hM hx
  have h4 := L4 hC ha hb hL hF (fun z hza hzb hzL hzF => by
    have h1 : z ∈ F ∩ (a ∩ b) := by simp [hza, hzb, hzF]
    rw [hx, mem_singleton] at h1
    exact hxL (h1 ▸ hzL))
  have hU := card_union4_le a b L F
  have hab := card_union_add_card_inter a b
  have s1 := card_sdiff_eq L (a ∪ b)
  rw [hC.unif a ha, hC.unif b hb] at hab
  rw [hC.unif L hL] at s1
  omega

/-! ## Lemma S (cross-type relations) -/

section S
variable {a b G G' : Finset V} {v w : V}

theorem S_a_A (ha : a ∈ H) (hb : b ∈ H) (hG : G ∈ H) (hG' : G' ∈ H)
    (hv : G ∩ (a ∩ b) = {v}) (hw : G' ∩ (a ∩ b) = {w}) (hvw : v ≠ w) :
    ∃ p, p ∈ G ∧ p ∈ G' ∧ p ∈ a ∧ p ∉ b := by
  obtain ⟨z, hza, hzG, hzG'⟩ := inter3 hC ha hG hG'
  refine ⟨z, hzG, hzG', hza, fun hzb => ?_⟩
  have h1 : z ∈ G ∩ (a ∩ b) := by simp [hza, hzb, hzG]
  have h2 : z ∈ G' ∩ (a ∩ b) := by simp [hza, hzb, hzG']
  rw [hv, mem_singleton] at h1
  rw [hw, mem_singleton] at h2
  exact hvw (h1 ▸ h2)

theorem S_a_C (ha : a ∈ H) (hb : b ∈ H) (hG : G ∈ H) (hG' : G' ∈ H)
    (hv : G ∩ (a ∩ b) = {v}) (hw : G' ∩ (a ∩ b) = {w}) (hvw : v ≠ w) :
    ∃ p, p ∈ G ∧ p ∈ G' ∧ p ∈ b ∧ p ∉ a := by
  rw [inter_comm a b] at hv hw
  exact S_a_A hC hb ha hG hG' hv hw hvw

theorem S_a_O (ha : a ∈ H) (hb : b ∈ H) (hG : G ∈ H) (hG' : G' ∈ H)
    (hM : (a ∩ b).card = 5) (hv : G ∩ (a ∩ b) = {v}) (hw : G' ∩ (a ∩ b) = {w}) (hvw : v ≠ w) :
    Disjoint (G \ (a ∪ b)) (G' \ (a ∪ b)) :=
  (R3 hC ha hb hG hG' hM hv hw hvw).2.2.2.2.1

/-- S(b): `|A_G ∩ A_G'| + |C_G ∩ C_G'| ≥ 5`. -/
theorem S_b (ha : a ∈ H) (hb : b ∈ H) (hG : G ∈ H) (hG' : G' ∈ H)
    (hM : (a ∩ b).card = 5) (hv : G ∩ (a ∩ b) = {v}) (hw : G' ∩ (a ∩ b) = {w}) (hvw : v ≠ w) :
    5 ≤ (G ∩ G' ∩ (a \ b)).card + (G ∩ G' ∩ (b \ a)).card := by
  have hO := S_a_O hC ha hb hG hG' hM hv hw hvw
  have hsub : G ∩ G' ⊆ (G ∩ G' ∩ (a \ b)) ∪ (G ∩ G' ∩ (b \ a)) := by
    intro z hz
    rw [mem_inter] at hz
    by_cases hza : z ∈ a <;> by_cases hzb : z ∈ b
    · exfalso
      have h1 : z ∈ G ∩ (a ∩ b) := by simp [hza, hzb, hz.1]
      have h2 : z ∈ G' ∩ (a ∩ b) := by simp [hza, hzb, hz.2]
      rw [hv, mem_singleton] at h1
      rw [hw, mem_singleton] at h2
      exact hvw (h1 ▸ h2)
    · simp [hza, hzb, hz.1, hz.2]
    · simp [hza, hzb, hz.1, hz.2]
    · exfalso
      exact Finset.disjoint_left.1 hO (by simp [hza, hzb, hz.1] : z ∈ G \ (a ∪ b))
        (by simp [hza, hzb, hz.2])
  have h1 := card_le_card hsub
  have h2 := card_union_le (G ∩ G' ∩ (a \ b)) (G ∩ G' ∩ (b \ a))
  have h3 := inter_ge5 hC hG hG'
  omega

/-- S(c): if `A_G ∩ A_G'` is a single point then `C_G = C_G'`. -/
theorem S_c (ha : a ∈ H) (hb : b ∈ H) (hG : G ∈ H) (hG' : G' ∈ H)
    (hM : (a ∩ b).card = 5) (hv : G ∩ (a ∩ b) = {v}) (hw : G' ∩ (a ∩ b) = {w}) (hvw : v ≠ w)
    (h1 : (G ∩ G' ∩ (a \ b)).card = 1) : G ∩ (b \ a) = G' ∩ (b \ a) := by
  obtain ⟨p, hp⟩ := card_eq_one.1 h1
  have hpG : p ∈ G ∧ p ∈ G' ∧ p ∈ a ∧ p ∉ b := by
    have : p ∈ G ∩ G' ∩ (a \ b) := by rw [hp]; exact mem_singleton_self p
    simp only [mem_inter, mem_sdiff] at this
    exact ⟨this.1.1, this.1.2, this.2.1, this.2.2⟩
  have hvab : v ∈ a ∩ b := by
    have : v ∈ G ∩ (a ∩ b) := by rw [hv]; exact mem_singleton_self v
    exact (mem_inter.1 this).2
  have hvG : v ∈ G := by
    have : v ∈ G ∩ (a ∩ b) := by rw [hv]; exact mem_singleton_self v
    exact (mem_inter.1 this).1
  obtain ⟨hGa, hGb, -⟩ := single_card hC ha hb hG hM hv
  obtain ⟨-, hG'b, -⟩ := single_card hC ha hb hG' hM hw
  -- the 5-pair (a, G), M' = a ∩ G
  have hM' : (a ∩ G).card = 5 := by rw [inter_comm]; exact hGa
  have hbM' : b ∩ (a ∩ G) = {v} := by
    ext z; constructor
    · intro hz
      have : z ∈ G ∩ (a ∩ b) := by simp only [mem_inter] at hz ⊢; tauto
      rw [hv] at this; exact this
    · intro hz; rw [mem_singleton] at hz; subst hz
      simp only [mem_inter] at hvab ⊢; exact ⟨hvab.2, hvab.1, hvG⟩
  have hG'M' : G' ∩ (a ∩ G) = {p} := by
    ext z; constructor
    · intro hz
      simp only [mem_inter] at hz
      have hzb : z ∉ b := by
        intro hzb
        have h1' : z ∈ G ∩ (a ∩ b) := by simp [hz.2.1, hzb, hz.2.2]
        have h2' : z ∈ G' ∩ (a ∩ b) := by simp [hz.2.1, hzb, hz.1]
        rw [hv, mem_singleton] at h1'
        rw [hw, mem_singleton] at h2'
        exact hvw (h1' ▸ h2')
      have : z ∈ G ∩ G' ∩ (a \ b) := by simp [hz.1, hz.2.1, hz.2.2, hzb]
      rw [hp] at this; exact this
    · intro hz; rw [mem_singleton] at hz; subst hz
      simp [hpG.1, hpG.2.1, hpG.2.2.1]
  have hvp : v ≠ p := by
    intro h; apply hpG.2.2.2; rw [← h]; exact (mem_inter.1 hvab).2
  have hdis := (R3 hC ha hG hb hG' hM' hbM' hG'M' hvp).2.2.2.2.1
  have hsub : G' ∩ (b \ a) ⊆ G ∩ (b \ a) := by
    intro z hz
    simp only [mem_inter, mem_sdiff] at hz ⊢
    refine ⟨?_, hz.2⟩
    by_contra hzG
    exact Finset.disjoint_left.1 hdis (by simp [hz.2.1, hz.2.2, hzG] : z ∈ b \ (a ∪ G))
      (by simp [hz.1, hz.2.2, hzG])
  have r1 := card_split_right G a b
  have r2 := card_split_right G' a b
  rw [hv, card_singleton] at r1
  rw [hw, card_singleton] at r2
  exact (eq_of_subset_of_card_le hsub (by omega)).symm

/-- S(c), symmetric form. -/
theorem S_c' (ha : a ∈ H) (hb : b ∈ H) (hG : G ∈ H) (hG' : G' ∈ H)
    (hM : (a ∩ b).card = 5) (hv : G ∩ (a ∩ b) = {v}) (hw : G' ∩ (a ∩ b) = {w}) (hvw : v ≠ w)
    (h1 : (G ∩ G' ∩ (b \ a)).card = 1) : G ∩ (a \ b) = G' ∩ (a \ b) := by
  rw [inter_comm a b] at hM hv hw
  exact S_c hC hb ha hG hG' hM hv hw hvw h1

end S

/-! ## Lemma K (multi edges) -/

theorem K_A {a b K : Finset V} (ha : a ∈ H) (hK : K ∈ H) :
    5 ≤ (K ∩ (a \ b)).card + (K ∩ (a ∩ b)).card := by
  have := inter_ge5 hC hK ha
  have := card_split_left K a b
  omega

theorem K_C {a b K : Finset V} (hb : b ∈ H) (hK : K ∈ H) :
    5 ≤ (K ∩ (b \ a)).card + (K ∩ (a ∩ b)).card := by
  have := inter_ge5 hC hK hb
  have := card_split_right K a b
  omega

theorem K_meets {a b K F : Finset V} (ha : a ∈ H) (hb : b ∈ H) (hK : K ∈ H) (hF : F ∈ H)
    {x : V} (hx : F ∩ (a ∩ b) = {x}) (hxK : x ∉ K) :
    (∃ p, p ∈ K ∧ p ∈ F ∧ p ∈ a ∧ p ∉ b) ∧ (∃ p, p ∈ K ∧ p ∈ F ∧ p ∈ b ∧ p ∉ a) := by
  have key : ∀ z, z ∈ F → z ∈ a → z ∈ b → z ∈ K → False := by
    intro z hzF hza hzb hzK
    have : z ∈ F ∩ (a ∩ b) := by simp [hza, hzb, hzF]
    rw [hx, mem_singleton] at this
    exact hxK (this ▸ hzK)
  constructor
  · obtain ⟨z, hza, hzF, hzK⟩ := inter3 hC ha hF hK
    exact ⟨z, hzK, hzF, hza, fun hzb => key z hzF hza hzb hzK⟩
  · obtain ⟨z, hzb, hzF, hzK⟩ := inter3 hC hb hF hK
    exact ⟨z, hzK, hzF, hzb, fun hza => key z hzF hza hzb hzK⟩

/-- Lemma K, second line: `|K∩A| + |K∩C| ≤ 9 − k − |K∩O_F|`. -/
theorem K_bound {a b K F : Finset V} (ha : a ∈ H) (hb : b ∈ H) (hK : K ∈ H) (hF : F ∈ H)
    (hM : (a ∩ b).card = 5) {x : V} (hx : F ∩ (a ∩ b) = {x}) (hxK : x ∉ K) :
    (K ∩ (a \ b)).card + (K ∩ (b \ a)).card + (K ∩ (a ∩ b)).card + (K ∩ (F \ (a ∪ b))).card
      ≤ 9 := by
  obtain ⟨-, -, hO⟩ := single_card hC ha hb hF hM hx
  have h4 := L4 hC ha hb hK hF (fun z hza hzb hzK hzF => by
    have : z ∈ F ∩ (a ∩ b) := by simp [hza, hzb, hzF]
    rw [hx, mem_singleton] at this
    exact hxK (this ▸ hzK))
  have hU := card_union4_le a b K F
  have hab := card_union_add_card_inter a b
  have s1 := card_sdiff_eq K (a ∪ b)
  have c1 := card_split K a b
  have e : (K \ (a ∪ b)) ∩ (F \ (a ∪ b)) = K ∩ (F \ (a ∪ b)) := by ext; simp <;> tauto
  rw [e] at hU
  rw [hC.unif a ha, hC.unif b hb] at hab
  rw [hC.unif K hK] at s1
  omega

/-! ## Lemma T (witnesses at a 5-pair) -/

/-- Lemma T, existence: for a single `G` of type `v` and `p ∈ A_G` there is an edge `W` with
`W ∩ ({v} ∪ A_G) = {p}` (note `a ∩ G = {v} ∪ A_G`). -/
theorem T_exists {a b G : Finset V} (ha : a ∈ H) (hb : b ∈ H) (hG : G ∈ H)
    (hM : (a ∩ b).card = 5) {v : V} (hv : G ∩ (a ∩ b) = {v}) {p : V} (hpG : p ∈ G)
    (hpa : p ∈ a) : ∃ W ∈ H, W ∩ (a ∩ G) = {p} := by
  obtain ⟨hGa, -, -⟩ := single_card hC ha hb hG hM hv
  have hM' : (a ∩ G).card = 5 := by rw [inter_comm]; exact hGa
  exact R2 hC ha hG hM' (mem_inter.2 ⟨hpa, hpG⟩)

/-- Lemma T, properties of a witness. -/
theorem T_props {a b G W : Finset V} (ha : a ∈ H) (hb : b ∈ H) (hG : G ∈ H) (hW : W ∈ H)
    (hM : (a ∩ b).card = 5) {v : V} (hv : G ∩ (a ∩ b) = {v}) {p : V} (hpb : p ∉ b)
    (hWp : W ∩ (a ∩ G) = {p}) :
    W ∩ (b \ a) ⊆ G ∩ (b \ a) ∧
    (∀ w, W ∩ (a ∩ b) = {w} →
      w ≠ v ∧ W ∩ (b \ a) = G ∩ (b \ a) ∧ W ∩ G ∩ (a \ b) = {p}) := by
  have hvab : v ∈ a ∩ b := by
    have : v ∈ G ∩ (a ∩ b) := by rw [hv]; exact mem_singleton_self v
    exact (mem_inter.1 this).2
  have hvG : v ∈ G := by
    have : v ∈ G ∩ (a ∩ b) := by rw [hv]; exact mem_singleton_self v
    exact (mem_inter.1 this).1
  have hpW : p ∈ W ∧ p ∈ a ∧ p ∈ G := by
    have : p ∈ W ∩ (a ∩ G) := by rw [hWp]; exact mem_singleton_self p
    simp only [mem_inter] at this; exact this
  obtain ⟨hGa, -, -⟩ := single_card hC ha hb hG hM hv
  have hM' : (a ∩ G).card = 5 := by rw [inter_comm]; exact hGa
  have hbM' : b ∩ (a ∩ G) = {v} := by
    ext z; constructor
    · intro hz
      have : z ∈ G ∩ (a ∩ b) := by simp only [mem_inter] at hz ⊢; tauto
      rw [hv] at this; exact this
    · intro hz; rw [mem_singleton] at hz; subst hz
      simp only [mem_inter] at hvab ⊢; exact ⟨hvab.2, hvab.1, hvG⟩
  have hvp : v ≠ p := by
    intro h; apply hpb; rw [← h]; exact (mem_inter.1 hvab).2
  have hdis := (R3 hC ha hG hb hW hM' hbM' hWp hvp).2.2.2.2.1
  have hsub : W ∩ (b \ a) ⊆ G ∩ (b \ a) := by
    intro z hz
    simp only [mem_inter, mem_sdiff] at hz ⊢
    refine ⟨?_, hz.2⟩
    by_contra hzG
    exact Finset.disjoint_left.1 hdis (by simp [hz.2.1, hz.2.2, hzG] : z ∈ b \ (a ∪ G))
      (by simp [hz.1, hz.2.2, hzG])
  refine ⟨hsub, fun w hw => ?_⟩
  have hvW : v ∉ W := by
    intro hvW
    have : v ∈ W ∩ (a ∩ G) := by simp [hvW, (mem_inter.1 hvab).1, hvG]
    rw [hWp, mem_singleton] at this
    exact hvp this
  have hwW : w ∈ W := by
    have : w ∈ W ∩ (a ∩ b) := by rw [hw]; exact mem_singleton_self w
    exact (mem_inter.1 this).1
  have hwv : w ≠ v := fun h => hvW (h ▸ hwW)
  refine ⟨hwv, ?_, ?_⟩
  · have r1 := card_split_right G a b
    have r2 := card_split_right W a b
    obtain ⟨-, hGb, -⟩ := single_card hC ha hb hG hM hv
    obtain ⟨-, hWb, -⟩ := single_card hC ha hb hW hM hw
    rw [hv, card_singleton] at r1
    rw [hw, card_singleton] at r2
    exact eq_of_subset_of_card_le hsub (by omega)
  · ext z; constructor
    · intro hz
      simp only [mem_inter, mem_sdiff] at hz
      have : z ∈ W ∩ (a ∩ G) := by simp [hz.1.1, hz.2.1, hz.1.2]
      rw [hWp] at this; exact this
    · intro hz; rw [mem_singleton] at hz; subst hz
      simp [hpW.1, hpW.2.1, hpW.2.2, hpb]

end Counter

end Erdos616R21

/-! ## Lemma A, second half: the minimum pairwise intersection is exactly 5 -/

namespace Erdos616R21
open Finset
variable {V : Type*} [DecidableEq V]

/-- Any set of size `m ≥ 4` is covered by at most `⌈m/4⌉` of its 4-subsets. -/
theorem exists_cover4 : ∀ (m : ℕ) (M : Finset V), M.card = m → 4 ≤ m → ∃ 𝓑 : Finset (Finset V),
    (∀ B ∈ 𝓑, B ⊆ M ∧ B.card = 4) ∧ (∀ x ∈ M, ∃ B ∈ 𝓑, x ∈ B) ∧
    𝓑.card * 4 ≤ m + 3 ∧ 𝓑.Nonempty := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro M hm h4
    by_cases h4' : m = 4
    · refine ⟨{M}, by simp [hm, h4'], fun x hx => ⟨M, by simp, hx⟩, by simp only [card_singleton]; omega, by simp⟩
    obtain ⟨B1, hB1M, hB1⟩ := exists_subset_card_eq (s := M) (n := 4) (by omega)
    have hsd := card_sdiff_add_card_inter M B1
    rw [inter_eq_right.2 hB1M, hB1, hm] at hsd
    by_cases hle : m ≤ 8
    · obtain ⟨B2, hRB2, hB2M, hB2⟩ :=
        exists_subsuperset_card_eq (sdiff_subset : M \ B1 ⊆ M) (n := 4) (by omega) (by omega)
      refine ⟨{B1, B2}, ?_, ?_, ?_, by simp⟩
      · intro B hB
        simp only [mem_insert, mem_singleton] at hB
        rcases hB with rfl | rfl
        · exact ⟨hB1M, hB1⟩
        · exact ⟨hB2M, hB2⟩
      · intro x hx
        by_cases hxB1 : x ∈ B1
        · exact ⟨B1, by simp, hxB1⟩
        · exact ⟨B2, by simp, hRB2 (mem_sdiff.2 ⟨hx, hxB1⟩)⟩
      · have := card_insert_le B1 {B2}
        rw [card_singleton] at this
        omega
    · obtain ⟨𝓑', h1, h2, h3, -⟩ := ih (m - 4) (by omega) (M \ B1) (by omega) (by omega)
      refine ⟨insert B1 𝓑', ?_, ?_, ?_, by simp⟩
      · intro B hB
        rw [mem_insert] at hB
        rcases hB with rfl | hB
        · exact ⟨hB1M, hB1⟩
        · exact ⟨(h1 B hB).1.trans sdiff_subset, (h1 B hB).2⟩
      · intro x hx
        by_cases hxB1 : x ∈ B1
        · exact ⟨B1, by simp, hxB1⟩
        · obtain ⟨B, hB, hxB⟩ := h2 x (mem_sdiff.2 ⟨hx, hxB1⟩)
          exact ⟨B, mem_insert_of_mem hB, hxB⟩
      · have := card_insert_le B1 𝓑'
        omega

theorem arithA_dec : ∀ m < 18, ∀ k < 6, 6 ≤ m → k * 4 ≤ m + 3 → 42 - m + k * (17 - m) ≤ 60 := by
  decide

theorem arithA : ∀ m k : ℕ, 6 ≤ m → m ≤ 17 → k * 4 ≤ m + 3 → 42 - m + k * (17 - m) ≤ 60 :=
  fun m k h1 h2 h3 => arithA_dec m (by omega) k (by omega) h1 h3

section
variable {H : Finset (Finset V)} (hC : Counter H)
include hC

theorem exists_two_edges : ∃ a ∈ H, ∃ b ∈ H, a ≠ b := by
  obtain ⟨a, ha, -⟩ := hC.avoid ∅ (by simp)
  obtain ⟨B, hBa, hB⟩ := exists_subset_card_eq (s := a) (n := 4) (by rw [hC.unif a ha]; omega)
  obtain ⟨b, hb, hdis⟩ := hC.avoid B (by omega)
  refine ⟨a, ha, b, hb, fun hab => ?_⟩
  subst hab
  obtain ⟨x, hx⟩ := card_pos.1 (by omega : 0 < B.card)
  exact Finset.disjoint_left.1 hdis (hBa hx) hx

/-- Lemma A: some pair of distinct edges meets in exactly 5 vertices. -/
theorem lemmaA : ∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ (a ∩ b).card = 5 := by
  obtain ⟨a0, ha0, b0, hb0, hne⟩ := exists_two_edges hC
  have hoff : (H.offDiag).Nonempty := ⟨(a0, b0), mem_offDiag.2 ⟨ha0, hb0, hne⟩⟩
  obtain ⟨⟨a, b⟩, hab, hmin⟩ := exists_min_image H.offDiag (fun p => (p.1 ∩ p.2).card) hoff
  rw [mem_offDiag] at hab
  dsimp only at hab hmin
  obtain ⟨ha, hb, hneab⟩ := hab
  refine ⟨a, ha, b, hb, hneab, ?_⟩
  have h5 := inter_ge5 hC ha hb
  by_contra hm5
  have minle : ∀ {c d : Finset V}, c ∈ H → d ∈ H → c ≠ d → (a ∩ b).card ≤ (c ∩ d).card :=
    fun hc hd hcd => hmin (_, _) (mem_offDiag.2 ⟨hc, hd, hcd⟩)
  obtain ⟨𝓑, hBsub, hBcov, hBcard, hBne⟩ := exists_cover4 _ (a ∩ b) rfl (by omega)
  have hav : ∀ B ∈ 𝓑, ∃ e ∈ H, Disjoint e B := fun B hB => hC.avoid B (by rw [(hBsub B hB).2])
  choose! f hfH hfdis using hav
  -- per-block bound
  have block : ∀ B ∈ 𝓑, (f B \ (a ∪ b)).card + (a ∩ b).card + 4 ≤ 21 := by
    intro B hB
    obtain ⟨hBM, hB4⟩ := hBsub B hB
    obtain ⟨x, hxB⟩ := card_pos.1 (by omega : 0 < B.card)
    have hxa : x ∈ a := (mem_inter.1 (hBM hxB)).1
    have hxb : x ∈ b := (mem_inter.1 (hBM hxB)).2
    have hxf : x ∉ f B := fun h => Finset.disjoint_left.1 (hfdis B hB) h hxB
    have hfa : f B ≠ a := fun h => hxf (h ▸ hxa)
    have hfb : f B ≠ b := fun h => hxf (h ▸ hxb)
    have m1 := minle (hfH B hB) ha hfa
    have m2 := minle (hfH B hB) hb hfb
    have hsubM : f B ∩ (a ∩ b) ⊆ (a ∩ b) \ B := by
      intro z hz
      rw [mem_inter] at hz
      exact mem_sdiff.2 ⟨hz.2, fun hzB => Finset.disjoint_left.1 (hfdis B hB) hz.1 hzB⟩
    have hc1 := card_le_card hsubM
    have hc2 := card_sdiff_add_card_inter (a ∩ b) B
    rw [inter_eq_right.2 hBM, hB4] at hc2
    have s1 := card_sdiff_eq (f B) (a ∪ b)
    rw [hC.unif _ (hfH B hB)] at s1
    have c1 := card_split (f B) a b
    have l1 := card_split_left (f B) a b
    have r1 := card_split_right (f B) a b
    omega
  -- the family {a, b} ∪ f(𝓑)
  set F : Finset (Finset V) := insert a (insert b (𝓑.image f)) with hFdef
  have hFH : F ⊆ H := by
    intro e he
    simp only [hFdef, mem_insert, mem_image] at he
    rcases he with rfl | rfl | ⟨B, hB, rfl⟩
    · exact ha
    · exact hb
    · exact hfH B hB
  have hspan := (propL_iff_span H 60).1 hC.propL F hFH (by simp [hFdef]) (by
    intro x
    by_contra hx; push Not at hx
    have hxa := hx a (by simp [hFdef])
    have hxb := hx b (by simp [hFdef])
    obtain ⟨B, hB, hxB⟩ := hBcov x (mem_inter.2 ⟨hxa, hxb⟩)
    have := hx (f B) (by simp only [hFdef, mem_insert, mem_image]; exact Or.inr (Or.inr ⟨B, hB, rfl⟩))
    exact Finset.disjoint_left.1 (hfdis B hB) this hxB)
  have hsub : F.biUnion id ⊆ (a ∪ b) ∪ 𝓑.biUnion (fun B => f B \ (a ∪ b)) := by
    intro z hz
    simp only [hFdef, mem_biUnion, mem_insert, mem_image, id] at hz
    obtain ⟨e, he, hze⟩ := hz
    rcases he with rfl | rfl | ⟨B, hB, rfl⟩
    · exact mem_union_left _ (mem_union_left _ hze)
    · exact mem_union_left _ (mem_union_right _ hze)
    · by_cases hz' : z ∈ a ∪ b
      · exact mem_union_left _ hz'
      · exact mem_union_right _ (mem_biUnion.2 ⟨B, hB, mem_sdiff.2 ⟨hze, hz'⟩⟩)
  have hc1 := card_le_card hsub
  have hc2 := card_union_le (a ∪ b) (𝓑.biUnion (fun B => f B \ (a ∪ b)))
  have hm17 : (a ∩ b).card ≤ 17 := by
    obtain ⟨B, hB⟩ := hBne
    have := block B hB; omega
  have hc4 := card_biUnion_le_mul 𝓑 (fun B => f B \ (a ∪ b)) (17 - (a ∩ b).card)
    (fun B hB => by have := block B hB; omega)
  have hab := card_union_add_card_inter a b
  rw [hC.unif a ha, hC.unif b hb] at hab
  have := arithA (a ∩ b).card 𝓑.card (by omega) hm17 hBcard
  omega

end

end Erdos616R21

/-! ## Lemma CP' (W7-5) — the 49-triple inequality used by W7-I and the Case-N encodings -/

namespace Erdos616R21
open Finset
variable {V : Type*} [DecidableEq V]

section
variable {H : Finset (Finset V)} (hC : Counter H)
include hC

/-- W7-5 (CP'): if `Q, X1, X2` pairwise meet in exactly 5 and `Q ∩ X1 ∩ X2 = {p}`, then every
edge `F` with `p ∉ F` satisfies `|F∩Q ∖ (X1∪X2)| ≤ |F∩(X1∩X2)∖Q| − 1`. -/
theorem CP {Q X1 X2 F : Finset V} (hQ : Q ∈ H) (hX1 : X1 ∈ H) (hX2 : X2 ∈ H) (hF : F ∈ H)
    (h1 : (Q ∩ X1).card = 5) (h2 : (Q ∩ X2).card = 5) (h12 : (X1 ∩ X2).card = 5) {p : V}
    (hp : Q ∩ X1 ∩ X2 = {p}) (hpF : p ∉ F) :
    ((F ∩ Q) \ (X1 ∪ X2)).card + 1 ≤ (F ∩ ((X1 ∩ X2) \ Q)).card := by
  have key : ∀ z, z ∈ Q → z ∈ X1 → z ∈ X2 → z = p := by
    intro z hzQ hz1 hz2
    have : z ∈ Q ∩ X1 ∩ X2 := by simp [hzQ, hz1, hz2]
    rw [hp, mem_singleton] at this; exact this
  have hL := L4 hC hQ hX1 hX2 hF (fun z hzQ hz1 hz2 hzF => hpF (key z hzQ hz1 hz2 ▸ hzF))
  -- |Q ∪ X1 ∪ X2| = 49
  have ha := card_union_add_card_inter Q X1
  have hb := card_union_add_card_inter (Q ∪ X1) X2
  have e1 : (Q ∪ X1) ∩ X2 = (Q ∩ X2) ∪ (X1 ∩ X2) := by ext; simp <;> tauto
  have hc := card_union_add_card_inter (Q ∩ X2) (X1 ∩ X2)
  have e2 : (Q ∩ X2) ∩ (X1 ∩ X2) = Q ∩ X1 ∩ X2 := by ext; simp <;> tauto
  rw [e1] at hb
  rw [e2, hp, card_singleton] at hc
  rw [hC.unif Q hQ, hC.unif X1 hX1] at ha
  rw [hC.unif X2 hX2] at hb
  -- union with F
  have hU : (Q ∪ X1 ∪ X2 ∪ F).card ≤ (Q ∪ X1 ∪ X2).card + (F \ (Q ∪ X1 ∪ X2)).card := by
    have : Q ∪ X1 ∪ X2 ∪ F = (Q ∪ X1 ∪ X2) ∪ (F \ (Q ∪ X1 ∪ X2)) := by ext; simp <;> tauto
    rw [this]; exact card_union_le _ _
  have s1 := card_sdiff_eq F (Q ∪ X1 ∪ X2)
  rw [hC.unif F hF] at s1
  -- F ∩ U contains two disjoint pieces
  have hsub : ((F ∩ Q) \ (X1 ∪ X2)) ∪ (F ∩ (X1 ∪ X2)) ⊆ F ∩ (Q ∪ X1 ∪ X2) := by
    intro z hz; simp only [mem_union, mem_inter, mem_sdiff] at hz ⊢; tauto
  have hdis : ((F ∩ Q) \ (X1 ∪ X2)) ∩ (F ∩ (X1 ∪ X2)) = ∅ := by
    ext z; simp only [mem_inter, mem_sdiff, mem_union, Finset.notMem_empty, iff_false]; tauto
  have hd := card_union_add_card_inter ((F ∩ Q) \ (X1 ∪ X2)) (F ∩ (X1 ∪ X2))
  rw [hdis, card_empty] at hd
  have hcs := card_le_card hsub
  have c1 := card_split F X1 X2
  have l1 := card_split_left F X1 X2
  have r1 := card_split_right F X1 X2
  have i1 := inter_ge5 hC hF hX1
  have i2 := inter_ge5 hC hF hX2
  have hz : F ∩ (X1 ∩ X2) ⊆ F ∩ ((X1 ∩ X2) \ Q) := by
    intro z hz
    simp only [mem_inter, mem_sdiff] at hz ⊢
    refine ⟨hz.1, ⟨hz.2.1, hz.2.2⟩, fun hzQ => hpF ?_⟩
    exact key z hzQ hz.2.1 hz.2.2 ▸ hz.1
  have hzc := card_le_card hz
  omega

end

end Erdos616R21

/-! ## Cross-type classes (N.0 / N8.0 input) and the rigid base configuration -/

namespace Erdos616R21
open Finset
variable {V : Type*} [DecidableEq V]

section
variable {H : Finset (Finset V)} (hC : Counter H)
include hC

/-- Cross-type singles `G` (type `v`), `G'` (type `w ≠ v`) of a 5-pair: with
`α = |A_G ∩ A_G'|`, `γ = |C_G ∩ C_G'|` we have `1 ≤ α, γ ≤ 4`, `α + γ ≥ 5` and `|G ∩ G'| = α + γ`. -/
theorem cross_class {a b G G' : Finset V} (ha : a ∈ H) (hb : b ∈ H) (hG : G ∈ H) (hG' : G' ∈ H)
    (hM : (a ∩ b).card = 5) {v w : V} (hv : G ∩ (a ∩ b) = {v}) (hw : G' ∩ (a ∩ b) = {w})
    (hvw : v ≠ w) :
    1 ≤ (G ∩ G' ∩ (a \ b)).card ∧ (G ∩ G' ∩ (a \ b)).card ≤ 4 ∧
    1 ≤ (G ∩ G' ∩ (b \ a)).card ∧ (G ∩ G' ∩ (b \ a)).card ≤ 4 ∧
    5 ≤ (G ∩ G' ∩ (a \ b)).card + (G ∩ G' ∩ (b \ a)).card ∧
    (G ∩ G').card = (G ∩ G' ∩ (a \ b)).card + (G ∩ G' ∩ (b \ a)).card := by
  obtain ⟨hGa, hGb, -⟩ := single_card hC ha hb hG hM hv
  have l1 := card_split_left G a b
  have r1 := card_split_right G a b
  rw [hv, card_singleton] at l1 r1
  have hA : G ∩ G' ∩ (a \ b) ⊆ G ∩ (a \ b) := by
    intro z hz; simp only [mem_inter, mem_sdiff] at hz ⊢; tauto
  have hCc : G ∩ G' ∩ (b \ a) ⊆ G ∩ (b \ a) := by
    intro z hz; simp only [mem_inter, mem_sdiff] at hz ⊢; tauto
  have cA := card_le_card hA
  have cC := card_le_card hCc
  obtain ⟨p, hpG, hpG', hpa, hpb⟩ := S_a_A hC ha hb hG hG' hv hw hvw
  obtain ⟨q, hqG, hqG', hqb, hqa⟩ := S_a_C hC ha hb hG hG' hv hw hvw
  have pA : 1 ≤ (G ∩ G' ∩ (a \ b)).card := card_pos.2 ⟨p, by simp [hpG, hpG', hpa, hpb]⟩
  have pC : 1 ≤ (G ∩ G' ∩ (b \ a)).card := card_pos.2 ⟨q, by simp [hqG, hqG', hqa, hqb]⟩
  have hS := S_b hC ha hb hG hG' hM hv hw hvw
  -- |G ∩ G'| splits: no point in a ∩ b, none outside a ∪ b
  have hO := S_a_O hC ha hb hG hG' hM hv hw hvw
  have hsub : G ∩ G' ⊆ G ∩ G' ∩ (a ∪ b) := by
    intro z hz
    rw [mem_inter] at hz
    refine mem_inter.2 ⟨mem_inter.2 hz, ?_⟩
    by_contra hz'
    exact Finset.disjoint_left.1 hO (mem_sdiff.2 ⟨hz.1, hz'⟩) (mem_sdiff.2 ⟨hz.2, hz'⟩)
  have hM0 : G ∩ G' ∩ (a ∩ b) = ∅ := by
    ext z
    simp only [mem_inter, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hzG, hzG'⟩, hza, hzb⟩
    have h1 : z ∈ G ∩ (a ∩ b) := by simp [hza, hzb, hzG]
    have h2 : z ∈ G' ∩ (a ∩ b) := by simp [hza, hzb, hzG']
    rw [hv, mem_singleton] at h1
    rw [hw, mem_singleton] at h2
    exact hvw (h1 ▸ h2)
  have hs := card_split (G ∩ G') a b
  rw [hM0, card_empty] at hs
  have heq : G ∩ G' ∩ (a ∪ b) = G ∩ G' := subset_antisymm inter_subset_left hsub
  rw [heq] at hs
  refine ⟨pA, by omega, pC, by omega, hS, by omega⟩

/-- N.0: for any 5-pair and cross-type singles, the 4-family `{a, b, G, G'}` spans exactly 61. -/
theorem K4_span {a b G G' : Finset V} (ha : a ∈ H) (hb : b ∈ H) (hG : G ∈ H) (hG' : G' ∈ H)
    (hM : (a ∩ b).card = 5) {v w : V} (hv : G ∩ (a ∩ b) = {v}) (hw : G' ∩ (a ∩ b) = {w})
    (hvw : v ≠ w) : (a ∪ b ∪ G ∪ G').card = 61 := by
  obtain ⟨-, -, -, -, hO, h12, h12'⟩ := R3 hC ha hb hG hG' hM hv hw hvw
  have hab := card_union_add_card_inter a b
  rw [hC.unif a ha, hC.unif b hb] at hab
  have e : a ∪ b ∪ G ∪ G' = (a ∪ b) ∪ ((G \ (a ∪ b)) ∪ (G' \ (a ∪ b))) := by ext; simp <;> tauto
  have h1 := card_union_add_card_inter (G \ (a ∪ b)) (G' \ (a ∪ b))
  rw [disjoint_iff_inter_eq_empty.1 hO, card_empty] at h1
  have hd : Disjoint (a ∪ b) ((G \ (a ∪ b)) ∪ (G' \ (a ∪ b))) := by
    rw [Finset.disjoint_left]; intro z hz hz'
    simp only [mem_union, mem_sdiff] at hz'
    rcases hz' with h | h <;> exact h.2 (mem_union.1 hz)
  have h2 := card_union_add_card_inter (a ∪ b) ((G \ (a ∪ b)) ∪ (G' \ (a ∪ b)))
  rw [disjoint_iff_inter_eq_empty.1 hd, card_empty] at h2
  rw [e]; omega

/-- The rigid base configuration (end of upper.md §1): a counterexample contains a 5-pair
`(a, b)` and, for every `x ∈ a ∩ b`, a single of type `x` meeting `a` and `b` in exactly 5 and
with exactly 12 points outside `a ∪ b`; singles of different types have disjoint outside parts. -/
theorem rigid_base : ∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ (a ∩ b).card = 5 ∧
    (∀ x ∈ a ∩ b, ∃ F ∈ H, F ∩ (a ∩ b) = {x} ∧ (F ∩ a).card = 5 ∧ (F ∩ b).card = 5 ∧
      (F \ (a ∪ b)).card = 12) ∧
    (∀ F ∈ H, ∀ F' ∈ H, ∀ x y : V, F ∩ (a ∩ b) = {x} → F' ∩ (a ∩ b) = {y} → x ≠ y →
      Disjoint (F \ (a ∪ b)) (F' \ (a ∪ b))) := by
  obtain ⟨a, ha, b, hb, hab, hM⟩ := lemmaA hC
  refine ⟨a, ha, b, hb, hab, hM, fun x hx => ?_, fun F hF F' hF' x y hx hy hxy =>
    (R3 hC ha hb hF hF' hM hx hy hxy).2.2.2.2.1⟩
  obtain ⟨F, hF, hFx⟩ := R2 hC ha hb hM hx
  exact ⟨F, hF, hFx, single_card hC ha hb hF hM hFx⟩

end

end Erdos616R21

/-! ## Lower bound: the EHT example H(21,10,7) gives `4 ≤ t(21)` -/

namespace Erdos616R21
open Finset

/-! ### Transport along an injection (to land on `Fin n`) -/

section transport
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

def mapFam (f : V ↪ W) (H : Finset (Finset V)) : Finset (Finset W) :=
  H.map ⟨Finset.map f, Finset.map_injective f⟩

theorem mem_mapFam (f : V ↪ W) (H : Finset (Finset V)) (e' : Finset W) :
    e' ∈ mapFam f H ↔ ∃ e ∈ H, e.map f = e' := by
  simp [mapFam]

theorem uniform_mapFam (f : V ↪ W) {H : Finset (Finset V)} {r : ℕ} (h : H.IsUniform r) :
    (mapFam f H).IsUniform r := by
  intro e' he'
  obtain ⟨e, he, rfl⟩ := (mem_mapFam f H e').1 he'
  rw [card_map]; exact h e he

theorem propL_mapFam (f : V ↪ W) {H : Finset (Finset V)} {v : ℕ} (h : PropL H v) :
    PropL (mapFam f H) v := by
  intro F' hF' hne hcard
  set F := H.filter (fun e => e.map f ∈ F') with hF
  have hFF' : F.map ⟨Finset.map f, Finset.map_injective f⟩ = F' := by
    ext e'
    simp only [hF, mem_map, mem_filter, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨e, ⟨_, he'⟩, rfl⟩; exact he'
    · intro he'
      obtain ⟨e, he, rfl⟩ := (mem_mapFam f H e').1 (hF' he')
      exact ⟨e, ⟨he, he'⟩, rfl⟩
  have hU : F'.biUnion id = (F.biUnion id).map f := by
    rw [← hFF']; ext y; simp only [mem_biUnion, mem_map, id, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, hy⟩
      obtain ⟨x, hx, rfl⟩ := mem_map.1 hy
      exact ⟨x, ⟨a, ha, hx⟩, rfl⟩
    · rintro ⟨x, ⟨a, ha, hx⟩, rfl⟩; exact ⟨_, ⟨a, ha, rfl⟩, mem_map_of_mem f hx⟩
  obtain ⟨x, hx⟩ := h F (filter_subset _ _)
    (by obtain ⟨e', he'⟩ := hne; rw [← hFF'] at he'; obtain ⟨e, he, -⟩ := mem_map.1 he'; exact ⟨e, he⟩)
    (by rw [hU, card_map] at hcard; exact hcard)
  refine ⟨f x, fun e' he' => ?_⟩
  rw [← hFF'] at he'
  obtain ⟨e, he, rfl⟩ := mem_map.1 he'
  exact mem_map_of_mem f (hx e he)

theorem not_transversal_mapFam (f : V ↪ W) {H : Finset (Finset V)} {k : ℕ}
    (h : ¬ (H : Set (Finset V)).HasFiniteTransversal k) :
    ¬ ((mapFam f H : Finset (Finset W)) : Set (Finset W)).HasFiniteTransversal k := by
  rintro ⟨S', hS', hhit⟩
  apply h
  refine ⟨S'.preimage f (f.injective.injOn), ?_, fun e he => ?_⟩
  · refine le_trans (card_le_card_of_injOn f (by intro a ha; exact mem_preimage.1 ha) (f.injective.injOn)) hS'
  · have he' : e.map f ∈ mapFam f H := (mem_mapFam f H _).2 ⟨e, by exact_mod_cast he, rfl⟩
    obtain ⟨y, hyS, hye⟩ := hhit _ (by exact_mod_cast he')
    obtain ⟨x, hxe, rfl⟩ := mem_map.1 hye
    exact ⟨x, mem_preimage.2 hyS, hxe⟩

end transport

/-! ### The example -/

abbrev V0 := Fin 10 ⊕ (Finset (Fin 10) × Fin 14)

def edge (T : Finset (Fin 10)) : Finset V0 :=
  T.image Sum.inl ∪ (univ : Finset (Fin 14)).image (fun i => Sum.inr (T, i))

@[simp] theorem inl_mem_edge (T : Finset (Fin 10)) (c : Fin 10) :
    (Sum.inl c : V0) ∈ edge T ↔ c ∈ T := by
  simp [edge]

@[simp] theorem inr_mem_edge (T T' : Finset (Fin 10)) (i : Fin 14) :
    (Sum.inr (T', i) : V0) ∈ edge T ↔ T' = T := by
  simp only [edge, mem_union, mem_image, mem_univ, true_and]
  constructor
  · rintro (⟨a, -, h⟩ | ⟨j, h⟩)
    · exact absurd h Sum.inl_ne_inr
    · simp only [Sum.inr.injEq, Prod.mk.injEq] at h; exact h.1.symm
  · rintro rfl; exact Or.inr ⟨i, rfl⟩

theorem card_edge (T : Finset (Fin 10)) : (edge T).card = T.card + 14 := by
  have h := card_union_add_card_inter (T.image (Sum.inl : Fin 10 → V0))
    ((univ : Finset (Fin 14)).image (fun i => (Sum.inr (T, i) : V0)))
  have h0 : T.image (Sum.inl : Fin 10 → V0) ∩
      (univ : Finset (Fin 14)).image (fun i => (Sum.inr (T, i) : V0)) = ∅ := by
    ext x; rcases x with c | ⟨T', i⟩ <;> simp
  rw [h0, card_empty, card_image_of_injective _ Sum.inl_injective,
    card_image_of_injective _ (fun i j hij => by simpa using hij)] at h
  simpa [edge] using h

def HL : Finset (Finset V0) := (powersetCard 7 (univ : Finset (Fin 10))).image edge

theorem mem_HL {e : Finset V0} : e ∈ HL ↔ ∃ T : Finset (Fin 10), T.card = 7 ∧ edge T = e := by
  simp [HL, mem_powersetCard]

theorem HL_uniform : HL.IsUniform 21 := by
  intro e he
  obtain ⟨T, hT, rfl⟩ := mem_HL.1 he
  rw [card_edge, hT]

theorem HL_not_transversal3 : ¬ (HL : Set (Finset V0)).HasFiniteTransversal 3 := by
  rintro ⟨S, hS, hhit⟩
  let g : V0 → Fin 10 := fun x => match x with
    | Sum.inl c => c
    | Sum.inr (T, _) => if h : T.Nonempty then T.min' h else 0
  set Z := S.image g
  have hZ : Z.card ≤ 3 := le_trans card_image_le hS
  have hZc : 7 ≤ Zᶜ.card := by rw [card_compl, Fintype.card_fin]; omega
  obtain ⟨T, hTZ, hT⟩ := exists_subset_card_eq hZc
  obtain ⟨x, hxS, hxe⟩ := hhit (edge T) (by
    show edge T ∈ (HL : Set (Finset V0)); exact_mod_cast mem_HL.2 ⟨T, hT, rfl⟩)
  have hgZ : g x ∈ Z := mem_image_of_mem g hxS
  rcases x with c | ⟨T', i⟩
  · rw [inl_mem_edge] at hxe
    exact (mem_compl.1 (hTZ hxe)) hgZ
  · rw [inr_mem_edge] at hxe
    subst hxe
    have hne : T'.Nonempty := card_pos.1 (by omega)
    have : g (Sum.inr (T', i)) = T'.min' hne := by simp [g, hne]
    rw [this] at hgZ
    exact (mem_compl.1 (hTZ (min'_mem T' hne))) hgZ

theorem HL_propL : PropL HL 60 := by
  intro F hF hne hcard
  -- every member of F is an edge
  have hFe : ∀ e ∈ F, ∃ T : Finset (Fin 10), T.card = 7 ∧ edge T = e := fun e he => mem_HL.1 (hF he)
  -- Step 1: at most three edges
  have hF3 : F.card ≤ 3 := by
    by_contra h4
    push Not at h4
    let pr : Finset V0 → Finset V0 := fun e => e.filter (fun x => x.isRight)
    have hpr : ∀ e ∈ F, (pr e).card = 14 := by
      intro e he
      obtain ⟨T, -, rfl⟩ := hFe e he
      have : pr (edge T) = (univ : Finset (Fin 14)).image (fun i => (Sum.inr (T, i) : V0)) := by
        ext x; rcases x with c | ⟨T', i⟩
        · simp [pr]
        · simp only [pr, mem_filter, inr_mem_edge, Sum.isRight_inr, and_true, mem_image, mem_univ,
            true_and, Sum.inr.injEq, Prod.mk.injEq]
          constructor
          · rintro rfl; exact ⟨i, rfl, rfl⟩
          · rintro ⟨j, h1, -⟩; exact h1.symm
      rw [this, card_image_of_injective _ (fun i j hij => by simpa using hij)]
      simp
    have hdis : (F : Set (Finset V0)).PairwiseDisjoint pr := by
      intro e he e' he' hee'
      obtain ⟨T, -, rfl⟩ := hFe e he
      obtain ⟨T', -, rfl⟩ := hFe e' he'
      rw [Function.onFun, Finset.disjoint_left]
      intro x hx hx'
      simp only [pr, mem_filter] at hx hx'
      rcases x with c | ⟨T'', i⟩
      · simp at hx
      · rw [inr_mem_edge] at hx hx'
        exact hee' (by rw [← hx.1, ← hx'.1])
    have hP : (F.biUnion pr).card = F.card * 14 := by
      rw [card_biUnion hdis, sum_congr rfl hpr]; simp [mul_comm]
    obtain ⟨e0, he0⟩ := hne
    obtain ⟨T0, hT0, rfl⟩ := hFe _ he0
    set core := (edge T0).filter (fun x => x.isLeft)
    have hcore : core.card = 7 := by
      have : core = T0.image Sum.inl := by
        ext x; rcases x with c | ⟨T', i⟩ <;> simp [core]
      rw [this, card_image_of_injective _ Sum.inl_injective, hT0]
    have hdc : Disjoint (F.biUnion pr) core := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [mem_biUnion, pr, mem_filter] at hx
      simp only [core, mem_filter] at hx'
      obtain ⟨-, -, -, h1⟩ := hx
      rcases x with c | ⟨T', i⟩ <;> simp_all
    have hsub : F.biUnion pr ∪ core ⊆ F.biUnion id := by
      intro x hx
      rcases mem_union.1 hx with hx | hx
      · obtain ⟨e, he, hxe⟩ := mem_biUnion.1 hx
        exact mem_biUnion.2 ⟨e, he, (mem_filter.1 hxe).1⟩
      · exact mem_biUnion.2 ⟨_, he0, (mem_filter.1 hx).1⟩
    have := card_le_card hsub
    have hu := card_union_add_card_inter (F.biUnion pr) core
    rw [disjoint_iff_inter_eq_empty.1 hdc, card_empty] at hu
    omega
  -- Step 2: three 7-subsets of a 10-set share a point
  let cm : Finset V0 → Finset (Fin 10) := fun e => univ.filter (fun c => (Sum.inl c : V0) ∉ e)
  have hcm : ∀ e ∈ F, (cm e).card = 3 := by
    intro e he
    obtain ⟨T, hT, rfl⟩ := hFe e he
    have : cm (edge T) = Tᶜ := by ext c; simp [cm]
    rw [this, card_compl, Fintype.card_fin, hT]
  have hK : (F.biUnion cm).card ≤ 9 := by
    have := card_biUnion_le_mul F cm 3 (fun e he => (hcm e he).le)
    omega
  obtain ⟨c, hc⟩ : ∃ c, c ∉ F.biUnion cm := by
    by_contra hall; push Not at hall
    have : F.biUnion cm = univ := eq_univ_of_forall hall
    rw [this, card_univ, Fintype.card_fin] at hK; omega
  refine ⟨Sum.inl c, fun e he => ?_⟩
  by_contra hce
  exact hc (mem_biUnion.2 ⟨e, he, by simp [cm, hce]⟩)

/-- **Lower bound, formal**: `4 ≤ localTransversalBound 21 60 1`. -/
theorem four_le : 4 ≤ Hypergraph.localTransversalBound 21 60 1 := by
  let f : V0 ↪ Fin (Fintype.card V0) := (Fintype.equivFin V0).toEmbedding
  exact four_le_of _ (mapFam f HL) (uniform_mapFam f HL_uniform) (propL_mapFam f HL_propL)
    (not_transversal_mapFam f HL_not_transversal3)

/-- Conversely, the statement rules out every counterexample. -/
theorem noCounter_of_statement (h : Statement) (n : ℕ) (H : Finset (Finset (Fin n))) :
    ¬ Counter H := by
  intro hC
  have h5 : (5 : ℕ∞) ≤ Hypergraph.localTransversalBound 21 60 1 := by
    unfold Hypergraph.localTransversalBound
    refine le_iInf₂ fun b hb => ?_
    have hT := hb n H (fun e he => hC.unif e he) ((local_iff_propL H 60).2 hC.propL)
    have : 5 ≤ b := by
      by_contra hlt
      obtain ⟨S, hS, hSe⟩ := hT
      obtain ⟨e, he, hdis⟩ := hC.avoid S (by omega)
      obtain ⟨v, hvS, hve⟩ := hSe e (by exact_mod_cast he)
      exact Finset.disjoint_left.1 hdis hve hvS
    exact_mod_cast this
  unfold Statement at h
  rw [h] at h5
  have : (5 : ℕ) ≤ 4 := by exact_mod_cast h5
  omega

/-- The r = 21 statement is now equivalent to the nonexistence of a counterexample. -/
theorem statement_of_noCounter (hub : ∀ (n : ℕ) (H : Finset (Finset (Fin n))), ¬ Counter H) :
    Statement :=
  le_antisymm (le_four_of_noCounter hub) four_le

/-- **Main reduction (fully formal).** The formal-conjectures statement at r = 21 is equivalent to
"no 21-uniform family on any `Fin n` has property L_60 and τ ≥ 5". -/
theorem erdos_616_r21_iff :
    Hypergraph.localTransversalBound 21 (3 * 21 - 3) 1 = 4 ↔
      ∀ (n : ℕ) (H : Finset (Finset (Fin n))), ¬ Counter H :=
  ⟨noCounter_of_statement, statement_of_noCounter⟩

end Erdos616R21
