import Erdos616Checkers.G14Check
/-!
# G14 glue (core Lean only): an abstract trace model satisfies every CNF accepted by `checkCNF`.
-/
open Std.Sat

namespace G14

/-- Abstract trace model: `occ t` = "some non-base edge has core trace `t`". The four fields are exactly what the
Mathlib side must prove from a counterexample (`lt`: traces are 16-bit masks; `univ`: per-edge rules give an
admissible state; `cov`: τ ≥ 5 on needed core 4-sets; `conf`: pairwise rules). -/
structure Model where
  occ : Nat → Prop
  lt : ∀ t, occ t → t < 65536
  univ : ∀ t, occ t → (states t).isEmpty = false
  cov : ∀ B, neededB B = true → ∃ t, occ t ∧ t &&& B = 0
  conf : ∀ t t', occ t → occ t' → t ≠ t' → compatTr t t' = true

theorem Q4_all {p : Nat → Bool} : Q4.all p = true ↔ p 0 = true ∧ p 1 = true ∧ p 2 = true ∧ p 3 = true := by
  simp [Q4]

theorem range_aux {a l r : Nat} (h1 : l ≤ a) (h2 : a ≤ r) : ∃ i, i < r + 1 - l ∧ a = l + 1 * i :=
  ⟨a - l, by omega, by omega⟩

/-- an admissible state lies in the enumerated box -/
theorem mem_box_of_ok {b : Nat} {o : O4} (h : ok b o = true) : o ∈ box b := by
  unfold ok okBasic at h
  simp only [Bool.and_eq_true, Q4_all, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨-, hs⟩, x0, x1, x2, x3⟩, -⟩, -⟩, -⟩, -⟩ := h
  obtain ⟨a0, a1, a2, a3⟩ := o
  simp only [O4.get, O4.sum, xq] at hs x0 x1 x2 x3
  have e0 : Lo b 0 ≤ a0 := by unfold Lo; omega
  have e1 : Lo b 1 ≤ a1 := by unfold Lo; omega
  have e2 : Lo b 2 ≤ a2 := by unfold Lo; omega
  have e3 : Lo b 3 ≤ a3 := by unfold Lo; omega
  unfold box rngLH
  simp only [List.mem_flatMap, List.mem_map, List.mem_range']
  exact ⟨a0, range_aux (r := 21 - pc b - (Lo b 1 + Lo b 2 + Lo b 3)) e0 (by omega),
    a1, range_aux (r := 21 - pc b - (a0 + Lo b 2 + Lo b 3)) e1 (by omega),
    a2, range_aux (r := 21 - pc b - (a0 + a1 + Lo b 3)) e2 (by omega),
    a3, range_aux (r := 21 - pc b - (a0 + a1 + a2)) e3 (by omega), rfl⟩

theorem states_ne_of_ok {b : Nat} {o : O4} (h : ok b o = true) : (states b).isEmpty = false := by
  have hm : o ∈ states b := by unfold states; exact List.mem_filter.2 ⟨mem_box_of_ok h, h⟩
  cases hs : states b with
  | nil => rw [hs] at hm; cases hm
  | cons _ _ => rfl

theorem compatTr_of {b1 b2 : Nat} {o1 o2 : O4} (h1 : ok b1 o1 = true) (h2 : ok b2 o2 = true)
    (hf : feasible b1 o1 b2 o2 = true) : compatTr b1 b2 = true := by
  unfold compatTr compatSt
  rw [List.any_eq_true]
  refine ⟨o1, List.mem_filter.2 ⟨mem_box_of_ok h1, h1⟩, List.any_eq_true.2 ⟨o2, List.mem_filter.2 ⟨mem_box_of_ok h2, h2⟩, hf⟩⟩

open Classical in
/-- the induced assignment: atom `v` (DIMACS variable `v+1`) is true iff trace `T[v]` occurs -/
noncomputable def assign (M : Model) (v : Nat) : Bool := decide (M.occ T[v]!)

theorem assign_true {M : Model} {v : Nat} : assign M v = true ↔ M.occ T[v]! := by
  unfold assign; simp

theorem idx_of_occ (M : Model) (hu : univOK () = true) {t : Nat} (ht : M.occ t) :
    ∃ v, v < T.size ∧ T[v]! = t := by
  unfold univOK at hu
  have h := List.all_eq_true.1 hu t (List.mem_range.2 (M.lt t ht))
  rw [M.univ t ht, Bool.false_or] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨_, h.1, h.2⟩

theorem stArr_get {u : Nat} (hu : u < T.size) : (T.map states)[u]! = states T[u]! := by
  have hu' : u < (T.map states).size := by simpa using hu
  rw [getElem!_pos (T.map states) u hu', getElem!_pos T u hu, Array.getElem_map]

theorem compatV_eq {u v : Nat} (hu : u < T.size) (hv : v < T.size) :
    compatV (T.map states) u v = compatTr T[u]! T[v]! := by
  unfold compatV compatTr
  rw [stArr_get hu, stArr_get hv]

theorem covOK_sound (M : Model) (hu : univOK () = true) (lits : List (Nat × Bool))
    (h : covOK lits = true) : lits.any (fun (i, n) => assign M i == n) = true := by
  unfold covOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hpos, h⟩ := h
  split at h
  · rename_i B _
    rw [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hB, heq⟩ := h
    obtain ⟨t, ht, htB⟩ := M.cov B hB
    obtain ⟨v, hv, hTv⟩ := idx_of_occ M hu ht
    have hmem : v ∈ avoiders B := by
      unfold avoiders
      rw [List.mem_filter, List.mem_range, hTv, htB]
      exact ⟨hv, rfl⟩
    rw [← heq, List.mem_map] at hmem
    obtain ⟨⟨i, n⟩, hl, hl1⟩ := hmem
    have hl2 : n = true := List.all_eq_true.1 hpos _ hl
    simp only at hl1
    subst hl1 hl2
    refine List.any_eq_true.2 ⟨(i, true), hl, ?_⟩
    simp only [beq_iff_eq]
    rw [assign_true, hTv]; exact ht
  · exact absurd h (by simp)

theorem clauseOK_sound (M : Model) (hu : univOK () = true) (extra lits : List (Nat × Bool))
    (he : extra.any (fun (i, n) => assign M i == n) = true)
    (h : clauseOK (T.map states) extra lits = true) : lits.any (fun (i, n) => assign M i == n) = true := by
  unfold clauseOK at h
  split at h
  · rename_i u v
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨hu', hv'⟩, hne⟩, hc⟩ := h
    rw [compatV_eq hu' hv'] at hc
    cases h1 : assign M u
    · simp [h1]
    cases h2 : assign M v
    · simp [h2]
    have := M.conf _ _ (assign_true.1 h1) (assign_true.1 h2) hne
    rw [hc] at this
    exact absurd this (by simp)
  · rw [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · subst h; exact he
    · exact covOK_sound M hu lits h

/-- **Glue theorem.** A trace model satisfies every CNF accepted by `checkCNF` (given the extra clause holds). -/
theorem eval_of_check (M : Model) (hu : univOK () = true) (f : CNF Nat) (extra : List (Nat × Bool))
    (hc : checkCNF f extra = true) (he : extra.any (fun (i, n) => assign M i == n) = true) :
    f.eval (assign M) = true := by
  unfold checkCNF checkCNFWith at hc
  unfold CNF.eval
  rw [Array.all_eq_true] at hc ⊢
  intro i hi
  exact clauseOK_sound M hu extra _ he (hc i hi)

end G14
