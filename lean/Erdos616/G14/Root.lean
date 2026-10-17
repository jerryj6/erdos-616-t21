import Erdos616.G14.Glue
/-!
# G14 root split (core Lean only): B* = {w,g0,g1,g2}; its 70 avoiders in `T` are the 51 "dead" ones (refuted by
w14_certdead) and 19 alive ones, each mapped by a base automorphism `s` (a permutation of the 16 core labels preserving
every `P_q`, here inside m3 and a4 only) onto one of the 5 representatives.
-/
open Std.Sat
namespace G14

def Bstar : Nat := 114
def deadAtoms : List Nat := [10077, 10179, 10236, 10291, 11638, 11693, 11748, 11796, 11851, 11899, 11945, 12952, 13007, 13062, 13110, 13165, 13213, 13259, 14278, 14329, 14378, 14400, 14449, 14469, 16050, 16052, 16135, 16137, 16171, 16173, 16988, 16990, 17073, 17075, 17109, 17111, 17837, 17839, 17841, 17876, 17878, 17880, 17915, 17916, 17927, 17929, 17931, 17966, 17967, 17978, 17979]
def deadClause : List (Nat × Bool) := deadAtoms.map fun a => (a, true)
def reps : List Nat := [14968, 15116, 15954, 16054, 17917]
/-- (atom of an alive avoider, atom of its representative, relabelling `s` with `s[i]` = old label of new label `i`) -/
def rootData : List (Nat × Nat × List Nat) := [(14968, 14968, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
  (15042, 14968, [0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 10, 11, 12, 13, 14, 15]),
  (15080, 14968, [0, 1, 2, 3, 4, 5, 6, 8, 9, 7, 10, 11, 12, 13, 14, 15]),
  (15116, 15116, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
  (15954, 15954, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
  (16003, 15954, [0, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 11, 12, 13, 14, 15]),
  (16054, 16054, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
  (16088, 15954, [0, 1, 2, 3, 4, 5, 6, 9, 7, 8, 10, 11, 12, 13, 14, 15]),
  (16139, 16054, [0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 10, 11, 12, 13, 14, 15]),
  (16175, 16054, [0, 1, 2, 3, 4, 5, 6, 8, 9, 7, 10, 11, 12, 13, 14, 15]),
  (16892, 15954, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 12, 14, 15]),
  (16941, 15954, [0, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 11, 13, 12, 14, 15]),
  (16992, 16054, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 12, 14, 15]),
  (17026, 15954, [0, 1, 2, 3, 4, 5, 6, 9, 7, 8, 10, 11, 13, 12, 14, 15]),
  (17077, 16054, [0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 10, 11, 13, 12, 14, 15]),
  (17113, 16054, [0, 1, 2, 3, 4, 5, 6, 8, 9, 7, 10, 11, 13, 12, 14, 15]),
  (17917, 17917, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
  (17968, 17917, [0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 10, 11, 12, 13, 14, 15]),
  (17980, 17917, [0, 1, 2, 3, 4, 5, 6, 8, 9, 7, 10, 11, 12, 13, 14, 15])]

/-- relabelled trace: new bit `i` = old bit `s[i]` -/
def pull (s : List Nat) (t : Nat) : Nat :=
  (List.range 16).foldl (fun acc i => if t.testBit s[i]! then acc ||| 2 ^ i else acc) 0

/-- `s` is a permutation of `0..15` preserving every base edge -/
def validPerm (s : List Nat) : Bool :=
  s.length == 16 && s.all (· < 16) && s.Nodup &&
  Q4.all fun q => (List.range 16).all fun i => (Pm q).testBit s[i]! == (Pm q).testBit i

def rootOK : Bool :=
  neededB Bstar && rootData.all (fun e => validPerm e.2.2 && reps.contains e.2.1 && decide (e.2.1 < T.size)) &&
  (List.range T.size).all fun a => T[a]! &&& Bstar != 0 || deadAtoms.contains a ||
    rootData.any fun e => e.1 == a && pull e.2.2 T[a]! == T[e.2.1]!

/-- **Root split.** Given refutations of the five representative cases and of the dead-avoider clause (each a
model-level statement, discharged by the LRAT-checked CNFs), no family of trace models that is closed under
relabelling by valid permutations can exist. `M s` is the model of the base relabelled by `s`; `hpull` says a trace
occurring for the reference labelling `s0` occurs, relabelled, for every valid `s`. -/
theorem root_split (hu : univOK () = true) (hr : rootOK = true)
    (caseR : ∀ r ∈ reps, ∀ M : Model, M.occ T[r]! → False)
    (caseDead : ∀ M : Model, (deadClause.any fun (i, n) => assign M i == n) = true → False)
    (M : List Nat → Model) (s0 : List Nat)
    (hpull : ∀ s, validPerm s = true → ∀ t, (M s0).occ t → (M s).occ (pull s t)) : False := by
  unfold rootOK at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨hB, hdata⟩, hall⟩ := hr
  obtain ⟨t, ht, htB⟩ := (M s0).cov Bstar hB
  obtain ⟨v, hv, hTv⟩ := idx_of_occ (M s0) hu ht
  have h := List.all_eq_true.1 hall v (List.mem_range.2 hv)
  rw [hTv, htB] at h
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact absurd h (by decide)
  · apply caseDead (M s0)
    refine List.any_eq_true.2 ⟨(v, true), ?_, ?_⟩
    · unfold deadClause
      exact List.mem_map.2 ⟨v, List.elem_iff.1 h, rfl⟩
    · simp only [beq_iff_eq]
      rw [assign_true, hTv]; exact ht
  · obtain ⟨e, he, h1⟩ := List.any_eq_true.1 h
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨-, h2⟩ := h1
    have hd := List.all_eq_true.1 hdata e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
    obtain ⟨⟨hval, hrep⟩, -⟩ := hd
    have := hpull e.2.2 hval t ht
    rw [h2] at this
    exact caseR e.2.1 (List.elem_iff.1 hrep) (M e.2.2) this

end G14
