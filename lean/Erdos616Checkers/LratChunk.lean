import Erdos616Checkers.LratCheck
/-!
Chunked LRAT checking for proofs too large to embed in one Lean file.

All lemmas are RUP (drat-trim reports 0 RAT lemmas for every certificate here; the splitter refuses RAT hints).
Deletions are dropped (sound: keeping clauses only strengthens the formula used for RUP).
A certificate `F` with lemma blocks `L 0, …, L (k-1)` (the last block ends with the empty clause) is checked as
`G 0 = F`, `G (j+1) = G j ++ L j`, and for every `j`: every clause of `L j` is RUP w.r.t. `G j` plus the earlier
clauses of `L j`, using the hint lists of block `j`. Soundness of each RUP step is Lean core's verified
`State.entails_clause_of_checkRup`.
-/
open Std.Sat Std.Tactic.BVDecide.LRAT.Internal

namespace LratChunk

/-- check that each lemma of `ls` is RUP (with the matching hint list of `hs`) w.r.t. the state,
adding it to the state afterwards. -/
def checkRups : State → List (CNF.Clause Nat) → List (Array Nat) → Bool
  | _, [], [] => true
  | s, l :: ls, h :: hs => if s.checkRup l h then checkRups (s.add l) ls hs else false
  | _, _, _ => false

theorem checkRups_sound : ∀ (s : State) (ls : List (CNF.Clause Nat)) (hs : List (Array Nat)),
    checkRups s ls hs = true → ∀ a, CNF.Sat a s.toCNF → ∀ l ∈ ls, CNF.Clause.Sat a l
  | _, [], [], _ => by intro a _ l hl; cases hl
  | s, l :: ls, h :: hs, H => by
    intro a ha l' hl'
    unfold checkRups at H
    split at H
    · rename_i hc
      have e := State.entails_clause_of_checkRup hc
      have hsa : CNF.Sat a (s.add l).toCNF := State.entails_add_of_entails_clause e a ha
      cases hl' with
      | head => exact e a ha
      | tail _ hm => exact checkRups_sound (s.add l) ls hs H a hsa l' hm
    · cases H
  | _, [], _ :: _, H => by simp [checkRups] at H
  | _, _ :: _, [], H => by simp [checkRups] at H

theorem block_sound (G L : CNF Nat) (hs : List (Array Nat))
    (h : checkRups (State.ofCNF G) L.clauses.toList hs = true) :
    ∀ a, CNF.Sat a G → CNF.Sat a L := by
  intro a ha
  have ha' : CNF.Sat a (State.ofCNF G).toCNF := by rw [State.ofCNF_toCNF_eq]; exact ha
  apply CNF.sat_of_all_mem_sat
  intro c hc
  rw [CNF.Internal.mem_iff] at hc
  exact checkRups_sound _ _ _ h a ha' c (Array.mem_toList_iff.mpr hc)

/-- parse hint lists: one line per lemma, natural numbers separated by spaces. -/
def parseHints (s : String) : List (Array Nat) := Id.run do
  let b := s.toUTF8
  let n := b.size
  let mut i := 0
  let mut out : Array (Array Nat) := #[]
  let mut cur : Array Nat := #[]
  let mut v : Nat := 0
  let mut inNum := false
  while i < n do
    let c := b.get! i
    if c ≥ 48 && c ≤ 57 then
      v := v * 10 + (c - 48).toNat; inNum := true
    else
      if inNum then cur := cur.push v; v := 0; inNum := false
      if c == 10 then out := out.push cur; cur := #[]
    i := i + 1
  if inNum then cur := cur.push v
  if cur.size > 0 then out := out.push cur
  return out.toList

/-- hint lists from a file in LRAT syntax (`id 0 hints 0` per lemma), parsed by core's native LRAT parser
(faster than `parseHints`; hints are untrusted data either way). -/
def hintsOfLRAT (s : String) : List (Array Nat) :=
  (LratCheck.lratOf s).toList.filterMap fun
    | .addEmpty _ h => some h
    | .addRup _ _ h => some h
    | _ => none

/-- DIMACS parser built from core's (natively compiled) `String.splitOn` / `String.toInt?`; same conventions as
`LratCheck.parseDimacs` (var v ↦ atom v-1). Lines starting with `c`/`p` are skipped; unparsable tokens are skipped,
so every use is paired with an external round-trip check (`CNF.dimacs` output vs the original file). -/
def parseDimacsFast (s : String) : CNF Nat := Id.run do
  let mut clauses : Array (CNF.Clause Nat) := #[]
  let mut cur : CNF.Clause Nat := CNF.Clause.empty
  for line in s.splitOn "\n" do
    if line.startsWith "c" || line.startsWith "p" then continue
    for tok in line.splitOn " " do
      match tok.toInt? with
      | some v =>
        if v == 0 then
          clauses := clauses.push cur
          cur := CNF.Clause.empty
        else
          cur := cur.add (v.natAbs - 1) (decide (v > 0))
      | none => pure ()
  return ⟨clauses⟩

/-- `G F L j = F ++ L 0 ++ … ++ L (j-1)`. -/
def G (F : CNF Nat) (L : Nat → CNF Nat) : Nat → CNF Nat
  | 0 => F
  | j + 1 => G F L j ++ L j

theorem chain (F : CNF Nat) (L : Nat → CNF Nat) (k : Nat)
    (step : ∀ j, j < k → ∀ a, CNF.Sat a (G F L j) → CNF.Sat a (L j)) :
    ∀ a, CNF.Sat a F → CNF.Sat a (G F L k) := by
  intro a ha
  induction k with
  | zero => exact ha
  | succ k ih =>
    have hk := ih (fun j hj => step j (by omega))
    show CNF.Sat a (G F L k ++ L k)
    exact CNF.sat_append.mpr ⟨hk, step k (by omega) a hk⟩

def hasEmpty (f : CNF Nat) : Bool := f.clauses.any (fun c => c.atoms.size == 0)

theorem not_sat_of_hasEmpty (f : CNF Nat) (h : hasEmpty f = true) (a : Nat → Bool) : ¬ CNF.Sat a f := by
  intro hs
  unfold hasEmpty at h
  rw [Array.any_eq_true] at h
  obtain ⟨i, hi, hc⟩ := h
  have hsat : CNF.Clause.Sat a f.clauses[i] := by
    unfold CNF.Sat CNF.eval at hs
    rw [Array.all_eq_true] at hs
    exact hs i hi
  have hz : f.clauses[i].literals.length = 0 := by
    rw [CNF.Clause.length_literals]; simpa [CNF.Clause.size] using hc
  unfold CNF.Clause.Sat CNF.Clause.eval at hsat
  rw [List.length_eq_zero_iff] at hz
  rw [hz] at hsat
  simp at hsat

/-- final assembly: if every block is RUP-valid and the last block contains the empty clause, `F` is unsat. -/
theorem unsat_of_blocks (F : CNF Nat) (L : Nat → CNF Nat) (k : Nat)
    (step : ∀ j, j < k → ∀ a, CNF.Sat a (G F L j) → CNF.Sat a (L j))
    (hk : 0 < k) (hlast : hasEmpty (L (k - 1)) = true) : F.Unsat := by
  intro a
  cases hF : F.eval a with
  | false => rfl
  | true =>
    exfalso
    have hG := chain F L k step a hF
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have := (CNF.sat_append.mp hG).2
    exact not_sat_of_hasEmpty _ hlast a (by simpa using this)

end LratChunk
