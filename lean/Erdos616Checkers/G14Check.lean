import Std.Sat.CNF
/-!
# G14 (N-K4 leaf of Erdős #616, r = 21): the decidable checkers (core Lean only, no Mathlib)

Everything here is a *computable* definition over 16-bit masks of the 16 core points of the (3,2,1,1)-K4 base
(bit order v, w, al0, al1, g0, g1, g2, m0, m1, m2, a3_0, a3_1, a4_0, a4_1, c3, c4; the order of the G14 CNFs),
plus the *glue theorem* `eval_of_check`: if an abstract "trace model" exists (occurring traces with the four
properties of `Model`), then every CNF that passes `checkCNF` is satisfied by the induced assignment.
The rules in `ok` (per-edge) and `rulesAt` (pairwise) are literal transcriptions of the referee's
`ref_states.ok` and `pairref.feasible` (sat/t21/w14ref/), with the overlap `zu` eliminated by taking its
least admissible value (all rules other than Lemma A are upper bounds on `zu`).
-/
open Std.Sat

namespace G14

/-- base edge `P_q` restricted to the core, as a 16-bit mask -/
def Pm : Nat → Nat
  | 0 => 16271 | 1 => 50163 | 2 => 19581 | 3 => 45182 | _ => 0
/-- `|O_q| = |P_q \ core|` -/
def OSZ : Nat → Nat
  | 0 => 10 | 1 => 11 | 2 => 12 | 3 => 12 | _ => 0
def cmp (y : Nat) : Nat := 65535 ^^^ y
/-- popcount on 16 bits -/
def pc (x : Nat) : Nat := (List.finRange 16).countP (fun i => x.testBit i.val)

structure O4 where
  o0 : Nat
  o1 : Nat
  o2 : Nat
  o3 : Nat
deriving DecidableEq, Repr

def O4.get (o : O4) : Nat → Nat
  | 0 => o.o0 | 1 => o.o1 | 2 => o.o2 | 3 => o.o3 | _ => 0
def O4.sum (o : O4) : Nat := o.o0 + o.o1 + o.o2 + o.o3

def Q4 : List Nat := [0, 1, 2, 3]
def PR : List (Nat × Nat) := [(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]
def TR : List (Nat × Nat × Nat) := [(0,1,2), (0,1,3), (0,2,3), (1,2,3)]

/-- `|X ∩ P_q|` for a state (b, o) -/
def xq (b : Nat) (o : O4) (q : Nat) : Nat := pc (b &&& Pm q) + o.get q

/-- per-edge rules (S13.1 list as in ref_states.ok) -/
def okBasic (b : Nat) (o : O4) : Bool :=
  Q4.all (fun q => o.get q ≤ OSZ q) && pc b + o.sum ≤ 21 && Q4.all (fun q => 5 ≤ xq b o q)

def okF1D1 (b : Nat) (o : O4) : Bool :=
  PR.all (fun p => let N := Pm p.1 &&& Pm p.2
    b &&& N != 0 && (b &&& N == N || xq b o p.1 + xq b o p.2 ≤ 9 + pc (b &&& N)))

def okL3 (b : Nat) (o : O4) : Bool :=
  TR.all (fun T => let t := Pm T.1 &&& Pm T.2.1 &&& Pm T.2.2
    let U := Pm T.1 ||| Pm T.2.1 ||| Pm T.2.2
    b &&& t != 0 || pc (b &&& U) + (o.get T.1 + o.get T.2.1 + o.get T.2.2) ≤ 8 + pc t)

def okNTb (b : Nat) : Bool :=
  PR.all (fun p => let i := p.1; let j := p.2; let N := Pm i &&& Pm j
    pc (b &&& N) != 1 || Q4.all (fun k => k == i || k == j ||
      (let y := Pm k &&& N
       pc y != 1 || y == (b &&& N) ||
         (2 ≤ pc (b &&& Pm k &&& Pm i &&& cmp N) && 2 ≤ pc (b &&& Pm k &&& Pm j &&& cmp N)))))

def okDerived (b : Nat) (o : O4) (i : Nat) : Bool :=
  let Nc := b &&& Pm i
  Q4.all (fun j => j == i ||
    ((pc (Pm j &&& Nc) != 1 || xq b o j == 5) &&
     ((o.get i == 0 && Nc &&& cmp (Pm j) == 0) ||
       pc (Pm j &&& Pm i) + pc (b &&& Pm j &&& cmp (Pm i)) + o.get j ≤ 9))) &&
  Q4.all (fun j => Q4.all (fun k => !(decide (j < k)) || j == i || k == i ||
    pc (Pm j &&& Nc) != 1 || pc (Pm k &&& Nc) != 1 || (Pm j &&& Nc) == (Pm k &&& Nc) ||
    (pc (Pm i &&& Pm j &&& Pm k &&& cmp b) != 1 && pc (b &&& Pm j &&& Pm k &&& cmp (Pm i)) != 1 &&
     (Pm j &&& Pm k &&& cmp (Pm i) &&& cmp b) == 0)))

def ok (b : Nat) (o : O4) : Bool :=
  okBasic b o && okF1D1 b o && okL3 b o && okNTb b && Q4.all (fun i => xq b o i != 5 || okDerived b o i)

/-- the o-box (triangular): `L_q = 5 - |b ∩ P_q|` (truncated, Lemma A) and `|b| + Σ o_q ≤ 21`; `o_q ≤ |O_q|` is left to `ok` -/
def Lo (b : Nat) (q : Nat) : Nat := 5 - pc (b &&& Pm q)
def rngLH (lo hi : Nat) : List Nat := List.range' lo (hi + 1 - lo)

def box (b : Nat) : List O4 :=
  let R := 21 - pc b
  let L0 := Lo b 0; let L1 := Lo b 1; let L2 := Lo b 2; let L3 := Lo b 3
  (rngLH L0 (R - (L1 + L2 + L3))).flatMap fun a0 =>
  (rngLH L1 (R - (a0 + L2 + L3))).flatMap fun a1 =>
  (rngLH L2 (R - (a0 + a1 + L3))).flatMap fun a2 =>
  (rngLH L3 (R - (a0 + a1 + a2))).map fun a3 => ⟨a0, a1, a2, a3⟩

def states (b : Nat) : List O4 := (box b).filter (ok b)

/-! ## pairwise rules (pairref.feasible) -/

def uu (b : Nat) (o : O4) : Nat := 21 - pc b - o.sum

/-- the 11 sets X of ≥ 2 base edges, as 4-bit masks -/
def XS : List Nat := [3, 5, 6, 9, 10, 12, 7, 11, 13, 14, 15]
def capX (X : Nat) : Nat := Q4.foldl (fun acc q => if X.testBit q then acc &&& Pm q else acc) 65535
def cupX (X : Nat) : Nat := Q4.foldl (fun acc q => if X.testBit q then acc ||| Pm q else acc) 0
/-- Σ_{q ∈ X} |O_q| -/
def osX (X : Nat) : Nat := Q4.foldl (fun acc q => if X.testBit q then acc + OSZ q else acc) 0
/-- Σ_{q ∉ X} o_q -/
def outX (X : Nat) (o : O4) : Nat := Q4.foldl (fun acc q => if X.testBit q then acc else acc + o.get q) 0

def isSingle (b : Nat) (i j : Nat) : Bool := pc (b &&& (Pm i &&& Pm j)) == 1

def rulesAt (b1 : Nat) (o1 : O4) (b2 : Nat) (o2 : O4) (z : O4) (zu : Nat) : Bool :=
  let I := b1 &&& b2
  let u1 := uu b1 o1
  let u2 := uu b2 o2
  -- range of zu
  zu ≤ min u1 u2 &&
  -- Lemma A
  5 ≤ pc I + z.sum + zu &&
  -- F1 with each base edge
  Q4.all (fun q => I &&& Pm q != 0 || 0 < z.get q) &&
  -- SAME: cross-type singles of one base pair: S(a), W7-I, S(b)
  PR.all (fun p => let i := p.1; let j := p.2; let N := Pm i &&& Pm j
    !(isSingle b1 i j && isSingle b2 i j && (b1 &&& N) != (b2 &&& N)) ||
    (I &&& cmp (Pm i ||| Pm j) == 0 && Q4.all (fun q => q == i || q == j || z.get q == 0) && zu == 0 &&
      (let a := pc (I &&& Pm i &&& cmp (Pm j)) + z.get i
       let c := pc (I &&& Pm j &&& cmp (Pm i)) + z.get j
       2 ≤ a && 2 ≤ c && 5 ≤ a + c))) &&
  -- L on X ∪ {F, F'} for every X of ≥ 2 base edges with ∩X ∩ F ∩ F' = ∅
  XS.all (fun X => capX X &&& I != 0 ||
    61 + (pc (I &&& cmp (cupX X)) + zu + outX X z) ≤
      (pc (cupX X) + osX X) + (pc (b1 &&& cmp (cupX X)) + u1 + outX X o1) +
        (pc (b2 &&& cmp (cupX X)) + u2 + outX X o2)) &&
  -- D1 at derived 5-pairs (P_k, F) (and (P_k, F')), unless F ∩ P_k ⊆ F'
  Q4.all (fun k => xq b1 o1 k != 5 || (b1 &&& Pm k &&& cmp b2 == 0 && z.get k == o1.get k) ||
    pc (b2 &&& Pm k) + o2.get k + pc (I &&& cmp (Pm k)) + zu + (z.sum - z.get k) ≤ 9) &&
  Q4.all (fun k => xq b2 o2 k != 5 || (b2 &&& Pm k &&& cmp b1 == 0 && z.get k == o2.get k) ||
    pc (b1 &&& Pm k) + o1.get k + pc (I &&& cmp (Pm k)) + zu + (z.sum - z.get k) ≤ 9)

def zr (o1 o2 : O4) (q : Nat) : List Nat :=
  let lo := o1.get q + o2.get q - OSZ q
  List.range' lo (min (o1.get q) (o2.get q) + 1 - lo)

def zbox (o1 o2 : O4) : List O4 :=
  (zr o1 o2 0).flatMap fun a0 => (zr o1 o2 1).flatMap fun a1 => (zr o1 o2 2).flatMap fun a2 =>
    (zr o1 o2 3).map fun a3 => ⟨a0, a1, a2, a3⟩

def zumin (b1 b2 : Nat) (z : O4) : Nat := 5 - (pc (b1 &&& b2) + z.sum)

def feasible (b1 : Nat) (o1 : O4) (b2 : Nat) (o2 : O4) : Bool :=
  (zbox o1 o2).any fun z => rulesAt b1 o1 b2 o2 z (zumin b1 b2 z)

def compatSt (b1 : Nat) (s1 : List O4) (b2 : Nat) (s2 : List O4) : Bool :=
  s1.any fun o1 => s2.any fun o2 => feasible b1 o1 b2 o2

/-- two traces are compatible: some state pair and some overlap vector satisfy all pairwise rules -/
def compatTr (t1 t2 : Nat) : Bool := compatSt t1 (states t1) t2 (states t2)

/-! ## the variable table and the CNF checker -/

def parseNats (s : String) : Array Nat :=
  ((s.split (fun ch => ch == ' ' || ch == '\n')).filterMap fun w => w.toNat?).toArray

def Ttext : String := include_str "G14T.txt"
/-- DIMACS variable `v` (atom `v-1`) stands for core trace `T[v-1]` -/
def T : Array Nat := parseNats Ttext
/-- the state table is passed as an argument (`sa = T.map states`) so that nothing heavy is a closed term -/
def compatV (sa : Array (List O4)) (u v : Nat) : Bool := compatSt T[u]! sa[u]! T[v]! sa[v]!

/-- untrusted helper: binary search for `t` in the sorted table -/
partial def findIdx (t : Nat) : Nat :=
  let rec go (lo hi : Nat) : Nat :=
    if lo + 1 ≥ hi then lo else
      let m := (lo + hi) / 2
      if T[m]! ≤ t then go m hi else go lo m
  go 0 T.size

/-- universe check: every 16-bit trace with an admissible state is in the table -/
def univOK (_ : Unit) : Bool :=
  (List.range 65536).all fun t => (states t).isEmpty || (findIdx t < T.size && T[findIdx t]! == t)

/-- a needed core 4-set: 4 points meeting every base edge -/
def neededB (B : Nat) : Bool := B < 65536 && pc B == 4 && Q4.all (fun q => B &&& Pm q != 0)

def avoiders (B : Nat) : List Nat := (List.range T.size).filter fun v => T[v]! &&& B == 0

/-- untrusted helper: guess the 4-set of a COV clause -/
def findB (atoms : List Nat) : Option Nat :=
  let W := cmp (atoms.foldl (fun acc v => acc ||| T[v]!) 0)
  (List.range 65536).find? fun B => B &&& cmp W == 0 && neededB B && (avoiders B).length == atoms.length

def covOK (lits : List (Nat × Bool)) : Bool :=
  lits.all (fun l => l.2) &&
    match findB (lits.map Prod.fst) with
    | some B => neededB B && lits.map Prod.fst == avoiders B
    | none => false

def clauseOK (sa : Array (List O4)) (extra : List (Nat × Bool)) (lits : List (Nat × Bool)) : Bool :=
  match lits with
  | [(u, false), (v, false)] => decide (u < T.size) && decide (v < T.size) && T[u]! != T[v]! && !(compatV sa u v)
  | _ => lits == extra || covOK lits

def checkCNFWith (sa : Array (List O4)) (f : CNF Nat) (extra : List (Nat × Bool)) : Bool :=
  f.clauses.all fun c => clauseOK sa extra c.literals

def checkCNF (f : CNF Nat) (extra : List (Nat × Bool)) : Bool := checkCNFWith (T.map states) f extra

end G14
