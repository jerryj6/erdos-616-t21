import G14Check
import LratCheck
open G14
def main (args : List String) : IO Unit := do
  let t0 ← IO.monoMsNow
  IO.println s!"T.size {T.size} {T[15116]!}"
  let sa := T.map states
  IO.println s!"sa size {sa.size} total states {sa.foldl (fun a l => a + l.length) 0}"
  let t1 ← IO.monoMsNow
  IO.println s!"sa ms {t1-t0}"
  let c := (List.range 3000).foldl (fun acc k => if compatV sa (k*5) (k*6+1) then acc+1 else acc) 0
  let t2 ← IO.monoMsNow
  IO.println s!"3000 compatV: {c} compatible, ms {t2-t1}"
  match args with
  | [f] =>
    let txt ← IO.FS.readFile f
    let cnf := LratCheck.parseDimacs txt
    let t3 ← IO.monoMsNow
    IO.println s!"parsed {cnf.clauses.size} clauses ms {t3-t2}"
    let mut bad := 0
    let mut nconf := 0
    let mut i := 0
    for cl in cnf.clauses do
      if !(clauseOK sa [] cl.literals) then
        bad := bad + 1
        if bad ≤ 5 then IO.println s!"not ok: clause {i} {cl.literals.take 5}"
      i := i + 1
      if i % 100000 == 0 then
        let tt ← IO.monoMsNow
        IO.println s!"  {i} clauses, bad {bad}, ms {tt-t3}"
    let t4 ← IO.monoMsNow
    IO.println s!"clauses {i} bad {bad} ms {t4-t3}"
  | _ =>
    let u := univOK ()
    let t3 ← IO.monoMsNow
    IO.println s!"univOK {u} ms {t3-t2}"
