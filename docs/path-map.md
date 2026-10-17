# Path map: working tree → this repository

The internal reports in `docs/` and the paper were originally written with paths in the working directory. Those paths
have now been rewritten to the repository paths below (paper §11 and Table 4 directly; `docs/` mechanically from this
table). The table is kept for provenance and for reading the raw logs, which are unchanged. Lean sources were renamed into one module tree; apart from
`import` lines, `include_str` data paths, the output path of the parser round-trip `#eval`, and file pointers inside
comments, their contents are unchanged (checked mechanically, see `lean/VERIFICATION.md`).

## Lean

| Working path | Repository path |
|---|---|
| `e616lean/BridgeG14.lean` | `lean/Erdos616/G14/Bridge.lean` |
| `e616lean/BridgeG14Final.lean` | `lean/Erdos616/G14/BridgeFinal.lean` |
| `e616lean/BridgeG14Pair.lean` | `lean/Erdos616/G14/BridgePair.lean` |
| `e616lean/Full.lean` | `lean/Erdos616/Basic.lean` |
| `e616lean/G14Assembly.lean` | `lean/Erdos616/G14/Assembly.lean` |
| `e616lean/G14Full.lean` | `lean/Erdos616/G14/Leaf.lean` |
| `e616lean/HandA.lean` | `lean/Erdos616/HandA.lean` |
| `e616lean/W7I.lean` | `lean/Erdos616/W7I.lean` |
| `e616lean/bridge/BridgeNoK4Leaves.lean` | `lean/Erdos616/NoK4/Leaves.lean` |
| `e616lean/bridge/NoK4Assembly.lean` | `lean/Erdos616/NoK4/Assembly.lean` |
| `e616lean/bridge/NoK4Base.lean` | `lean/Erdos616/NoK4/Base.lean` |
| `e616lean/bridge/NoK4Build.lean` | `lean/Erdos616/NoK4/Build.lean` |
| `e616lean/bridge/NoK4Edge.lean` | `lean/Erdos616/NoK4/Edge.lean` |
| `e616lean/bridge/NoK4Frame.lean` | `lean/Erdos616/NoK4/Frame.lean` |
| `e616lean/bridge/NoK4Pair.lean` | `lean/Erdos616/NoK4/Pair.lean` |
| `e616lean/bridge/TrCheck.lean` | `lean/Erdos616Checkers/TrCheck.lean` |
| `e616lean/bridge/TrRun24x.lean` | `lean/Erdos616/NoK4/TrRun24x.lean` |
| `e616lean/bridge/TrRun33.lean` | `lean/Erdos616/NoK4/TrRun33.lean` |
| `e616lean/bridge/TrRun34.lean` | `lean/Erdos616/NoK4/TrRun34.lean` |
| `e616lean/bridge/WitData.lean` | `lean/Erdos616/NoK4/WitData.lean` |
| `e616lean/final/Erdos616R21Final.lean` | `lean/Erdos616/Final.lean` |
| `e616lean/final/Neg.lean` | `lean/test/Neg.lean` |
| `e616lean/g14/G14Case14968.lean` | `lean/Erdos616/G14/Case14968.lean` |
| `e616lean/g14/G14Case15116.lean` | `lean/Erdos616/G14/Case15116.lean` |
| `e616lean/g14/G14Case15954.lean` | `lean/Erdos616/G14/Case15954.lean` |
| `e616lean/g14/G14Case16054.lean` | `lean/Erdos616/G14/Case16054.lean` |
| `e616lean/g14/G14Case17917.lean` | `lean/Erdos616/G14/Case17917.lean` |
| `e616lean/g14/G14CaseDead.lean` | `lean/Erdos616/G14/CaseDead.lean` |
| `e616lean/g14/G14Check.lean` | `lean/Erdos616Checkers/G14Check.lean` |
| `e616lean/g14/G14Glue.lean` | `lean/Erdos616/G14/Glue.lean` |
| `e616lean/g14/G14Root.lean` | `lean/Erdos616/G14/Root.lean` |
| `e616lean/g14/G14Univ.lean` | `lean/Erdos616/G14/Univ.lean` |
| `e616lrat/LratCheck.lean` | `lean/Erdos616Checkers/LratCheck.lean` |
| `e616lrat/LratChunk.lean` | `lean/Erdos616Checkers/LratChunk.lean` |
| `e616lrat/certs/tree_24x_0.lean` | `lean/Erdos616/Cert/tree_24x_0.lean` |
| `e616lrat/certs/tree_24x_1.lean` | `lean/Erdos616/Cert/tree_24x_1.lean` |
| `e616lrat/certs/tree_24x_2.lean` | `lean/Erdos616/Cert/tree_24x_2.lean` |
| `e616lrat/certs/tree_24x_3.lean` | `lean/Erdos616/Cert/tree_24x_3.lean` |
| `e616lrat/certs/tree_24x_4.lean` | `lean/Erdos616/Cert/tree_24x_4.lean` |
| `e616lrat/certs/tree_24x_5.lean` | `lean/Erdos616/Cert/tree_24x_5.lean` |
| `e616lrat/certs/tree_24x_6.lean` | `lean/Erdos616/Cert/tree_24x_6.lean` |
| `e616lrat/certs/tree_33_0.lean` | `lean/Erdos616/Cert/tree_33_0.lean` |
| `e616lrat/certs/tree_33_1.lean` | `lean/Erdos616/Cert/tree_33_1.lean` |
| `e616lrat/certs/tree_33_2.lean` | `lean/Erdos616/Cert/tree_33_2.lean` |
| `e616lrat/certs/tree_33_3.lean` | `lean/Erdos616/Cert/tree_33_3.lean` |
| `e616lrat/certs/tree_33_4.lean` | `lean/Erdos616/Cert/tree_33_4.lean` |
| `e616lrat/certs/tree_33_5.lean` | `lean/Erdos616/Cert/tree_33_5.lean` |
| `e616lrat/certs/tree_33_6.lean` | `lean/Erdos616/Cert/tree_33_6.lean` |
| `e616lrat/certs/tree_33_7.lean` | `lean/Erdos616/Cert/tree_33_7.lean` |
| `e616lrat/certs/tree_34_0.lean` | `lean/Erdos616/Cert/tree_34_0.lean` |
| `e616lrat/certs/tree_34_1.lean` | `lean/Erdos616/Cert/tree_34_1.lean` |
| `e616lrat/certs/tree_34_2.lean` | `lean/Erdos616/Cert/tree_34_2.lean` |
| `e616lrat/certs/tree_34_3.lean` | `lean/Erdos616/Cert/tree_34_3.lean` |
| `e616lrat/certs/tree_34_4.lean` | `lean/Erdos616/Cert/tree_34_4.lean` |
| `e616lrat/certs/w14_14968.lean` | `lean/Erdos616/Cert/w14_14968.lean` |
| `e616lrat/certs/w14_15116.lean` | `lean/Erdos616/Cert/w14_15116.lean` |
| `e616lrat/certs/w14_17917.lean` | `lean/Erdos616/Cert/w14_17917.lean` |
| `e616lrat/certs/w14_certdead.lean` | `lean/Erdos616/Cert/w14_certdead.lean` |
| `e616lrat/chunks/w14_15954/w14_15954_B0.lean` | `lean/Erdos616/Cert/w14_15954/B0.lean` |
| `e616lrat/chunks/w14_15954/w14_15954_B1.lean` | `lean/Erdos616/Cert/w14_15954/B1.lean` |
| `e616lrat/chunks/w14_15954/w14_15954_B10.lean` | `lean/Erdos616/Cert/w14_15954/B10.lean` |
| `e616lrat/chunks/w14_15954/w14_15954_B2.lean` | `lean/Erdos616/Cert/w14_15954/B2.lean` |
| `e616lrat/chunks/w14_15954/w14_15954_B3.lean` | `lean/Erdos616/Cert/w14_15954/B3.lean` |
| `e616lrat/chunks/w14_15954/w14_15954_B4.lean` | `lean/Erdos616/Cert/w14_15954/B4.lean` |
| `e616lrat/chunks/w14_15954/w14_15954_B5.lean` | `lean/Erdos616/Cert/w14_15954/B5.lean` |
| `e616lrat/chunks/w14_15954/w14_15954_B6.lean` | `lean/Erdos616/Cert/w14_15954/B6.lean` |
| `e616lrat/chunks/w14_15954/w14_15954_B7.lean` | `lean/Erdos616/Cert/w14_15954/B7.lean` |
| `e616lrat/chunks/w14_15954/w14_15954_B8.lean` | `lean/Erdos616/Cert/w14_15954/B8.lean` |
| `e616lrat/chunks/w14_15954/w14_15954_B9.lean` | `lean/Erdos616/Cert/w14_15954/B9.lean` |
| `e616lrat/chunks/w14_15954/w14_15954_Data.lean` | `lean/Erdos616/Cert/w14_15954/Data.lean` |
| `e616lrat/chunks/w14_15954/w14_15954_Final.lean` | `lean/Erdos616/Cert/w14_15954/Final.lean` |
| `e616lrat/chunks/w14_16054/w14_16054_B0.lean` | `lean/Erdos616/Cert/w14_16054/B0.lean` |
| `e616lrat/chunks/w14_16054/w14_16054_B1.lean` | `lean/Erdos616/Cert/w14_16054/B1.lean` |
| `e616lrat/chunks/w14_16054/w14_16054_B2.lean` | `lean/Erdos616/Cert/w14_16054/B2.lean` |
| `e616lrat/chunks/w14_16054/w14_16054_B3.lean` | `lean/Erdos616/Cert/w14_16054/B3.lean` |
| `e616lrat/chunks/w14_16054/w14_16054_B4.lean` | `lean/Erdos616/Cert/w14_16054/B4.lean` |
| `e616lrat/chunks/w14_16054/w14_16054_B5.lean` | `lean/Erdos616/Cert/w14_16054/B5.lean` |
| `e616lrat/chunks/w14_16054/w14_16054_B6.lean` | `lean/Erdos616/Cert/w14_16054/B6.lean` |
| `e616lrat/chunks/w14_16054/w14_16054_B7.lean` | `lean/Erdos616/Cert/w14_16054/B7.lean` |
| `e616lrat/chunks/w14_16054/w14_16054_B8.lean` | `lean/Erdos616/Cert/w14_16054/B8.lean` |
| `e616lrat/chunks/w14_16054/w14_16054_B9.lean` | `lean/Erdos616/Cert/w14_16054/B9.lean` |
| `e616lrat/chunks/w14_16054/w14_16054_Data.lean` | `lean/Erdos616/Cert/w14_16054/Data.lean` |
| `e616lrat/chunks/w14_16054/w14_16054_Final.lean` | `lean/Erdos616/Cert/w14_16054/Final.lean` |
| `e616lean/g14/T.txt` | `lean/Erdos616Checkers/G14T.txt` |
| `e616lean/final/final.out` | `lean/VERIFICATION.md` (original axiom log reproduced there) |

## Certificate data (release asset `e616-sat-certs.tar.zst`, laid out by `scripts/fetch_certs.sh`)

| Working path | Repository path |
|---|---|
| `e616/w11ref/tr/tree_{24x,33,34}_*.cnf` | `data/cnf/tree_*.cnf` |
| `e616/t21/w14/w14_cert2_<r>.cnf` | `data/cnf/w14_<r>.cnf` |
| `e616/t21/w14/w14_certdead.cnf` | `data/cnf/w14_certdead.cnf` |
| `e616lrat/lrat/*.lrat` | `data/lrat/*.lrat` |
| `e616lrat/chunks/w14_{15954,16054}/` | `data/chunks/w14_{15954,16054}/` (regenerated by `sat/lrat/split.py`) |

## Scripts and notes

| Working path | Repository path |
|---|---|
| `work/e616/w11ref/tr/` | `sat/w11ref/tr/` |
| `work/e616/t21/w14/` | `sat/t21/w14/` |
| `work/e616/t21/w14ref/` | `sat/t21/w14ref/` |
| `work/e616/nref/` | `sat/nref/` |
| `work/e616/w10ref/` | `sat/w10ref/` |
| `work/e616lrat/{gen,split,gen_chunks,renum,cmp}.py` | `sat/lrat/` |
| `candidates/erdos-616-t21-upper.md` | `docs/proof-notes.md` |
| `candidates/erdos-616-<x>-referee.md` | `docs/referee/<x>-referee.md` |
| `candidates/lean-erdos616[-<x>].md` | `docs/lean-reports/<x or main>.md` |
| `paper/erdos616-t21.{tex,pdf}` | `paper/` |
