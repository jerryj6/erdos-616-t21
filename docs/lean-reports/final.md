> **Internal working note.** This file is a raw report written while the proof was being developed and checked. It is kept for provenance. File paths, run names and timings refer to the original working directory, not to this repository; see `docs/path-map.md` for the correspondence. The curated statements are in `paper/` and `README.md`.

# Erdős #616 t(21)=4 — end-to-end Lean theorem (2026-10-16 19:30 EDT)

Exit 0, no sorry. Negative control (=5) fails. Statement def localTransversalBound copied from formal-conjectures into Full.lean. Trust base: Lean kernel + propext/Classical.choice/Quot.sound + native_decide (compiled LRAT and trace/G14 checkers). Built from /tmp/g14m (G14Full, HandA, E616Full) + work/e616lean/bridge (NoK4Assembly, W7I) + work/e616lrat; HandA sources identical md5 4d9a8976.

```lean
import G14Full
import NoK4Assembly
/-! Erdős #616: t(21) = 4, end to end. -/
theorem erdos_616_t21_eq_4 :
    Hypergraph.localTransversalBound 21 (3 * 21 - 3) 1 = 4 :=
  erdos_616_r21_of_NK4 Erdos616R21.NK4_leaf_proved
#print axioms erdos_616_t21_eq_4
```
```
'erdos_616_t21_eq_4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ok24x._native.native_decide.ax_1_1,
 ok33._native.native_decide.ax_1_1,
 ok34._native.native_decide.ax_1_1,
 G14.chk14968._native.native_decide.ax_1_1,
 G14.chk15116._native.native_decide.ax_1_1,
 G14.chk15954._native.native_decide.ax_1_1,
 G14.chk16054._native.native_decide.ax_1_1,
 G14.chk17917._native.native_decide.ax_1_1,
 G14.chkDead._native.native_decide.ax_1_1,
 G14.root_ok._native.native_decide.ax_1_1,
 G14.univ_ok._native.native_decide.ax_1_1,
 E616.tree_24x_0.certOk_eq._native.native_decide.ax_1_1,
 E616.tree_24x_1.certOk_eq._native.native_decide.ax_1_1,
 E616.tree_24x_2.certOk_eq._native.native_decide.ax_1_1,
 E616.tree_24x_3.certOk_eq._native.native_decide.ax_1_1,
 E616.tree_24x_4.certOk_eq._native.native_decide.ax_1_1,
 E616.tree_24x_5.certOk_eq._native.native_decide.ax_1_1,
 E616.tree_24x_6.certOk_eq._native.native_decide.ax_1_1,
 E616.tree_33_0.certOk_eq._native.native_decide.ax_1_1,
 E616.tree_33_1.certOk_eq._native.native_decide.ax_1_1,
 E616.tree_33_2.certOk_eq._native.native_decide.ax_1_1,
 E616.tree_33_3.certOk_eq._native.native_decide.ax_1_1,
 E616.tree_33_4.certOk_eq._native.native_decide.ax_1_1,
 E616.tree_33_5.certOk_eq._native.native_decide.ax_1_1,
 E616.tree_33_6.certOk_eq._native.native_decide.ax_1_1,
 E616.tree_33_7.certOk_eq._native.native_decide.ax_1_1,
 E616.tree_34_0.certOk_eq._native.native_decide.ax_1_1,
 E616.tree_34_1.certOk_eq._native.native_decide.ax_1_1,
 E616.tree_34_2.certOk_eq._native.native_decide.ax_1_1,
 E616.tree_34_3.certOk_eq._native.native_decide.ax_1_1,
 E616.tree_34_4.certOk_eq._native.native_decide.ax_1_1,
 E616.w14_14968.certOk_eq._native.native_decide.ax_1_1,
 E616.w14_15116.certOk_eq._native.native_decide.ax_1_1,
 E616.w14_17917.certOk_eq._native.native_decide.ax_1_1,
 E616.w14_certdead.certOk_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.hlast._native.native_decide.ax_1_1,
 E616C.w14_16054.hlast._native.native_decide.ax_1_1,
 E616C.w14_15954.B0.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.B1.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.B10.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.B2.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.B3.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.B4.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.B5.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.B6.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.B7.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.B8.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_15954.B9.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_16054.B0.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_16054.B1.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_16054.B2.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_16054.B3.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_16054.B4.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_16054.B5.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_16054.B6.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_16054.B7.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_16054.B8.ok_eq._native.native_decide.ax_1_1,
 E616C.w14_16054.B9.ok_eq._native.native_decide.ax_1_1]
```
