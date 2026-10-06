/-
Simple673/Local/FinalAll.lean — the eight-point local inequality.

`localInequality : LocalInequality` follows from

* `kTabArray_sound` (`Simple673/Kernel/Table.lean`): the kernel table is a sound lower
  enclosure of `K²`, proved with the standard axioms;
* `localInequality_of_checkPar` (`Simple673/Local/Soundness.lean`): soundness of the branch
  and bound in its form with parallel parts, proved with the standard axioms;
* `Local.check_passes` (`Simple673/Local/RunAll.lean`): the checker accepts the root box on
  that table (the array `kTabArray` of `Simple673/Kernel/Array.lean`), evaluated by compiled code
  (`native_decide`).

So `#print axioms localInequality` lists the three standard axioms and one computational fact.
-/
import Simple673.Local.Soundness
import Simple673.Local.RunAll
import Simple673.Kernel.Table

namespace Simple673

/-- **The local inequality**: for eight points with gaps `g_r ≥ 17/20`,
`∑ κ_i ≤ α ∑ g_r + ∑_{i<j} W_{ij} K(y_j - y_i)² + ∑_r B_r(g_r)`. -/
theorem localInequality : LocalInequality :=
  localInequality_of_checkPar kTabArray kTabArray_size kTabArray_sound 32 96 (by norm_num)
    Local.check_passes

end Simple673
