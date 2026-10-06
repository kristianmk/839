/-
Line889/Local/FinalAll.lean — the seven-point local inequality.

`localInequality : LocalInequality` follows from

* `kTabArray_sound` (`Line889/Kernel/Table.lean`): the kernel table is a sound lower
  enclosure of `K²`, proved with the standard axioms;
* `localInequality_of_check` (`Line889/Local/Soundness.lean`): soundness of the branch and
  bound, proved with the standard axioms;
* `Local.check_passes` (`Line889/Local/RunAll.lean`): the checker accepts the root box on
  that table (the array `kTabArray` of `Line889/Kernel/Array.lean`), evaluated by compiled code
  (`native_decide`).

So `#print axioms localInequality` lists the three standard axioms and one computational fact.
-/
import Line889.Local.Soundness
import Line889.Local.RunAll
import Line889.Kernel.Table

namespace Line889

/-- **The local inequality**: for seven points with gaps `g_r ≥ 17/20`,
`∑ κ_i ≤ α ∑ g_r + ∑_{i<j} W_{ij} K(y_j - y_i)² + ∑_r B_r(g_r)`. -/
theorem localInequality : LocalInequality :=
  localInequality_of_check kTabArray kTabArray_size kTabArray_sound Local.check_passes

end Line889
