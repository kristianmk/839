/-
Distinct839/Local/FinalAll.lean — the seven-point local inequality.

`localInequality : LocalInequality` follows from

* `kTabArray_sound` (`Distinct839/Kernel/Table.lean`): the kernel table is a sound lower
  enclosure of `K²`, proved with the standard axioms;
* `localInequality_of_check` (`Distinct839/Local/Soundness.lean`): soundness of the branch and
  bound, proved with the standard axioms;
* `Local.check_passes` (`Distinct839/Local/RunAll.lean`): the checker accepts the root box on
  that table, evaluated by compiled code (`native_decide`).

So `#print axioms localInequality` lists the three standard axioms and one computational fact.
-/
import Distinct839.Local.Soundness
import Distinct839.Local.RunAll

namespace Distinct839

/-- **The local inequality**: for all gaps `≥ 17/20` and all `2⁷` labelings,
`∑ κ_{i,d_i} ≤ α ∑ g_r + ∑_{i<j} W_{ij}^{d_i d_j} K(y_j - y_i)² + ∑_r B_r^{d_r d_{r+1}}(g_r)`. -/
theorem localInequality : LocalInequality :=
  localInequality_of_check kTabArray kTabArray_size kTabArray_sound Local.check_passes

end Distinct839
