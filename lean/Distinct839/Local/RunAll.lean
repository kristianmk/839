/-
Distinct839/Local/RunAll.lean — the evaluation of the checker of the local inequality.

The statement `checkAll kTabArray = true` says that the branch and bound of
`Distinct839/Local/Checker.lean` accepts the root box when it reads the kernel table
`kTabArray` of `Distinct839/Kernel/Table.lean`. It is evaluated by compiled code:
`native_decide` compiles the Boolean, runs it, and records the result as the axiom
`Distinct839.Local.check_passes._native.native_decide.ax_1_1`. This is the only place in the
development where Lean's kernel does not check a computation.
-/
import Distinct839.Kernel.Table
import Distinct839.Local.Checker

namespace Distinct839.Local

/-- The checker accepts the root box `[13926, 209009]⁶` on the kernel table (60,467,309 boxes). -/
theorem check_passes : checkAll kTabArray = true := by native_decide

end Distinct839.Local
