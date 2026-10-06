/-
Simple673/Local/RunAll.lean — the evaluation of the checker of the local inequality.

The statement `checkAllPar kTabArray 32 96 = true` says that the branch and bound of
`Simple673/Local/Checker.lean` accepts the root box when it reads the kernel table
`kTabArray` of `Simple673/Kernel/Array.lean`. The search is that of `checkAll`, cut after
`32` splits into `96` parts, which compiled code evaluates as tasks, each on a thread of its
own (the value of the statement does not depend on how they are scheduled). It is evaluated by
compiled code: `native_decide` compiles
the Boolean, runs it, and records the result as the axiom
`Simple673.Local.check_passes._native.native_decide.ax_1_1`. This is the only place in the
development `Simple673` where Lean's kernel does not check a computation.
-/
import Simple673.Kernel.Array
import Simple673.Local.Checker

namespace Simple673.Local

/-- The checker accepts the root box `[13926, 262143]⁷` on the kernel table (535,332,163 boxes,
of which 267,666,082 are accepted and the others split). -/
theorem check_passes : checkAllPar kTabArray 32 96 = true := by native_decide

end Simple673.Local
