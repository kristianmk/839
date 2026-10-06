/-
Line889/Local/RunAll.lean — the evaluation of the checker of the local inequality.

The statement `checkAll kTabArray = true` says that the branch and bound of
`Line889/Local/Checker.lean` accepts the root box when it reads the kernel table
`kTabArray` of `Line889/Kernel/Array.lean`. It is evaluated by compiled code:
`native_decide` compiles the Boolean, runs it, and records the result as the axiom
`Line889.Local.check_passes._native.native_decide.ax_1_1`. This is the only place in the
development `Line889` where Lean's kernel does not check a computation.
-/
import Line889.Kernel.Array
import Line889.Local.Checker

namespace Line889.Local

/-- The checker accepts the root box `[13926, 262143]⁶` on the kernel table (572,959,453 boxes,
of which 286,479,727 are accepted and the others split). -/
theorem check_passes : checkAll kTabArray = true := by native_decide

end Line889.Local
