/-
Simple673/Kernel/Array.lean — the kernel table as an array, for the local-inequality checker.

`kTabArray` holds `kTab k` for `k = 0, …, tabR`: 262144 entries, 16 periods of 16384 cells. It
computes the 8192 trigonometric enclosures once (`trigArr`) and shares them between the 16
periods of the table. The evaluation of the whole array by the Lean interpreter takes about two
minutes.

This file contains the definitions and the size of the array, and nothing else: it and
`Simple673/Kernel/Compute.lean` are what the compiled run of the checker imports from this
directory, so that the run does not depend on the proofs about the kernel. That the array agrees
with `kTab` (`Kernel.kTabArray_getElem`) and is a sound lower enclosure of `K²`
(`kTabArray_sound`) is proved in `Simple673/Kernel/Table.lean`. The three names `kTabArray`,
`kTabArray_size` and `kTabArray_sound` are the interface used by `Simple673/Local`.
-/
import Simple673.Kernel.Compute

namespace Simple673.Kernel

/-- The 8192 enclosures `Distinct839.Kernel.trigEncl j`, `j < H/2`, computed once. -/
def trigArr : Array Distinct839.Kernel.TrigEncl :=
  Array.ofFn (n := 8192) fun j => Distinct839.Kernel.trigEncl j

/-- `Distinct839.Kernel.trigEncl j`, read from `trigArr` when `j` is in range. -/
def trigCached (j : ℕ) : Distinct839.Kernel.TrigEncl :=
  if h : j < trigArr.size then trigArr[j] else Distinct839.Kernel.trigEncl j

/-- **The kernel table as an array**: `kTabArray[k] = kTab k` for `k ≤ tabR = 262143`. -/
def _root_.Simple673.kTabArray : Array ℕ :=
  Array.ofFn (n := tabR + 1) fun k => kTabWith trigCached k

/-- The table has `tabR + 1 = 262144` entries. -/
theorem _root_.Simple673.kTabArray_size : kTabArray.size = tabR + 1 := Array.size_ofFn

end Simple673.Kernel
