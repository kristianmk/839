/-
Distinct839/Local/Soundness.lean — soundness of the checker for the local inequality.

Main results:

* `localInequality_of_check`: if `tab` is a sound table of lower bounds for `K²` and
  `checkAll tab = true`, then `LocalInequality` holds;
* `localInequality_of_chunks`: the same from the checks of the chunks `0, …, n - 1` at some
  depth, which can be evaluated separately (and in parallel).

Neither uses `native_decide`. The only facts about `K` that enter are the hypothesis `hsound`
and `0 ≤ K t ^ 2`.

Outline of the proof (files of `Distinct839/Local/`):

* `Checker`  — the executable checker (no Mathlib import, compiled to native code);
* `Basic`    — signed pairs, loops, array reads;
* `Potential`— the piecewise linear potentials: integer values on the grid, exact minima at
               end points and knots, affine supports, the bound for their negative parts;
* `Kernel`   — range minima of the table and affine supports of the kernel square;
* `Model`    — the inequality in grid units, pressure, clamping of a box to `∑ u ≤ R`;
* `Node`     — the label shortcut and the two lower bounds on a box;
* `Search`   — the tests on one box, the recursion, paths and chunks;
* `Bridge`   — from grid units to the statement of `Distinct839/Defs.lean`.
-/
import Distinct839.Local.Bridge

namespace Distinct839

/-- **Soundness of the branch-and-bound checker.** If `tab[k] / V ≤ K(t)²` on every cell
`[k/H, (k+1)/H]` of the table and the checker accepts the root box, then the seven-point local
inequality holds for all gaps `≥ 17/20` and all `128` labelings.

The hypothesis `hsize` is not needed: the checker reads the table with default `0` beyond its
end, which is a valid lower bound for `K²`. -/
theorem localInequality_of_check (tab : Array ℕ) (hsize : tab.size = tabR + 1)
    (hsound : ∀ (k : ℕ) (h : k < tab.size) (t : ℝ), (k : ℝ) / gridH ≤ t →
      t ≤ ((k : ℝ) + 1) / gridH → (tab[k] : ℝ) / scaleV ≤ K t ^ 2)
    (hcheck : checkAll tab = true) : LocalInequality := by
  have _ := hsize
  exact Local.localInequality_of_boxOK
    (Local.checkAll_sound tab (Local.tabOK_of_sound tab hsound) hcheck)

/-- Soundness of the chunked check: the chunks `i = 0, …, n - 1` at depth `depth` cover the
root box, so if each of them passes, the local inequality holds. -/
theorem localInequality_of_chunks (tab : Array ℕ) (hsize : tab.size = tabR + 1)
    (hsound : ∀ (k : ℕ) (h : k < tab.size) (t : ℝ), (k : ℝ) / gridH ≤ t →
      t ≤ ((k : ℝ) + 1) / gridH → (tab[k] : ℝ) / scaleV ≤ K t ^ 2)
    (depth n : ℕ) (hn : 0 < n)
    (hcheck : ∀ i < n, Local.checkChunk tab depth n i = true) : LocalInequality := by
  have _ := hsize
  exact Local.localInequality_of_boxOK
    (Local.checkChunks_sound tab (Local.tabOK_of_sound tab hsound) depth n hn hcheck)

end Distinct839
