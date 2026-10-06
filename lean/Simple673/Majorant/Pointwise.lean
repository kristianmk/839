/-
Simple673/Majorant/Pointwise.lean — the pointwise majorant `fCos ≤ gMaj` on `[-1/2, 1/2]`.

Both functions are even, so it suffices to treat `[0, 1/2]`. This interval is cut into 14
subintervals, and the rational test `leafOK` of `Checker.lean` is evaluated on each of them by the
kernel. The margin `gMaj - fCos` is smallest at `u = 1/2`, where it is `0.0516…`; on
`[0, 15/32]` it is at least `0.11`. The test bounds both functions on a subinterval by their
values at the midpoint and a Lipschitz term, so what it loses grows with the length of the
subinterval. The subdivision is the dyadic one obtained by halving an interval until the test
holds on it: the lengths are `1/16` on `[0, 3/16]`, `1/32` on `[3/16, 15/32]` and `1/64` on
`[15/32, 1/2]`. The smallest margin of the test (`γ · hLow² - fUp`) is `1.09 · 10⁻²`, on the last
subinterval.

The file follows `Distinct839/Majorant/Pointwise.lean`, with the list of breakpoints for the
second window.
-/
import Simple673.Spec
import Simple673.Majorant.Checker

open Real

namespace Simple673.Majorant

/-- The breakpoints after `0` of the subdivision of `[0, 1/2]`. -/
def majorantBreaks : List ℚ :=
  [1/16, 1/8, 3/16, 7/32, 1/4, 9/32, 5/16, 11/32, 3/8, 13/32, 7/16, 15/32, 31/64, 1/2]

/-- The rational test succeeds on every subinterval (kernel computation in `ℚ`). -/
theorem majorantBreaks_ok : checkAll (0 :: majorantBreaks) = true := by decide +kernel

theorem majorantBreaks_last : (1 / 2 : ℚ) ∈ majorantBreaks := by decide +kernel

/-- `fCos ≤ gMaj` on `[0, 1/2]`. -/
theorem fCos_le_gMaj_of_nonneg {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) : fCos u ≤ gMaj u := by
  refine checkAll_sound majorantBreaks 0 majorantBreaks_ok (1 / 2) majorantBreaks_last u ?_ ?_
  · rw [Rat.cast_zero]; exact h0
  · have e : (((1 / 2 : ℚ)) : ℝ) = 1 / 2 := by norm_num
    rw [e]; exact h1

end Simple673.Majorant

namespace Simple673

open Majorant

/-- **The pointwise majorant**: `fCos u ≤ gMaj u` for `|u| ≤ 1/2`. -/
theorem majorantPointwise : MajorantPointwise := by
  intro u hu
  rcases le_total 0 u with h | h
  · exact fCos_le_gMaj_of_nonneg h (le_trans (le_abs_self u) hu)
  · have h' := fCos_le_gMaj_of_nonneg (u := -u) (by linarith)
      (le_trans (neg_le_abs u) hu)
    rwa [fCos_neg, gMaj_neg] at h'

end Simple673
