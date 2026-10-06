/-
Line889/Majorant/Pointwise.lean — the pointwise majorant `fCos ≤ gMaj` on `[-1/2, 1/2]`.

Both functions are even, so it suffices to treat `[0, 1/2]`. This interval is cut into 28
subintervals (finer near `1/2`, where the margin `gMaj - fCos` is smallest, about `2.04 · 10⁻³`;
on `[0, 2/5]` it is at least `0.09`), and the rational test `leafOK` of `Checker.lean` is evaluated
on each of them by the kernel. The subdivision is the dyadic one on which the test holds with
margin at least `10⁻⁴`; the smallest margin of the test is `6.85 · 10⁻⁴`, on the subinterval
`[127/256, 255/512]`.

The file follows `Simple673/Majorant/Pointwise.lean` and `Distinct839/Majorant/Pointwise.lean`,
with a new list of breakpoints.
-/
import Line889.Spec
import Line889.Majorant.Checker

open Real

namespace Line889.Majorant

/-- The breakpoints after `0` of the subdivision of `[0, 1/2]`. -/
def majorantBreaks : List ℚ :=
  [1/64, 1/32, 3/64, 1/16, 3/32, 1/8, 5/32, 3/16, 7/32, 1/4, 9/32, 5/16, 11/32, 3/8, 13/32,
   7/16, 29/64, 15/32, 61/128, 31/64, 125/256, 63/128, 253/512, 127/256, 255/512, 511/1024,
   1023/2048, 1/2]

/-- The rational test succeeds on every subinterval (kernel computation in `ℚ`). -/
theorem majorantBreaks_ok : checkAll (0 :: majorantBreaks) = true := by decide +kernel

theorem majorantBreaks_last : (1 / 2 : ℚ) ∈ majorantBreaks := by decide +kernel

/-- `fCos ≤ gMaj` on `[0, 1/2]`. -/
theorem fCos_le_gMaj_of_nonneg {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) : fCos u ≤ gMaj u := by
  refine checkAll_sound majorantBreaks 0 majorantBreaks_ok (1 / 2) majorantBreaks_last u ?_ ?_
  · rw [Rat.cast_zero]; exact h0
  · have e : (((1 / 2 : ℚ)) : ℝ) = 1 / 2 := by norm_num
    rw [e]; exact h1

end Line889.Majorant

namespace Line889

open Majorant

/-- **The pointwise majorant**: `fCos u ≤ gMaj u` for `|u| ≤ 1/2`. -/
theorem majorantPointwise : MajorantPointwise := by
  intro u hu
  rcases le_total 0 u with h | h
  · exact fCos_le_gMaj_of_nonneg h (le_trans (le_abs_self u) hu)
  · have h' := fCos_le_gMaj_of_nonneg (u := -u) (by linarith)
      (le_trans (neg_le_abs u) hu)
    rwa [fCos_neg, gMaj_neg] at h'

end Line889
