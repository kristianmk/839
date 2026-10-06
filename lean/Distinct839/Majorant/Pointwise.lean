/-
Distinct839/Majorant/Pointwise.lean — the pointwise majorant `fCos ≤ gMaj` on `[-1/2, 1/2]`.

Both functions are even, so it suffices to treat `[0, 1/2]`. This interval is cut into 42
subintervals (finer near `1/2`, where the margin `gMaj - fCos` is smallest, about `5 · 10⁻⁴`),
and the rational test `leafOK` of `Checker.lean` is evaluated on each of them by the kernel.
-/
import Distinct839.Spec
import Distinct839.Majorant.Checker

open Real

namespace Distinct839.Majorant

/-- The breakpoints after `0` of the subdivision of `[0, 1/2]`. -/
def majorantBreaks : List ℚ :=
  [1/128, 1/64, 3/128, 1/32, 3/64, 1/16, 5/64, 3/32, 1/8, 9/64, 5/32, 11/64, 3/16, 7/32, 1/4,
   9/32, 19/64, 5/16, 41/128, 21/64, 11/32, 23/64, 3/8, 13/32, 7/16, 29/64, 15/32, 61/128, 31/64,
   125/256, 63/128, 253/512, 127/256, 509/1024, 255/512, 1021/2048, 511/1024, 2045/4096,
   1023/2048, 2047/4096, 4095/8192, 1/2]

/-- The rational test succeeds on every subinterval (kernel computation in `ℚ`). -/
theorem majorantBreaks_ok : checkAll (0 :: majorantBreaks) = true := by decide +kernel

theorem majorantBreaks_last : (1 / 2 : ℚ) ∈ majorantBreaks := by decide +kernel

/-- `fCos ≤ gMaj` on `[0, 1/2]`. -/
theorem fCos_le_gMaj_of_nonneg {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) : fCos u ≤ gMaj u := by
  refine checkAll_sound majorantBreaks 0 majorantBreaks_ok (1 / 2) majorantBreaks_last u ?_ ?_
  · rw [Rat.cast_zero]; exact h0
  · have e : (((1 / 2 : ℚ)) : ℝ) = 1 / 2 := by norm_num
    rw [e]; exact h1

end Distinct839.Majorant

namespace Distinct839

open Majorant

/-- **The pointwise majorant**: `fCos u ≤ gMaj u` for `|u| ≤ 1/2`. -/
theorem majorantPointwise : MajorantPointwise := by
  intro u hu
  rcases le_total 0 u with h | h
  · exact fCos_le_gMaj_of_nonneg h (le_trans (le_abs_self u) hu)
  · have h' := fCos_le_gMaj_of_nonneg (u := -u) (by linarith)
      (le_trans (neg_le_abs u) hu)
    rwa [fCos_neg, gMaj_neg] at h'

end Distinct839
