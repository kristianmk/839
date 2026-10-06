/-
Ceilings/Line/Range7.lean — second window: no certificate of range seven gives more than 67.357%.

`ceiling_line_range7`: for the window of `Simple673`, every pair-energy certificate `(x, b)` of
range seven for simple points with `x < 1` has `(2 - C - b)/(1 - x) < 0.67357` (the proof of the
67.35% theorem uses such a certificate, with the constant `0.67353…`). The hypothesis `0 ≤ b` of
the statement is not used: the weights of the mixture are normalised by the length.

Two periodic trial states of simple points, each with five points in a period: one of length
`7.04735` with gaps `1.03627`, `1.03627`, `1.96582`, `1.04317`, `1.96582`, and one of length
`8.04125` with gaps `1.04588`, `1.97681`, `1.04588`, `1.98634`, `1.98634`. Their range-seven pair
energies per period are bounded by `eUp` (kernel evaluation of `State.rangeUp`), and the mixture
with the weights `weights` has `0.6735660811…` points per unit length.
-/
import Ceilings.Line.Kernel

namespace Ceilings

namespace Line.Range7

/-- The two trial states. -/
def states : Fin 2 → State := ![
  ⟨[1, 1, 1, 1, 1],
    [103627 / 100000, 103627 / 100000, 98291 / 50000, 104317 / 100000, 98291 / 50000]⟩,
  ⟨[1, 1, 1, 1, 1],
    [26147 / 25000, 197681 / 100000, 26147 / 25000, 99317 / 50000, 99317 / 50000]⟩]

/-- The weights of the mixture (not normalised). -/
def weights : Fin 2 → ℚ := ![83773669370, 50939546858]

/-- Upper bounds for the range-seven pair energies per period. -/
def eUp : Fin 2 → ℚ := ![12817649379 / 1000000000000, 4314648299 / 500000000000]

theorem sep_ok : ∀ k, (states k).sepOK (17 / 20) = true := by decide +kernel

theorem simple_ok : ∀ k, (states k).simpleOK = true := by decide +kernel

theorem energy_ok : ∀ k, (states k).rangeUp k2 7 ≤ eUp k := by decide +kernel

theorem mix_ok : LineMixOK states weights eUp CloLineQ := by decide +kernel

theorem ratio_lt : mixM states weights / mixP states weights < 67357 / 100000 := by
  decide +kernel

end Line.Range7

open Line.Range7 in
/-- **Ceiling for certificates of range seven, simple points** (window of `Simple673`): the
constant of a pair-energy certificate of range seven is below `0.67357`. -/
theorem ceiling_line_range7 {x b : ℝ} (h : PairCert1 7 x b) (_hb : 0 ≤ b) (hx : x < 1) :
    (2 - energyCLine - b) / (1 - x) < 67357 / 100000 := by
  have h1 := Line.ceiling_of_range states weights eUp sep_ok simple_ok energy_ok mix_ok h hx
  have h2 : ((mixM states weights / mixP states weights : ℚ) : ℝ) < ((67357 / 100000 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr ratio_lt
  have h3 : ((67357 / 100000 : ℚ) : ℝ) = 67357 / 100000 := by norm_num
  rw [h3] at h2
  exact lt_of_le_of_lt h1 h2

end Ceilings
