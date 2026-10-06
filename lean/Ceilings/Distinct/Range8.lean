/-
Ceilings/Distinct/Range8.lean — no certificate of range eight gives more than 83.943%.

`ceiling_range8`: for the window of `Distinct839`, every pair-energy certificate `(x₁, x₂, b)` of
range eight (pairs at index distance at most eight, as in an inequality for nine consecutive points)
with `b ≥ 0` and `2 - 2x₁ + x₂ > 0` has `(3 - C + x₂ - x₁ - b)/(2 - 2x₁ + x₂) < 0.83943`.

Three periodic trial states (multiplicities; gaps): simple, simple, double, empty, double, double,
empty; four simple points, a double point and a simple point; seven simple points and one empty
site. Their range-eight pair energies per period are bounded by `eUp` (kernel evaluation of
`State.rangeUp`), and the mixture with the weights `weights` has `0.839422262…` points per unit of
multiplicity.
-/
import Ceilings.Distinct.Kernel

namespace Ceilings

namespace Distinct.Range8

/-- The three trial states. -/
def states : Fin 3 → State := ![
  ⟨[1, 1, 2, 2, 2],
    [2053 / 2000, 190489 / 100000, 108977 / 100000, 38939 / 20000, 26417 / 25000]⟩,
  ⟨[1, 1, 1, 1, 2, 1],
    [103957 / 100000, 102343 / 100000, 25373 / 25000, 105091 / 100000, 21417 / 20000,
      184713 / 100000]⟩,
  ⟨[1, 1, 1, 1, 1, 1, 1],
    [104611 / 100000, 103003 / 100000, 51433 / 50000, 51433 / 50000, 103003 / 100000,
      104611 / 100000, 185879 / 100000]⟩]

/-- The weights of the mixture (not normalised). -/
def weights : Fin 3 → ℚ := ![13144148305, 121145292173, 6689966905]

/-- Upper bounds for the range-eight pair energies per period. -/
def eUp : Fin 3 → ℚ :=
  ![11996691389 / 200000000000, 84167603039 / 1000000000000, 84386633381 / 1000000000000]

theorem sep_ok : ∀ k, (states k).sepOK (17 / 20) = true := by decide +kernel

theorem energy_ok : ∀ k, (states k).rangeUp k2 8 ≤ eUp k := by decide +kernel

theorem mix_ok : MixOK states weights eUp CloQ := by decide +kernel

theorem ratio_lt : mixL states weights / mixN states weights < 83943 / 100000 := by
  decide +kernel

end Distinct.Range8

open Distinct.Range8 in
/-- **Ceiling for certificates of range eight** (window of `Distinct839`): the constant of a
pair-energy certificate of range eight is below `0.83943`. -/
theorem ceiling_range8 {x₁ x₂ b : ℝ} (h : PairCert 8 x₁ x₂ b) (hb : 0 ≤ b)
    (hD : 0 < 2 - 2 * x₁ + x₂) :
    (3 - energyC + x₂ - x₁ - b) / (2 - 2 * x₁ + x₂) < 83943 / 100000 := by
  have h1 := Distinct.ceiling_of_range states weights eUp sep_ok energy_ok mix_ok h hb hD
  have h2 : ((mixL states weights / mixN states weights : ℚ) : ℝ) < ((83943 / 100000 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr ratio_lt
  have h3 : ((83943 / 100000 : ℚ) : ℝ) = 83943 / 100000 := by norm_num
  rw [h3] at h2
  exact lt_of_le_of_lt h1 h2

end Ceilings
