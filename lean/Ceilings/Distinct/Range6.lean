/-
Ceilings/Distinct/Range6.lean — no certificate of range six gives more than 83.916%.

`ceiling_range6`: for the window of `Distinct839`, every pair-energy certificate `(x₁, x₂, b)` of
range six (pairs at index distance at most six, as in an inequality for seven consecutive points)
with `b ≥ 0` and `2 - 2x₁ + x₂ > 0` has `(3 - C + x₂ - x₁ - b)/(2 - 2x₁ + x₂) < 0.83916`
(Proposition "six" of the paper; the proof of the 83.90% theorem uses such a certificate, with the
constant `0.83900…`).

Three periodic trial states (multiplicities; gaps): the lattice of simple points with spacing
`1.02532`; six simple points and one empty site, period `7.07365`; simple, simple, double, empty,
double, double, empty, period `7.03513`. Their range-six pair energies per period are bounded by
`eUp` (kernel evaluation of `State.rangeUp`), and the mixture with the weights `weights` has
`0.839151809…` points per unit of multiplicity.
-/
import Ceilings.Distinct.Kernel

namespace Ceilings

namespace Distinct.Range6

/-- The three trial states. -/
def states : Fin 3 → State := ![
  ⟨[1], [25633 / 25000]⟩,
  ⟨[1, 1, 1, 1, 1, 1],
    [26317 / 25000, 103483 / 100000, 5173 / 5000, 103483 / 100000, 26317 / 25000,
      186403 / 100000]⟩,
  ⟨[1, 1, 2, 2, 2],
    [5143 / 5000, 52939 / 50000, 195107 / 100000, 54553 / 50000, 95281 / 50000]⟩]

/-- The weights of the mixture (not normalised). -/
def weights : Fin 3 → ℚ := ![328442951348, 40438090226, 53616063408]

/-- Upper bounds for the range-six pair energies per period. -/
def eUp : Fin 3 → ℚ :=
  ![3237832179 / 200000000000, 63558663623 / 1000000000000, 58213357439 / 1000000000000]

theorem sep_ok : ∀ k, (states k).sepOK (17 / 20) = true := by decide +kernel

theorem energy_ok : ∀ k, (states k).rangeUp k2 6 ≤ eUp k := by decide +kernel

theorem mix_ok : MixOK states weights eUp CloQ := by decide +kernel

theorem ratio_lt : mixL states weights / mixN states weights < 83916 / 100000 := by
  decide +kernel

end Distinct.Range6

open Distinct.Range6 in
/-- **Ceiling for certificates of range six** (window of `Distinct839`): the constant of a
pair-energy certificate of range six is below `0.83916`. -/
theorem ceiling_range6 {x₁ x₂ b : ℝ} (h : PairCert 6 x₁ x₂ b) (hb : 0 ≤ b)
    (hD : 0 < 2 - 2 * x₁ + x₂) :
    (3 - energyC + x₂ - x₁ - b) / (2 - 2 * x₁ + x₂) < 83916 / 100000 := by
  have h1 := Distinct.ceiling_of_range states weights eUp sep_ok energy_ok mix_ok h hb hD
  have h2 : ((mixL states weights / mixN states weights : ℚ) : ℝ) < ((83916 / 100000 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr ratio_lt
  have h3 : ((83916 / 100000 : ℚ) : ℝ) = 83916 / 100000 := by norm_num
  rw [h3] at h2
  exact lt_of_le_of_lt h1 h2

end Ceilings
