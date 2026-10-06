/-
Ceilings/Distinct/Range10.lean — no certificate of range ten gives more than 83.957%.

`ceiling_range10`: for the window of `Distinct839`, every pair-energy certificate `(x₁, x₂, b)` of
range ten (pairs at index distance at most ten, as in an inequality for eleven consecutive points)
with `b ≥ 0` and `2 - 2x₁ + x₂ > 0` has `(3 - C + x₂ - x₁ - b)/(2 - 2x₁ + x₂) < 0.83957`.

Three periodic trial states (multiplicities; gaps): simple, simple, double, empty, double, double,
empty; four simple points, a double point and a simple point; seven simple points and one empty
site. Their range-ten pair energies per period are bounded by `eUp` (kernel evaluation of
`State.rangeUp`), and the mixture with the weights `weights` has `0.839562813…` points per unit of
multiplicity.
-/
import Ceilings.Distinct.Kernel

namespace Ceilings

namespace Distinct.Range10

/-- The three trial states. -/
def states : Fin 3 → State := ![
  ⟨[1, 1, 2, 2, 2],
    [51257 / 50000, 9517 / 5000, 27217 / 25000, 48657 / 25000, 52779 / 50000]⟩,
  ⟨[1, 1, 1, 1, 2, 1],
    [25947 / 25000, 102083 / 100000, 101201 / 100000, 52441 / 50000, 21387 / 20000, 5774 / 3125]⟩,
  ⟨[1, 1, 1, 1, 1, 1, 1],
    [52203 / 50000, 25681 / 25000, 12821 / 12500, 12821 / 12500, 25681 / 25000, 52203 / 50000,
      18589 / 10000]⟩]

/-- The weights of the mixture (not normalised). -/
def weights : Fin 3 → ℚ := ![14620571742, 116575471289, 9572446714]

/-- Upper bounds for the range-ten pair energies per period. -/
def eUp : Fin 3 → ℚ :=
  ![61197827451 / 1000000000000, 21664323099 / 250000000000, 3483846223 / 40000000000]

theorem sep_ok : ∀ k, (states k).sepOK (17 / 20) = true := by decide +kernel

theorem energy_ok : ∀ k, (states k).rangeUp k2 10 ≤ eUp k := by decide +kernel

theorem mix_ok : MixOK states weights eUp CloQ := by decide +kernel

theorem ratio_lt : mixL states weights / mixN states weights < 83957 / 100000 := by
  decide +kernel

end Distinct.Range10

open Distinct.Range10 in
/-- **Ceiling for certificates of range ten** (window of `Distinct839`): the constant of a
pair-energy certificate of range ten is below `0.83957`. -/
theorem ceiling_range10 {x₁ x₂ b : ℝ} (h : PairCert 10 x₁ x₂ b) (hb : 0 ≤ b)
    (hD : 0 < 2 - 2 * x₁ + x₂) :
    (3 - energyC + x₂ - x₁ - b) / (2 - 2 * x₁ + x₂) < 83957 / 100000 := by
  have h1 := Distinct.ceiling_of_range states weights eUp sep_ok energy_ok mix_ok h hb hD
  have h2 : ((mixL states weights / mixN states weights : ℚ) : ℝ) < ((83957 / 100000 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr ratio_lt
  have h3 : ((83957 / 100000 : ℚ) : ℝ) = 83957 / 100000 := by norm_num
  rw [h3] at h2
  exact lt_of_le_of_lt h1 h2

end Ceilings
