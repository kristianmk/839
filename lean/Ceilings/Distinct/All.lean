/-
Ceilings/Distinct/All.lean — no pair-energy certificate gives 84% with the window of `Distinct839`.

`ceiling_all`: every pair-energy certificate `(x₁, x₂, b)` for all pairs, with `b ≥ 0` and
`2 - 2x₁ + x₂ > 0`, has `(3 - C + x₂ - x₁ - b)/(2 - 2x₁ + x₂) < 0.83998` (Proposition "ceiling"
of the paper, for certificates). By `PairCert.toAll` this covers the certificates of every
range (`ceiling_any_range`).

Three periodic trial states of period seven (multiplicities; gaps): six simple points and one
empty site; four simple points, a double point and a simple point; simple, simple, double, empty,
double, double, empty. For each state the pair energy per period of every range is bounded by
`eUp`: `State.allUp` evaluates the pairs inside a period and, for every ordered pair of points,
the sum over the next `N₀ = 30` periods, and bounds the rest by the telescoping tail from
`T₀ = 210` on. The mixture with the weights `weights` has `0.8399799907…` points per unit of
multiplicity.
-/
import Ceilings.Distinct.Kernel

namespace Ceilings

namespace Distinct.All

/-- The three trial states, all of period seven. -/
def states : Fin 3 → State := ![
  ⟨[1, 1, 1, 1, 1, 1],
    [104001 / 100000, 10213 / 10000, 10207 / 10000, 10213 / 10000, 104001 / 100000,
      46417 / 25000]⟩,
  ⟨[1, 1, 1, 1, 2, 1],
    [51563 / 50000, 50697 / 50000, 100497 / 100000, 104251 / 100000, 21263 / 20000,
      184417 / 100000]⟩,
  ⟨[1, 1, 2, 2, 2],
    [51043 / 50000, 105133 / 100000, 48541 / 25000, 108453 / 100000, 47541 / 25000]⟩]

/-- The weights of the mixture (not normalised). -/
def weights : Fin 3 → ℚ := ![17162866408, 108531410039, 17162866409]

/-- Upper bounds for the pair energies per period, all pairs. -/
def eUp : Fin 3 → ℚ :=
  ![75242376497 / 1000000000000, 47188450689 / 500000000000, 13176198917 / 200000000000]

/-- number of periods evaluated explicitly -/
def N₀ : Fin 3 → ℕ := fun _ => 30

/-- the tail bound `Q(t)² ≤ E²/t²` is used for `t ≥ T₀ = N₀ · 7` -/
def T₀ : Fin 3 → ℚ := fun _ => 210

theorem sep_ok : ∀ k, (states k).sepOK (17 / 20) = true := by decide +kernel

theorem T_ok : ∀ k, 6 < T₀ k := by decide +kernel

theorem all_ok : ∀ k, (states k).allOK (T₀ k) (N₀ k) = true := by decide +kernel

theorem energy_ok_0 : (states 0).allUp Q kI (E2gen aQ (T₀ 0)) (N₀ 0) ≤ eUp 0 := by
  decide +kernel

theorem energy_ok_1 : (states 1).allUp Q kI (E2gen aQ (T₀ 1)) (N₀ 1) ≤ eUp 1 := by
  decide +kernel

theorem energy_ok_2 : (states 2).allUp Q kI (E2gen aQ (T₀ 2)) (N₀ 2) ≤ eUp 2 := by
  decide +kernel

theorem energy_ok : ∀ k, (states k).allUp Q kI (E2gen aQ (T₀ k)) (N₀ k) ≤ eUp k := by
  intro k
  fin_cases k
  · exact energy_ok_0
  · exact energy_ok_1
  · exact energy_ok_2

theorem mix_ok : MixOK states weights eUp CloQ := by decide +kernel

theorem ratio_lt : mixL states weights / mixN states weights < 83998 / 100000 := by
  decide +kernel

end Distinct.All

open Distinct.All in
/-- **Ceiling for all pair-energy certificates** (window of `Distinct839`): the constant of a
pair-energy certificate is below `0.83998`; in particular it is below `84%`. -/
theorem ceiling_all {x₁ x₂ b : ℝ} (h : PairCertAll x₁ x₂ b) (hb : 0 ≤ b)
    (hD : 0 < 2 - 2 * x₁ + x₂) :
    (3 - energyC + x₂ - x₁ - b) / (2 - 2 * x₁ + x₂) < 83998 / 100000 := by
  have h1 := Distinct.ceiling_of_all states weights eUp T₀ N₀ sep_ok T_ok all_ok energy_ok
    mix_ok h hb hD
  have h2 : ((mixL states weights / mixN states weights : ℚ) : ℝ) < ((83998 / 100000 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr ratio_lt
  have h3 : ((83998 / 100000 : ℚ) : ℝ) = 83998 / 100000 := by norm_num
  rw [h3] at h2
  exact lt_of_le_of_lt h1 h2

/-- The weaker form `< 0.83999`. -/
theorem ceiling_all_83999 {x₁ x₂ b : ℝ} (h : PairCertAll x₁ x₂ b) (hb : 0 ≤ b)
    (hD : 0 < 2 - 2 * x₁ + x₂) :
    (3 - energyC + x₂ - x₁ - b) / (2 - 2 * x₁ + x₂) < 83999 / 100000 :=
  (ceiling_all h hb hD).trans (by norm_num)

/-- With this window no pair-energy certificate of any range gives `84%`. -/
theorem ceiling_any_range {r : ℕ} {x₁ x₂ b : ℝ} (h : PairCert r x₁ x₂ b) (hb : 0 ≤ b)
    (hD : 0 < 2 - 2 * x₁ + x₂) :
    (3 - energyC + x₂ - x₁ - b) / (2 - 2 * x₁ + x₂) < 83998 / 100000 :=
  ceiling_all h.toAll hb hD

end Ceilings
