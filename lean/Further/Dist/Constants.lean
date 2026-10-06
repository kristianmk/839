/-
Further/Dist/Constants.lean — the constants of the counting step for "simple or on the line".

The Gram part is that of `Distinct839` (zeros on the line of multiplicity one and two), with the
clipping level `c = clipC = 67/20`, the rewards `x = rewX`, `y = rewY`, the span cost
`b = spanB` and the energy constant `C₀ = energyC0` of `Distinct839/Defs.lean`. New is the second
level `t = 27/8 ≥ c` of the threshold inequality with two parameters
(`Further/Threshold.lean`), which is applied to the zeros outside the Gram part.

Per unit of multiplicity, a zero that is simple or on the line is worth at least `e₁ = 1 + x`,
and a zero off the line of multiplicity at least two is worth at least `e₀ = 2t − t²/4`:

    q = (e₀ − C₀ − b)/(e₀ − e₁) = 3376433/3797325.

The per-class inequalities are checked here by exact rational arithmetic. The binding ones are
the pair of simple zeros off the line, `t² ≤ 2(2t − e₁)` (`11.390625 ≤ 11.3913`), and the pair of
double zeros off the line, `t² = 4(2t − e₀)`.
-/
import Distinct839.Assembly.Constants

noncomputable section

namespace Further.Dist

open Distinct839 (clipC rewX rewY spanB alphaP energyC0)

/-- the second level `t = 27/8` of the threshold inequality -/
def tLev : ℝ := 27 / 8

/-- `e₁ = 1 + x`: the value, per unit of multiplicity, of a zero that is simple or on the line. -/
def e1C : ℝ := 1 + rewX

/-- `e₀ = 2t − t²/4 = 999/256`: the value, per unit of multiplicity, of a zero off the line of
multiplicity at least two. -/
def e0C : ℝ := 2 * tLev - tLev ^ 2 / 4

/-- the final constant `(e₀ − C₀ − b)/(e₀ − e₁) = 3376433/3797325` -/
def qSL : ℝ := 3376433 / 3797325

lemma tLev_pos : 0 < tLev := by unfold tLev; norm_num

/-- `c ≤ t`. -/
lemma clipC_le_tLev : clipC ≤ tLev := by unfold clipC tLev; norm_num

lemma e0C_eq : e0C = 999 / 256 := by unfold e0C tLev; norm_num

/-- `2t − e₁ > 0`: the cost, per unit of multiplicity, of a zero that is simple or on the line. -/
lemma two_tLev_sub_e1C_pos : 0 < 2 * tLev - e1C := by unfold tLev e1C rewX; norm_num

/-- `2t − e₀ = t²/4 > 0`. -/
lemma two_tLev_sub_e0C_pos : 0 < 2 * tLev - e0C := by unfold e0C tLev; norm_num

/-- `e₀ − e₁ > 0`: the coefficient of the count of zeros that are simple or on the line. -/
lemma e0C_sub_e1C_pos : 0 < e0C - e1C := by unfold e0C e1C tLev rewX; norm_num

/-- simple good zero: `2t − 1 − x = 2t − e₁`. -/
lemma coeff_simple : 2 * tLev * 1 - (1 ^ 2 + rewX) = (2 * tLev - e1C) * 1 := by
  unfold e1C; ring

/-- double good zero: `4t − 4 − y ≤ 2(2t − e₁)`, that is `4 + y ≥ 2e₁`. -/
lemma coeff_double : 2 * tLev * 2 - (2 ^ 2 + rewY) ≤ (2 * tLev - e1C) * 2 := by
  unfold e1C tLev rewX rewY; norm_num

/-- on-line zero of multiplicity at least three outside the Gram part: `t² ≤ 3(2t − e₁)`. -/
lemma coeff_triple : tLev ^ 2 ≤ (2 * tLev - e1C) * 3 := by
  unfold e1C tLev rewX; norm_num

/-- off-line pair of simple zeros: `t² ≤ 2(2t − e₁)`, that is `4t − t² ≥ 2e₁`. -/
lemma coeff_pair_simple : tLev ^ 2 ≤ 2 * (2 * tLev - e1C) := by
  unfold e1C tLev rewX; norm_num

/-- off-line pair of zeros of multiplicity two: `t² = 4(2t − e₀)`. -/
lemma coeff_pair_multiple : tLev ^ 2 = 4 * (2 * tLev - e0C) := by
  unfold e0C; ring

/-- `q·(e₀ − e₁) = e₀ − C₀ − b`. -/
lemma qSL_mul : qSL * (e0C - e1C) = e0C - energyC0 - spanB := by
  unfold qSL e0C e1C tLev energyC0 rewX spanB alphaP; norm_num

end Further.Dist
