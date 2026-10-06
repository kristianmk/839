/-
Line889/Assembly/Constants.lean — the constants of the counting step for "simple or on the line".

The Gram part consists of the simple zeros on the critical line, with the clipping level
`c = clipC = 2`, the site reward `x = rewX`, the span cost `b = spanB = 6α` and the energy
constant `C₀ = energyC0` of `Line889/Defs.lean`. The zeros outside the Gram part enter through
the threshold inequality with two levels (`Further/Threshold.lean`), at the second level
`t = tLev = 27/8 ≥ c`.

Per unit of multiplicity, a zero that is simple or on the line is worth at least `e₁ = 1 + x`
(`e1C`, defined here), and a zero off the line of multiplicity at least two is worth at least
`e₀ = e0C = 2t − t²/4 = 999/256`:

    q = (e₀ − C₀ − b)/(e₀ − e₁) = qFinal = 50652159/56956375.

The counting step of `Line889/Assembly/Block.lean` needs two relations between the levels and the
reward, which are checked here by exact rational arithmetic:

* `coeff_two`: `t² ≤ 2(2t − e₁)`, that is `4t − t² ≥ 2 + 2x` (`135/64 = 2.109375 ≥ 2.10905`; it
  holds for `x ≤ 7/128`). It is used for a zero on the line of multiplicity at least two outside
  the Gram part and for a pair of simple zeros off the line;
* `coeff_pair_multiple`: `t² = 4(2t − e₀)`, the definition of `e₀`. It is used for a pair of zeros
  off the line of multiplicity at least two.

`tLev`, `e0C` and `qFinal` are definitions of `Line889/Defs.lean`; the values `e0C = 999/256` and
`qFinal = (e0C − energyC0 − spanB)/(e0C − 1 − rewX)` are also recorded in `Line889/Compose.lean`
(`e0C_eq`, `qFinal_eq`, `levels_ok`).
-/
import Line889.Defs

noncomputable section

namespace Line889.Assembly

/-- `e₁ = 1 + x`: the value, per unit of multiplicity, of a zero that is simple or on the line. -/
def e1C : ℝ := 1 + rewX

lemma clipC_pos : 0 < clipC := by unfold clipC; norm_num

lemma tLev_pos : 0 < tLev := by unfold tLev; norm_num

/-- `c ≤ t`: the condition on the two levels of the threshold inequality. -/
lemma clipC_le_tLev : clipC ≤ tLev := by unfold clipC tLev; norm_num

/-- `2t − e₁ > 0`: the cost, per unit of multiplicity, of a zero that is simple or on the line. -/
lemma two_tLev_sub_e1C_pos : 0 < 2 * tLev - e1C := by unfold tLev e1C rewX; norm_num

/-- `2t − e₀ = t²/4 > 0`: the cost, per unit of multiplicity, of a zero off the line of
multiplicity at least two. -/
lemma two_tLev_sub_e0C_pos : 0 < 2 * tLev - e0C := by unfold e0C tLev; norm_num

/-- `e₀ − e₁ > 0`: the coefficient of the count of zeros that are simple or on the line. -/
lemma e0C_sub_e1C_pos : 0 < e0C - e1C := by unfold e0C e1C tLev rewX; norm_num

/-- A zero on the line of multiplicity at least two outside the Gram part, and a pair of simple
zeros off the line: `t² ≤ 2(2t − e₁)`, that is `4t − t² ≥ 2 + 2x`. -/
lemma coeff_two : tLev ^ 2 ≤ 2 * (2 * tLev - e1C) := by unfold e1C tLev rewX; norm_num

/-- A pair of zeros off the line of multiplicity two: `t² = 4(2t − e₀)`. -/
lemma coeff_pair_multiple : tLev ^ 2 = 4 * (2 * tLev - e0C) := by unfold e0C; ring

/-- `q·(e₀ − e₁) = e₀ − C₀ − b`. -/
lemma qFinal_mul : qFinal * (e0C - e1C) = e0C - energyC0 - spanB := by
  unfold qFinal e0C e1C tLev energyC0 rewX spanB alphaP; norm_num

lemma rewX_nonneg : 0 ≤ rewX := by unfold rewX; norm_num

lemma spanB_nonneg : 0 ≤ spanB := by unfold spanB alphaP; norm_num

lemma energyC0_pos : 0 < energyC0 := by unfold energyC0; norm_num

end Line889.Assembly
