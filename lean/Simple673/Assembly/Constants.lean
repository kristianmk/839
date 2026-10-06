/-
Simple673/Assembly/Constants.lean — the constants of the counting step.

With `c = clipC = 2`, `x₁ = rewX = 8722·10⁻⁶`, `b = spanB = 7α = 4389·10⁻⁶` and
`C₀ = energyC0 = 6639737/5000000`:

    q = qFinal = (2 − C₀ − b)/(1 − x₁) = 1669159/2478195 = 0.67353…

At clipping level `2` the threshold inequality has the coefficients `2c = 4` (trace) and
`c² = 4` (each positive eigenvalue of the remainder); see `Simple673/Assembly/Block.lean` for
the counting step. The identity for `q` and the sign facts used in the assembly are checked here
by exact rational arithmetic.
-/
import Simple673.Defs

noncomputable section

namespace Simple673.Assembly

lemma clipC_pos : 0 < clipC := by unfold clipC; norm_num

/-- `2c = 4`: the coefficient of the trace in the threshold inequality. -/
lemma two_clipC : 2 * clipC = 4 := by unfold clipC; norm_num

/-- `c² = 4`: the cost of a positive eigenvalue of the remainder. -/
lemma clipC_sq : clipC ^ 2 = 4 := by unfold clipC; norm_num

lemma rewX_nonneg : 0 ≤ rewX := by unfold rewX; norm_num

/-- `1 − x₁ > 0`: the coefficient of the count of simple zeros on the line. -/
lemma one_sub_rewX_pos : 0 < 1 - rewX := by unfold rewX; norm_num

lemma spanB_nonneg : 0 ≤ spanB := by unfold spanB alphaP; norm_num

lemma energyC0_pos : 0 < energyC0 := by unfold energyC0; norm_num

/-- `q·(1 − x₁) = 2 − C₀ − b`, exactly: both sides are `1669159/2500000`. -/
lemma qFinal_mul : qFinal * (1 - rewX) = 2 - energyC0 - spanB := by
  unfold qFinal energyC0 rewX spanB alphaP; norm_num

end Simple673.Assembly
