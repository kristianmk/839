/-
Distinct839/Assembly/Constants.lean — the constants of the counting step.

With `c = clipC = 67/20`, `x = rewX`, `y = rewY`, `b = spanB`, `C₀ = energyC0`:

    ν = 2c − 3 − y + x,    μ = 2 − 2x + y,    q = (3 − C₀ + y − x − b)/μ = 1645064/1960733.

The per-class coefficient identities and inequalities of the certificate principle of the paper
are checked here by exact rational arithmetic.
-/
import Distinct839.Defs

noncomputable section

namespace Distinct839.Assembly

/-- `ν = 2c − 3 − y + x`, the coefficient of the count with multiplicity. -/
def nuC : ℝ := 2 * clipC - 3 - rewY + rewX

/-- `μ = 2 − 2x + y`, the coefficient of the count of distinct zeros. -/
def muC : ℝ := 2 - 2 * rewX + rewY

/-- The label of a multiplicity: `1 ↦ 0`, everything else (in practice `2`) `↦ 1`. -/
def labOf (m : ℕ) : Fin 2 := if m = 1 then 0 else 1

lemma labOf_one : labOf 1 = 0 := rfl

lemma labOf_two : labOf 2 = 1 := rfl

lemma rew_zero : rew 0 = rewX := by unfold rew; rw [if_pos rfl]

lemma rew_one : rew 1 = rewY := by unfold rew; rw [if_neg (by decide)]

lemma mulOf_labOf {m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ 2) : mulOf (labOf m) = m := by
  have h : m = 1 ∨ m = 2 := by omega
  rcases h with rfl | rfl
  · rw [labOf_one]; norm_num [mulOf]
  · rw [labOf_two]; norm_num [mulOf]

lemma clipC_pos : 0 < clipC := by unfold clipC; norm_num

lemma nuC_pos : 0 < nuC := by unfold nuC clipC rewY rewX; norm_num

lemma muC_pos : 0 < muC := by unfold muC rewY rewX; norm_num

lemma spanB_nonneg : 0 ≤ spanB := by unfold spanB alphaP; norm_num

lemma energyC0_pos : 0 < energyC0 := by unfold energyC0; norm_num

/-- `q·μ = 3 − C₀ + y − x − b`. -/
lemma qFinal_mul_muC : qFinal * muC = 3 - energyC0 + rewY - rewX - spanB := by
  unfold qFinal muC energyC0 rewY rewX spanB alphaP; norm_num

/-- `2c − ν = 3 + y − x`. -/
lemma two_clipC_sub_nuC : 2 * clipC - nuC = 3 + rewY - rewX := by unfold nuC; ring

/-- simple good zero: `ν + μ = 2c − 1 − x`. -/
lemma coeff_simple : nuC * 1 + muC = 2 * clipC * 1 - (1 ^ 2 + rewX) := by
  unfold nuC muC; ring

/-- double good zero: `2ν + μ = 4c − 4 − y`. -/
lemma coeff_double : nuC * 2 + muC = 2 * clipC * 2 - (2 ^ 2 + rewY) := by
  unfold nuC muC; ring

/-- on-line zero of multiplicity at least three: `3ν + μ ≥ c²` (`r_h ≥ 0` in the paper). -/
lemma coeff_triple : clipC ^ 2 ≤ nuC * 3 + muC := by
  unfold nuC muC clipC rewY rewX; norm_num

/-- off-line pair: `2ν + 2μ ≥ c²` (`r_k ≥ 0` in the paper). -/
lemma coeff_pair : clipC ^ 2 ≤ 2 * (nuC + muC) := by
  unfold nuC muC clipC rewY rewX; norm_num

end Distinct839.Assembly
