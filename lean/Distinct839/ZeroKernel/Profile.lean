/-
Distinct839/ZeroKernel/Profile.lean — elementary facts about the profile and the kernel.

The cosine polynomial `fCos = 1 + ∑ a_j cos(2π j u)` satisfies `|fCos - 1| ≤ ∑ |a_j| = 0.321589`,
so the profile `vProf = (2/5) fCos` is even, continuous and takes values in `(0, 1)`. The majorant
`gMaj` is nonnegative, and the kernel `K` (a combination of shifted sincs) satisfies `K 0 = 1` and
`|K| ≤ 2`. These are the only properties of the window that the zero side uses, apart from the
integral formula for `K` and the majorant statements, which are hypotheses of `gramData`.
-/
import Distinct839.Spec2

open scoped BigOperators
open Real

noncomputable section

namespace Distinct839.ZeroKernel

/-! ## The cosine polynomial -/

/-- The six window coefficients as rational numbers. -/
lemma aC_vals : aC 0 = 193305 / 1000000 ∧ aC 1 = -23105 / 1000000 ∧ aC 2 = 29166 / 1000000 ∧
    aC 3 = 13952 / 1000000 ∧ aC 4 = -21009 / 1000000 ∧ aC 5 = 41052 / 1000000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [aC, aInt]

/-- `fCos` written out. -/
lemma fCos_eq (u : ℝ) :
    fCos u = 1 + (193305 / 1000000 * Real.cos (2 * π * 1 * u)
      - 23105 / 1000000 * Real.cos (2 * π * 2 * u)
      + 29166 / 1000000 * Real.cos (2 * π * 3 * u)
      + 13952 / 1000000 * Real.cos (2 * π * 4 * u)
      - 21009 / 1000000 * Real.cos (2 * π * 5 * u)
      + 41052 / 1000000 * Real.cos (2 * π * 6 * u)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := aC_vals
  simp only [fCos, Fin.sum_univ_six, h0, h1, h2, h3, h4, h5]
  norm_num
  ring

/-- `|fCos u - 1| ≤ ∑ |a_j|`. -/
lemma abs_fCos_sub_one_le (u : ℝ) : |fCos u - 1| ≤ 321589 / 1000000 := by
  rw [fCos_eq, abs_le]
  have h1 := Real.cos_le_one (2 * π * 1 * u)
  have h2 := Real.cos_le_one (2 * π * 2 * u)
  have h3 := Real.cos_le_one (2 * π * 3 * u)
  have h4 := Real.cos_le_one (2 * π * 4 * u)
  have h5 := Real.cos_le_one (2 * π * 5 * u)
  have h6 := Real.cos_le_one (2 * π * 6 * u)
  have g1 := Real.neg_one_le_cos (2 * π * 1 * u)
  have g2 := Real.neg_one_le_cos (2 * π * 2 * u)
  have g3 := Real.neg_one_le_cos (2 * π * 3 * u)
  have g4 := Real.neg_one_le_cos (2 * π * 4 * u)
  have g5 := Real.neg_one_le_cos (2 * π * 5 * u)
  have g6 := Real.neg_one_le_cos (2 * π * 6 * u)
  constructor <;> linarith

lemma fCos_pos (u : ℝ) : 0 < fCos u := by
  have h := (abs_le.mp (abs_fCos_sub_one_le u)).1
  linarith

lemma fCos_le (u : ℝ) : fCos u ≤ 2 := by
  have h := (abs_le.mp (abs_fCos_sub_one_le u)).2
  linarith

lemma fCos_even (u : ℝ) : fCos (-u) = fCos u := by
  simp only [fCos, mul_neg, Real.cos_neg]

lemma fCos_continuous : Continuous fCos := by
  unfold fCos
  fun_prop

/-! ## The profile -/

lemma vProf_even (s : ℝ) : vProf (-s) = vProf s := by
  simp only [vProf, fCos_even]

lemma vProf_pos (s : ℝ) : 0 < vProf s := by
  have := fCos_pos s
  unfold vProf
  positivity

lemma vProf_nonneg (s : ℝ) : 0 ≤ vProf s := (vProf_pos s).le

lemma vProf_le_one (s : ℝ) : vProf s ≤ 1 := by
  have := fCos_le s
  unfold vProf
  linarith

lemma abs_vProf_le_one (s : ℝ) : |vProf s| ≤ 1 := by
  rw [abs_of_nonneg (vProf_nonneg s)]
  exact vProf_le_one s

lemma vProf_continuous : Continuous vProf := by
  unfold vProf
  exact continuous_const.mul fCos_continuous

/-! ## The majorant and the kernel -/

lemma gMaj_nonneg (u : ℝ) : 0 ≤ gMaj u := by
  unfold gMaj gammaM
  positivity

/-- `sincN` vanishes at the nonzero integers `j + 1`. -/
lemma sincN_nat_succ (j : ℕ) : sincN ((j : ℝ) + 1) = 0 := by
  have hne : π * ((j : ℝ) + 1) ≠ 0 := by positivity
  rw [sincN, Real.sinc_of_ne_zero hne]
  have : Real.sin (π * ((j : ℝ) + 1)) = 0 := by
    have h := Real.sin_nat_mul_pi (j + 1)
    rw [mul_comm]
    push_cast at h
    exact h
  rw [this, zero_div]

lemma sincN_neg (t : ℝ) : sincN (-t) = sincN t := by
  simp only [sincN, mul_neg, Real.sinc_neg]

lemma abs_sincN_le_one (t : ℝ) : |sincN t| ≤ 1 := Real.abs_sinc_le_one _

/-- `K 0 = 1`. -/
lemma K_zero : K 0 = 1 := by
  unfold K
  have h0 : sincN 0 = 1 := by simp [sincN]
  have hterm : ∀ j : Fin 6,
      aC j / 2 * (sincN (0 - (((j : ℕ) : ℝ) + 1)) + sincN (0 + (((j : ℕ) : ℝ) + 1))) = 0 := by
    intro j
    rw [zero_sub, zero_add, sincN_neg, sincN_nat_succ, add_zero, mul_zero]
  rw [h0, Finset.sum_eq_zero fun j _ => hterm j, add_zero]

/-- `|K| ≤ 2`: the sincs are bounded by `1` and `∑ |a_j| < 1`. -/
lemma abs_K_le (t : ℝ) : |K t| ≤ 2 := by
  unfold K
  have hs : ∀ x : ℝ, |sincN x| ≤ 1 := abs_sincN_le_one
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := aC_vals
  simp only [Fin.sum_univ_six, h0, h1, h2, h3, h4, h5]
  norm_num
  have a0 := abs_le.mp (hs t)
  have a1 := abs_le.mp (hs (t - 1))
  have b1 := abs_le.mp (hs (t + 1))
  have a2 := abs_le.mp (hs (t - 2))
  have b2 := abs_le.mp (hs (t + 2))
  have a3 := abs_le.mp (hs (t - 3))
  have b3 := abs_le.mp (hs (t + 3))
  have a4 := abs_le.mp (hs (t - 4))
  have b4 := abs_le.mp (hs (t + 4))
  have a5 := abs_le.mp (hs (t - 5))
  have b5 := abs_le.mp (hs (t + 5))
  have a6 := abs_le.mp (hs (t - 6))
  have b6 := abs_le.mp (hs (t + 6))
  rw [abs_le]
  constructor <;> linarith

end Distinct839.ZeroKernel
