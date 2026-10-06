/-
Distinct839/Kernel/Basic.lean — the kernel `K` as the cosine transform of the window.

The window is `fCos(u) = 1 + ∑ a_j cos(2π j u)` on `[-1/2, 1/2]`. This file proves
   `fCos u ≥ 678411/10⁶ > 0`,   `∫_{-1/2}^{1/2} fCos = 1`,
   `K(t) = ∫_{-1/2}^{1/2} fCos(u) cos(2π t u) du`              (`K_eq_integral`),
   `K(-t) = K(t)`,   `K(0) = 1`,   `|K(t)| ≤ 1`,
and the estimate `|∫ fCos · g| ≤ sup |g|` (`abs_integral_fCos_mul_le`) that is used again for the
derivatives of `K` in `Distinct839/Kernel/Deriv.lean`.

Naming convention for all files in `Distinct839/Kernel/`: the statements used by the other layers
(`K_eq_integral`, `K_neg`, `K_zero`, `abs_K_le_one`, `fCos_pos`, `kTab`, `kTab_sound`, `kTabArray`,
`kTabArray_size`, `kTabArray_sound`, `betaBound`) live in the namespace `Distinct839`; everything
else lives in `Distinct839.Kernel`.
-/
import Distinct839.Defs

noncomputable section

open Real MeasureTheory intervalIntegral
open scoped BigOperators

namespace Distinct839.Kernel

/-! ## The window -/

@[fun_prop]
lemma continuous_fCos : Continuous fCos := by
  unfold fCos
  fun_prop

/-- `∑ |a_j| = 321589 · 10⁻⁶`. -/
lemma sum_abs_aC : ∑ j : Fin 6, |aC j| = 321589 / 1000000 := by
  have e : ∀ (j : Fin 6) (z : ℤ), aInt j = z → aC j = (z : ℝ) / 1000000 :=
    fun j z h => by rw [aC, h]
  rw [Fin.sum_univ_six, e 0 193305 rfl, e 1 (-23105) rfl, e 2 29166 rfl, e 3 13952 rfl,
    e 4 (-21009) rfl, e 5 41052 rfl]
  rw [abs_of_nonneg (by norm_num), abs_of_neg (by norm_num), abs_of_nonneg (by norm_num),
    abs_of_nonneg (by norm_num), abs_of_neg (by norm_num), abs_of_nonneg (by norm_num)]
  norm_num

/-- The window is bounded below by `1 - ∑ |a_j| = 0.678411`. -/
lemma fCos_ge (u : ℝ) : 678411 / 1000000 ≤ fCos u := by
  have h : ∀ j : Fin 6, -|aC j| ≤ aC j * Real.cos (2 * π * ((j : ℕ) + 1) * u) := by
    intro j
    have h1 : |aC j * Real.cos (2 * π * ((j : ℕ) + 1) * u)| ≤ |aC j| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
    exact (abs_le.mp h1).1
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h j)
  rw [Finset.sum_neg_distrib, sum_abs_aC] at hs
  unfold fCos
  linarith

/-- The window is positive. -/
theorem _root_.Distinct839.fCos_pos (u : ℝ) : 0 < fCos u := by
  linarith [fCos_ge u]

/-! ## The integral formula for the kernel -/

/-- `∫_{-1/2}^{1/2} cos(2π t u) du = sinc(t)`. -/
lemma integral_cos_two_pi_mul (t : ℝ) :
    ∫ u in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (2 * π * t * u) = sincN t := by
  unfold sincN
  rcases eq_or_ne t 0 with rfl | ht
  · norm_num
  · have hc : 2 * π * t ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) ht
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos,
      Real.sinc_of_ne_zero (mul_ne_zero pi_ne_zero ht)]
    have h1 : 2 * π * t * (1 / 2) = π * t := by ring
    have h2 : 2 * π * t * (-1 / 2) = -(π * t) := by ring
    rw [h1, h2, Real.sin_neg, smul_eq_mul]
    field_simp
    ring

/-- Product-to-sum: `fCos(u) cos(2π t u)` as a combination of cosines. -/
lemma fCos_mul_cos (t u : ℝ) :
    fCos u * Real.cos (2 * π * t * u) =
      Real.cos (2 * π * t * u) + ∑ j : Fin 6, aC j / 2 *
        (Real.cos (2 * π * (t - ((j : ℕ) + 1)) * u)
          + Real.cos (2 * π * (t + ((j : ℕ) + 1)) * u)) := by
  unfold fCos
  rw [add_mul, one_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : 2 * π * (t - ((j : ℕ) + 1)) * u = 2 * π * t * u - 2 * π * ((j : ℕ) + 1) * u := by ring
  have h2 : 2 * π * (t + ((j : ℕ) + 1)) * u = 2 * π * t * u + 2 * π * ((j : ℕ) + 1) * u := by ring
  rw [h1, h2, Real.cos_sub, Real.cos_add]
  ring

/-- The kernel is the cosine transform of the window. -/
theorem _root_.Distinct839.K_eq_integral (t : ℝ) :
    K t = ∫ u in (-(1 : ℝ) / 2)..(1 / 2), fCos u * Real.cos (2 * π * t * u) := by
  have hint : ∀ s : ℝ, IntervalIntegrable (fun u : ℝ => Real.cos (2 * π * s * u)) volume
      (-(1 : ℝ) / 2) (1 / 2) := fun s => (by fun_prop : Continuous _).intervalIntegrable _ _
  simp_rw [fCos_mul_cos]
  rw [intervalIntegral.integral_add (hint t), intervalIntegral.integral_finsetSum]
  · unfold K
    rw [integral_cos_two_pi_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hint _) (hint _),
      integral_cos_two_pi_mul, integral_cos_two_pi_mul]
  · intro j _
    exact ((hint _).add (hint _)).const_mul _
  · exact (by fun_prop : Continuous _).intervalIntegrable _ _

/-- The kernel is even. -/
theorem _root_.Distinct839.K_neg (t : ℝ) : K (-t) = K t := by
  rw [K_eq_integral, K_eq_integral]
  congr 1
  funext u
  rw [show 2 * π * (-t) * u = -(2 * π * t * u) by ring, Real.cos_neg]

/-- The normalised sinc vanishes at non-zero integers. -/
lemma sincN_intCast {n : ℤ} (hn : n ≠ 0) : sincN n = 0 := by
  unfold sincN
  rw [Real.sinc_of_ne_zero (mul_ne_zero pi_ne_zero (Int.cast_ne_zero.mpr hn)), mul_comm,
    Real.sin_int_mul_pi, zero_div]

/-- `K(0) = 1`. -/
theorem _root_.Distinct839.K_zero : K 0 = 1 := by
  unfold K
  have h0 : sincN 0 = 1 := by simp [sincN]
  have h : ∀ j : Fin 6, aC j / 2 * (sincN (0 - ((j : ℕ) + 1)) + sincN (0 + ((j : ℕ) + 1))) = 0 := by
    intro j
    have e1 : (0 : ℝ) - ((j : ℕ) + 1) = ((-((j : ℕ) + 1 : ℤ) : ℤ) : ℝ) := by push_cast; ring
    have e2 : (0 : ℝ) + ((j : ℕ) + 1) = ((((j : ℕ) + 1 : ℤ) : ℤ) : ℝ) := by push_cast; ring
    rw [e1, e2, sincN_intCast (by omega), sincN_intCast (by omega)]
    ring
  rw [h0, Finset.sum_eq_zero fun j _ => h j, add_zero]

/-- The window has integral one. -/
theorem integral_fCos : ∫ u in (-(1 : ℝ) / 2)..(1 / 2), fCos u = 1 := by
  have h := K_eq_integral 0
  rw [K_zero] at h
  simpa using h.symm

/-- If `|g| ≤ C` on `[-1/2, 1/2]` then `|∫ fCos · g| ≤ C`, because `fCos ≥ 0` and `∫ fCos = 1`. -/
lemma abs_integral_fCos_mul_le {g : ℝ → ℝ} {C : ℝ} (hg : Continuous g)
    (hC : ∀ u ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2), |g u| ≤ C) :
    |∫ u in (-(1 : ℝ) / 2)..(1 / 2), fCos u * g u| ≤ C := by
  have hab : -(1 : ℝ) / 2 ≤ 1 / 2 := by norm_num
  calc |∫ u in (-(1 : ℝ) / 2)..(1 / 2), fCos u * g u|
      ≤ ∫ u in (-(1 : ℝ) / 2)..(1 / 2), |fCos u * g u| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ u in (-(1 : ℝ) / 2)..(1 / 2), fCos u * C := by
        apply intervalIntegral.integral_mono_on hab
        · exact (by fun_prop : Continuous fun u => |fCos u * g u|).intervalIntegrable _ _
        · exact (by fun_prop : Continuous fun u => fCos u * C).intervalIntegrable _ _
        · intro u hu
          rw [abs_mul, abs_of_pos (fCos_pos u)]
          exact mul_le_mul_of_nonneg_left (hC u hu) (fCos_pos u).le
    _ = C := by rw [intervalIntegral.integral_mul_const, integral_fCos, one_mul]

/-- `|K(t)| ≤ 1`. -/
theorem _root_.Distinct839.abs_K_le_one (t : ℝ) : |K t| ≤ 1 := by
  rw [K_eq_integral]
  exact abs_integral_fCos_mul_le (by fun_prop) fun u _ => Real.abs_cos_le_one _

end Distinct839.Kernel
