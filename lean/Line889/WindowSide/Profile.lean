/-
Line889/WindowSide/Profile.lean — elementary facts about the profile `vProf = (2/5)·fCos`.

The window is `f(u) = 1 + ∑_{j=1}^{6} a_j cos(2πju)` on `[−1/2, 1/2]`; on the zeta side it enters
through the profile `vProf = (2/5)·fCos` (`Defs.lean`). This file proves:

* `sum_abs_aC`: `∑_j |a_j| = 234142·10⁻⁶`, hence `0.765858 ≤ fCos ≤ 1.234142` everywhere;
* `vProf_pos`, `vProf_le_one`, `vProf_even`, `continuous_vProf`;
* `integral_fCos`: `∫_{−1/2}^{1/2} fCos = 1` (each cosine integrates to `0`), so `∫ vProf = 2/5`;
* `integral_vProf_sq_ge`: `∫_{−1/2}^{1/2} vProf² ≥ (2/5)² = 4/25`, from the pointwise inequality
  `v² ≥ 2cv − c²` with `c = 2/5` (Cauchy–Schwarz on an interval of length one, without computing
  `∫ fCos² = 1 + ½∑a_j²`).

This is `Distinct839/WindowSide/Profile.lean` (and `Simple673/WindowSide/Profile.lean`) for the
coefficients of the third window; only the three numbers `∑|a_j|`, `1 − ∑|a_j|`, `1 + ∑|a_j|`
differ.
-/
import Line889.Defs

open scoped BigOperators
open Real

noncomputable section

namespace Line889

namespace WindowSide

/-! ## Pointwise bounds -/

/-- `∑_j |a_j| = 234142·10⁻⁶`. -/
theorem sum_abs_aC : ∑ j : Fin 6, |aC j| = 234142 / 1000000 := by
  have h0 : aInt 0 = 200566 := rfl
  have h1 : aInt 1 = 19 := rfl
  have h2 : aInt 2 = -9358 := rfl
  have h3 : aInt 3 = 9283 := rfl
  have h4 : aInt 4 = -6746 := rfl
  have h5 : aInt 5 = 8170 := rfl
  simp only [Fin.sum_univ_six, aC, h0, h1, h2, h3, h4, h5, abs_div]
  norm_num

/-- `|fCos u − 1| ≤ ∑_j |a_j|`. -/
theorem abs_fCos_sub_one_le (u : ℝ) : |fCos u - 1| ≤ 234142 / 1000000 := by
  rw [← sum_abs_aC]
  unfold fCos
  rw [add_sub_cancel_left]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  calc |aC j| * |Real.cos (2 * π * ((j : ℕ) + 1) * u)| ≤ |aC j| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
    _ = |aC j| := mul_one _

/-- `fCos ≥ 1 − ∑|a_j| = 0.765858` everywhere. -/
theorem fCos_ge (u : ℝ) : 765858 / 1000000 ≤ fCos u := by
  have h := (abs_le.mp (abs_fCos_sub_one_le u)).1
  linarith

/-- `fCos ≤ 1 + ∑|a_j| = 1.234142` everywhere. -/
theorem fCos_le (u : ℝ) : fCos u ≤ 1234142 / 1000000 := by
  have h := (abs_le.mp (abs_fCos_sub_one_le u)).2
  linarith

theorem vProf_eq (s : ℝ) : vProf s = 2 / 5 * fCos s := rfl

/-- `vProf > 0` everywhere (indeed `vProf ≥ 0.30`). -/
theorem vProf_pos (s : ℝ) : 0 < vProf s := by
  rw [vProf_eq]; have := fCos_ge s; positivity

/-- `vProf ≤ 1` everywhere (indeed `vProf ≤ 0.50`). -/
theorem vProf_le_one (s : ℝ) : vProf s ≤ 1 := by
  rw [vProf_eq]; have := fCos_le s; linarith

theorem abs_vProf_le_one (s : ℝ) : |vProf s| ≤ 1 := by
  rw [abs_of_pos (vProf_pos s)]; exact vProf_le_one s

/-- `fCos` is even. -/
theorem fCos_even (u : ℝ) : fCos (-u) = fCos u := by
  unfold fCos
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_neg, Real.cos_neg]

/-- `vProf` is even. -/
theorem vProf_even (s : ℝ) : vProf (-s) = vProf s := by
  rw [vProf_eq, vProf_eq, fCos_even]

theorem continuous_fCos : Continuous fCos := by
  unfold fCos
  fun_prop

theorem continuous_vProf : Continuous vProf := by
  have h : vProf = fun s => 2 / 5 * fCos s := rfl
  rw [h]
  exact continuous_const.mul continuous_fCos

/-! ## Integrals over `[−1/2, 1/2]` -/

/-- `∫_{−1/2}^{1/2} cos(2π(n+1)s) ds = 0`. -/
theorem integral_cos_harmonic (n : ℕ) :
    ∫ s in (-(1:ℝ)/2)..(1/2), Real.cos (2 * π * ((n : ℝ) + 1) * s) = 0 := by
  have hc : (2 * π * ((n : ℝ) + 1)) ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos]
  have h1 : 2 * π * ((n : ℝ) + 1) * (1 / 2) = ((n + 1 : ℕ) : ℝ) * π := by push_cast; ring
  have h2 : 2 * π * ((n : ℝ) + 1) * (-(1:ℝ) / 2) = -(((n + 1 : ℕ) : ℝ) * π) := by push_cast; ring
  rw [h1, h2, Real.sin_neg, Real.sin_nat_mul_pi]
  simp

/-- `∫_{−1/2}^{1/2} fCos = 1`. -/
theorem integral_fCos : ∫ s in (-(1:ℝ)/2)..(1/2), fCos s = 1 := by
  have hcos : ∀ j : Fin 6, IntervalIntegrable
      (fun s => aC j * Real.cos (2 * π * ((j : ℕ) + 1) * s)) MeasureTheory.volume (-(1:ℝ)/2) (1/2) :=
    fun j => (continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
      |>.intervalIntegrable _ _
  have hsum : IntervalIntegrable
      (fun s => ∑ j : Fin 6, aC j * Real.cos (2 * π * ((j : ℕ) + 1) * s))
      MeasureTheory.volume (-(1:ℝ)/2) (1/2) := by
    refine Continuous.intervalIntegrable ?_ _ _
    fun_prop
  unfold fCos
  rw [intervalIntegral.integral_add intervalIntegrable_const hsum,
    intervalIntegral.integral_finsetSum fun j _ => hcos j]
  simp only [intervalIntegral.integral_const_mul, integral_cos_harmonic, mul_zero,
    Finset.sum_const_zero, add_zero, intervalIntegral.integral_const, smul_eq_mul]
  norm_num

/-- `∫_{−1/2}^{1/2} vProf = 2/5`. -/
theorem integral_vProf : ∫ s in (-(1:ℝ)/2)..(1/2), vProf s = 2 / 5 := by
  show ∫ s in (-(1:ℝ)/2)..(1/2), 2 / 5 * fCos s = 2 / 5
  rw [intervalIntegral.integral_const_mul, integral_fCos, mul_one]

/-- `∫_{−1/2}^{1/2} vProf² ≥ 4/25`: integrate `vProf² ≥ (4/5)·vProf − 4/25`. -/
theorem integral_vProf_sq_ge : 4 / 25 ≤ ∫ s in (-(1:ℝ)/2)..(1/2), vProf s ^ 2 := by
  have hint : IntervalIntegrable vProf MeasureTheory.volume (-(1:ℝ)/2) (1/2) :=
    continuous_vProf.intervalIntegrable _ _
  have hlow : ∫ s in (-(1:ℝ)/2)..(1/2), (4 / 5 * vProf s - 4 / 25) = 4 / 25 := by
    rw [intervalIntegral.integral_sub (hint.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, integral_vProf, intervalIntegral.integral_const,
      smul_eq_mul]
    norm_num
  rw [← hlow]
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((hint.const_mul _).sub intervalIntegrable_const)
    ((continuous_vProf.pow 2).intervalIntegrable _ _) fun s _ => ?_
  nlinarith [sq_nonneg (vProf s - 2 / 5)]

end WindowSide

end Line889
