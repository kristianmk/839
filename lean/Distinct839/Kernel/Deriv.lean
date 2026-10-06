/-
Distinct839/Kernel/Deriv.lean — the derivative of the kernel.

From `K(t) = ∫ fCos(u) cos(2π t u) du` over `[-1/2, 1/2]` (`K_eq_integral`), differentiation
under the integral sign gives
   `K'(t) = -∫ fCos(u) · 2π u · sin(2π t u) du`                       (`hasDerivAt_K`).
Since `fCos ≥ 0`, `∫ fCos = 1` and `|u| ≤ 1/2`, this yields
   `|K'(t)| ≤ π`                                                       (`abs_deriv_K_le`),
   `|K'(s) - K'(t)| ≤ π² |s - t|`                                      (`abs_deriv_K_sub_le`),
and, by the mean value inequality, the cell estimate used for the kernel table:
   `|K(t)| ≥ |K(t₀)| - h · min(π, |K'(t₀)| + π² h)` for `|t - t₀| ≤ h`  (`abs_K_ge_of_abs_sub_le`).
-/
import Distinct839.Kernel.Basic

noncomputable section

open Real MeasureTheory intervalIntegral
open scoped BigOperators Topology

namespace Distinct839.Kernel

/-- The derivative of the kernel, as an integral: `K'(t) = -∫ fCos(u) · 2π u · sin(2π t u) du`. -/
def Kd (t : ℝ) : ℝ :=
  ∫ u in (-(1 : ℝ) / 2)..(1 / 2), fCos u * (-(2 * π * u) * Real.sin (2 * π * t * u))

/-- Differentiation under the integral sign: `K` has derivative `Kd t` at `t`. -/
theorem hasDerivAt_K (t : ℝ) : HasDerivAt K (Kd t) t := by
  have hK : K = fun t => ∫ u in (-(1 : ℝ) / 2)..(1 / 2), fCos u * Real.cos (2 * π * t * u) :=
    funext K_eq_integral
  rw [hK]
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun t u => fCos u * Real.cos (2 * π * t * u))
    (F' := fun t u => fCos u * (-(2 * π * u) * Real.sin (2 * π * t * u)))
    (x₀ := t) (s := Set.univ) (a := -(1 : ℝ) / 2) (b := 1 / 2)
    (bound := fun u => |fCos u| * (2 * π * |u|))
    Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_
  · exact key.2
  · exact Filter.Eventually.of_forall fun s =>
      (by fun_prop : Continuous fun u => fCos u * Real.cos (2 * π * s * u)).aestronglyMeasurable
  · exact (by fun_prop : Continuous fun u =>
      fCos u * Real.cos (2 * π * t * u)).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun u =>
      fCos u * (-(2 * π * u) * Real.sin (2 * π * t * u))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u _ s _ => ?_
    show ‖fCos u * (-(2 * π * u) * Real.sin (2 * π * s * u))‖ ≤ |fCos u| * (2 * π * |u|)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_mul, abs_mul, abs_two,
      abs_of_pos pi_pos]
    have h1 : |Real.sin (2 * π * s * u)| ≤ 1 := Real.abs_sin_le_one _
    have h2 : 0 ≤ 2 * π * |u| := by positivity
    calc |fCos u| * (2 * π * |u| * |Real.sin (2 * π * s * u)|)
        ≤ |fCos u| * (2 * π * |u| * 1) := by gcongr
      _ = |fCos u| * (2 * π * |u|) := by ring
  · exact (by fun_prop : Continuous fun u => |fCos u| * (2 * π * |u|)).intervalIntegrable _ _
  · refine Filter.Eventually.of_forall fun u _ s _ => ?_
    have h1 : HasDerivAt (fun x : ℝ => 2 * π * x * u) (2 * π * u) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 * π)).mul_const u
    have h2 := (h1.cos).const_mul (fCos u)
    have e : fCos u * (-(2 * π * u) * Real.sin (2 * π * s * u))
        = fCos u * (-Real.sin (2 * π * s * u) * (2 * π * u)) := by ring
    show HasDerivAt (fun x : ℝ => fCos u * Real.cos (2 * π * x * u))
      (fCos u * (-(2 * π * u) * Real.sin (2 * π * s * u))) s
    rw [e]
    exact h2

/-- The kernel is differentiable. -/
theorem differentiable_K : Differentiable ℝ K := fun t => (hasDerivAt_K t).differentiableAt

/-- The derivative of the kernel is the integral `Kd`. -/
theorem deriv_K (t : ℝ) : deriv K t = Kd t := (hasDerivAt_K t).deriv

/-- `|K'(t)| ≤ π`. -/
theorem abs_deriv_K_le (t : ℝ) : |deriv K t| ≤ π := by
  rw [deriv_K]
  unfold Kd
  refine abs_integral_fCos_mul_le (by fun_prop) fun u hu => ?_
  have hu' : |u| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
  rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_two, abs_of_pos pi_pos]
  have h1 : |Real.sin (2 * π * t * u)| ≤ 1 := Real.abs_sin_le_one _
  calc 2 * π * |u| * |Real.sin (2 * π * t * u)| ≤ 2 * π * (1 / 2) * 1 := by gcongr
    _ = π := by ring

/-- `|K'(s) - K'(t)| ≤ π² |s - t|`. -/
theorem abs_deriv_K_sub_le (s t : ℝ) : |deriv K s - deriv K t| ≤ π ^ 2 * |s - t| := by
  rw [deriv_K, deriv_K]
  unfold Kd
  rw [← intervalIntegral.integral_sub
    ((by fun_prop : Continuous fun u =>
      fCos u * (-(2 * π * u) * Real.sin (2 * π * s * u))).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun u =>
      fCos u * (-(2 * π * u) * Real.sin (2 * π * t * u))).intervalIntegrable _ _)]
  simp_rw [← mul_sub]
  refine abs_integral_fCos_mul_le (by fun_prop) fun u hu => ?_
  have hu' : |u| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
  rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_two, abs_of_pos pi_pos]
  have h1 : |Real.sin (2 * π * s * u) - Real.sin (2 * π * t * u)| ≤ 2 * π * |u| * |s - t| := by
    refine (Real.abs_sin_sub_sin_le _ _).trans (le_of_eq ?_)
    rw [show 2 * π * s * u - 2 * π * t * u = 2 * π * u * (s - t) by ring, abs_mul, abs_mul,
      abs_mul, abs_two, abs_of_pos pi_pos]
  have h2 : 0 ≤ |s - t| := abs_nonneg _
  have h3 : 0 ≤ |u| := abs_nonneg _
  calc 2 * π * |u| * |Real.sin (2 * π * s * u) - Real.sin (2 * π * t * u)|
      ≤ 2 * π * |u| * (2 * π * |u| * |s - t|) := by gcongr
    _ ≤ 2 * π * (1 / 2) * (2 * π * (1 / 2) * |s - t|) := by gcongr
    _ = π ^ 2 * |s - t| := by ring

/-- Cell estimate. If `|t - t₀| ≤ h` then `|K(t)| ≥ |K(t₀)| - h · min(π, |K'(t₀)| + π² h)`. -/
theorem abs_K_ge_of_abs_sub_le {t₀ t h : ℝ} (ht : |t - t₀| ≤ h) :
    |K t₀| - h * min π (|deriv K t₀| + π ^ 2 * h) ≤ |K t| := by
  have hh : 0 ≤ h := (abs_nonneg _).trans ht
  set C : ℝ := min π (|deriv K t₀| + π ^ 2 * h) with hC
  have hC0 : 0 ≤ C := le_min pi_pos.le (by positivity)
  -- on the closed ball of radius `h` around `t₀` the derivative is bounded by `C`
  have hbound : ∀ x ∈ Metric.closedBall t₀ h, ‖deriv K x‖ ≤ C := by
    intro x hx
    have hx' : |x - t₀| ≤ h := by simpa [Real.dist_eq] using hx
    rw [Real.norm_eq_abs, hC]
    refine le_min (abs_deriv_K_le x) ?_
    have h1 : |deriv K x| ≤ |deriv K t₀| + |deriv K x - deriv K t₀| := by
      have := abs_add_le (deriv K t₀) (deriv K x - deriv K t₀)
      simpa using this
    have h2 : |deriv K x - deriv K t₀| ≤ π ^ 2 * h :=
      (abs_deriv_K_sub_le x t₀).trans (mul_le_mul_of_nonneg_left hx' (by positivity))
    linarith
  have hmv := (convex_closedBall t₀ h).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => differentiable_K x) hbound
    (Metric.mem_closedBall_self hh) (by simpa [Real.dist_eq] using ht : t ∈ Metric.closedBall t₀ h)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  have h3 : C * |t - t₀| ≤ h * C := by
    rw [mul_comm h C]
    exact mul_le_mul_of_nonneg_left ht hC0
  have h4 : |K t₀| ≤ |K t| + |K t - K t₀| := by
    have := abs_sub_abs_le_abs_sub (K t₀) (K t)
    rw [abs_sub_comm (K t₀) (K t)] at this
    linarith
  linarith

end Distinct839.Kernel
