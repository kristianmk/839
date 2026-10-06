/-
Simple673/Majorant/Fourier.lean — the Fourier transform of the two-sinc majorant.

Let `d = sep = 17/20`, `γ = gammaM = 13/20` and `m(t) = max(d - |t|, 0)`. The function

  `FMaj t = (2γ/d²) · (m(t) cos(π t) + sin(π m(t))/π)`

is continuous, even and supported in `[-d, d]` (it is `γ · H ⋆ H` for
`H = (2/d) cos(π ξ) 1_{|ξ| ≤ d/2}`, but this description is not used). Two elementary integrals
give `∫ FMaj t · cos(2π u t) dt = gMaj u`, so the Fourier transform of `FMaj` is `gMaj`. Since
`gMaj` is integrable, Fourier inversion gives

  `∫ gMaj u · cos(2π t u) du = FMaj t`,

which is `LMaj` at `t = 0` and `0` for `|t| ≥ d`.

The exported facts (`gMaj_nonneg`, `continuous_gMaj`, `integrable_gMaj`, `integral_gMaj`,
`integral_gMaj_cos`) are in the namespace `Simple673`, the auxiliary ones in
`Simple673.Majorant`.

The file follows `Distinct839/Majorant/Fourier.lean`. The proofs do not depend on the values of
the constants: they use only `d > 0` and `γ ≥ 0`.
-/
import Simple673.Defs

open Real MeasureTheory
open scoped FourierTransform

namespace Simple673.Majorant

/-! ## Elementary facts -/

lemma sep_pos : 0 < sep := by unfold sep; norm_num

lemma sep_ne_zero : sep ≠ 0 := sep_pos.ne'

lemma gammaM_nonneg : 0 ≤ gammaM := by unfold gammaM; norm_num

/-- `sin x = x · sinc x`, for every real `x`. -/
lemma sin_eq_mul_sinc (x : ℝ) : sin x = x * sinc x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [sinc_of_ne_zero hx]
    field_simp

/-- `sinc x² ≤ 2/(1 + x²)`. -/
lemma sinc_sq_le (x : ℝ) : sinc x ^ 2 ≤ 2 * (1 + x ^ 2)⁻¹ := by
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hA : sinc x ^ 2 ≤ 1 := by
    calc sinc x ^ 2 = |sinc x| ^ 2 := (sq_abs _).symm
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_sinc_le_one x) 2
      _ = 1 := one_pow 2
  have hB : sinc x ^ 2 * x ^ 2 ≤ 1 := by
    have h : sinc x * x = sin x := by rw [mul_comm]; exact (sin_eq_mul_sinc x).symm
    rw [← mul_pow, h]
    exact sin_sq_le_one x
  rw [← div_eq_mul_inv, le_div_iff₀ h1, mul_add, mul_one]
  linarith

/-- `gMaj u ≤ 4γ (1/(1 + x₋²) + 1/(1 + x₊²))`, `x_± = π d (u ± 1/2)`. -/
lemma gMaj_le (u : ℝ) :
    gMaj u ≤ gammaM * (4 * (1 + (π * sep * (u - 1 / 2)) ^ 2)⁻¹
      + 4 * (1 + (π * sep * (u + 1 / 2)) ^ 2)⁻¹) := by
  unfold gMaj sincN
  rw [show π * (sep * (u - 1 / 2)) = π * sep * (u - 1 / 2) by ring,
    show π * (sep * (u + 1 / 2)) = π * sep * (u + 1 / 2) by ring]
  refine mul_le_mul_of_nonneg_left ?_ gammaM_nonneg
  have h1 := sinc_sq_le (π * sep * (u - 1 / 2))
  have h2 := sinc_sq_le (π * sep * (u + 1 / 2))
  nlinarith [sq_nonneg (sinc (π * sep * (u - 1 / 2)) - sinc (π * sep * (u + 1 / 2)))]

end Simple673.Majorant

/-! ## The majorant: positivity, continuity, integrability -/

namespace Simple673

open Majorant

/-- The majorant is nonnegative. -/
theorem gMaj_nonneg (u : ℝ) : 0 ≤ gMaj u := mul_nonneg gammaM_nonneg (sq_nonneg _)

/-- The majorant is continuous. -/
theorem continuous_gMaj : Continuous gMaj := by
  have h : Continuous fun u : ℝ =>
      gammaM * (sincN (sep * (u - 1 / 2)) + sincN (sep * (u + 1 / 2))) ^ 2 := by
    unfold sincN
    fun_prop
  exact h

/-- The majorant is integrable on `ℝ`: it is bounded by a sum of two Cauchy densities. -/
theorem integrable_gMaj : Integrable gMaj := by
  have hne : π * sep ≠ 0 := mul_ne_zero pi_ne_zero sep_ne_zero
  have h1 : Integrable fun x : ℝ => (1 + (π * sep * x) ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.comp_mul_left' hne
  have hm : Integrable fun u : ℝ => (1 + (π * sep * (u - 1 / 2)) ^ 2)⁻¹ :=
    h1.comp_sub_right (1 / 2)
  have hp : Integrable fun u : ℝ => (1 + (π * sep * (u + 1 / 2)) ^ 2)⁻¹ :=
    h1.comp_add_right (1 / 2)
  have hB : Integrable fun u : ℝ => gammaM * (4 * (1 + (π * sep * (u - 1 / 2)) ^ 2)⁻¹
      + 4 * (1 + (π * sep * (u + 1 / 2)) ^ 2)⁻¹) :=
    ((hm.const_mul 4).add (hp.const_mul 4)).const_mul gammaM
  refine hB.mono' continuous_gMaj.aestronglyMeasurable (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (gMaj_nonneg u)]
  exact gMaj_le u

end Simple673

namespace Simple673.Majorant

lemma integrable_gMaj_mul_cos (t : ℝ) :
    Integrable fun u : ℝ => gMaj u * cos (2 * π * t * u) := by
  refine integrable_gMaj.mono' (continuous_gMaj.mul (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gMaj_nonneg u)]
  exact mul_le_of_le_one_right (gMaj_nonneg u) (abs_cos_le_one _)

lemma integrable_gMaj_mul_sin (t : ℝ) :
    Integrable fun u : ℝ => gMaj u * sin (2 * π * t * u) := by
  refine integrable_gMaj.mono' (continuous_gMaj.mul (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gMaj_nonneg u)]
  exact mul_le_of_le_one_right (gMaj_nonneg u) (abs_sin_le_one _)

/-! ## Two elementary integrals -/

/-- `∫₀^d (d - t) cos(a t) dt = (1 - cos(a d))/a²` for `a ≠ 0`. -/
lemma integral_tri_cos_of_ne {a : ℝ} (ha : a ≠ 0) :
    ∫ t in (0 : ℝ)..sep, (sep - t) * cos (a * t) = (1 - cos (a * sep)) / a ^ 2 := by
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) sep,
      HasDerivAt (fun y : ℝ => (sep - y) * sin (a * y) / a - cos (a * y) / a ^ 2)
        ((sep - t) * cos (a * t)) t := by
    intro t _
    have hlin : HasDerivAt (fun y : ℝ => a * y) a t := by
      have h := (hasDerivAt_id' t).const_mul a
      rwa [mul_one] at h
    have h1 : HasDerivAt (fun y : ℝ => sep - y) (-1) t := (hasDerivAt_id' t).const_sub sep
    have h2 : HasDerivAt (fun y : ℝ => sin (a * y)) (cos (a * t) * a) t := hlin.sin
    have h3 : HasDerivAt (fun y : ℝ => cos (a * y)) (-sin (a * t) * a) t := hlin.cos
    have h4 : HasDerivAt (fun y : ℝ => (sep - y) * sin (a * y))
        (-1 * sin (a * t) + (sep - t) * (cos (a * t) * a)) t := h1.mul h2
    have h5 : HasDerivAt (fun y : ℝ => (sep - y) * sin (a * y) / a - cos (a * y) / a ^ 2)
        ((-1 * sin (a * t) + (sep - t) * (cos (a * t) * a)) / a
          - (-sin (a * t) * a) / a ^ 2) t := (h4.div_const a).sub (h3.div_const (a ^ 2))
    refine h5.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ => (sep - t) * cos (a * t)).intervalIntegrable _ _)]
  simp only [mul_zero, sin_zero, cos_zero]
  ring

/-- `∫₀^d (d - t) cos(a t) dt = (d²/2) sinc(a d/2)²`. -/
lemma integral_tri_cos (a : ℝ) :
    ∫ t in (0 : ℝ)..sep, (sep - t) * cos (a * t) = sep ^ 2 / 2 * sinc (a * sep / 2) ^ 2 := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hd : ∀ t ∈ Set.uIcc (0 : ℝ) sep,
        HasDerivAt (fun y : ℝ => sep * y - y * y / 2) ((sep - t) * cos (0 * t)) t := by
      intro t _
      have h1 : HasDerivAt (fun y : ℝ => sep * y) (sep * 1) t := (hasDerivAt_id' t).const_mul sep
      have h2 : HasDerivAt (fun y : ℝ => y * y) (1 * t + t * 1) t :=
        (hasDerivAt_id' t).mul (hasDerivAt_id' t)
      have h3 : HasDerivAt (fun y : ℝ => sep * y - y * y / 2)
          (sep * 1 - (1 * t + t * 1) / 2) t := h1.sub (h2.div_const 2)
      refine h3.congr_deriv ?_
      rw [zero_mul, cos_zero]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun t : ℝ => (sep - t) * cos (0 * t)).intervalIntegrable _ _)]
    simp only [zero_mul, zero_div, sinc_zero]
    ring
  · have hs := sep_ne_zero
    have hx : a * sep / 2 ≠ 0 := div_ne_zero (mul_ne_zero ha hs) two_ne_zero
    have hcos : cos (a * sep) = 1 - 2 * sin (a * sep / 2) ^ 2 := by
      have h := cos_two_mul (a * sep / 2)
      rw [show 2 * (a * sep / 2) = a * sep by ring, cos_sq'] at h
      rw [h]
      ring
    rw [integral_tri_cos_of_ne ha, sinc_of_ne_zero hx, hcos]
    field_simp
    ring

/-- `∫₀^d sin(π d - b t) dt = d · sin(π d - b d/2) · sinc(b d/2)`. -/
lemma integral_sin_sub (b : ℝ) :
    ∫ t in (0 : ℝ)..sep, sin (π * sep - b * t)
      = sep * sin (π * sep - b * sep / 2) * sinc (b * sep / 2) := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp only [zero_mul, zero_div, sub_zero, sinc_zero, mul_one, intervalIntegral.integral_const,
      smul_eq_mul]
  · have hs := sep_ne_zero
    have hx : b * sep / 2 ≠ 0 := div_ne_zero (mul_ne_zero hb hs) two_ne_zero
    have hgen : ∀ X Y : ℝ, cos (X - Y) - cos (X + Y) = 2 * sin X * sin Y := by
      intro X Y
      rw [cos_sub, cos_add]
      ring
    have key : cos (π * sep - b * sep) - cos (π * sep)
        = 2 * sin (π * sep - b * sep / 2) * sin (b * sep / 2) := by
      have h := hgen (π * sep - b * sep / 2) (b * sep / 2)
      rw [show π * sep - b * sep / 2 - b * sep / 2 = π * sep - b * sep by ring,
        show π * sep - b * sep / 2 + b * sep / 2 = π * sep by ring] at h
      exact h
    rw [intervalIntegral.integral_comp_sub_mul (f := sin) hb, integral_sin, mul_zero, sub_zero,
      key, sinc_of_ne_zero hx, smul_eq_mul]
    field_simp

/-- The first triangle term, in terms of `sincN`. -/
lemma integral_half1 (u : ℝ) :
    ∫ t in (0 : ℝ)..sep, (sep - t) * cos ((2 * π * u + π) * t)
      = sep ^ 2 / 2 * sincN (sep * (u + 1 / 2)) ^ 2 := by
  unfold sincN
  rw [integral_tri_cos, show (2 * π * u + π) * sep / 2 = π * (sep * (u + 1 / 2)) by ring]

/-- The second triangle term, in terms of `sincN`. -/
lemma integral_half2 (u : ℝ) :
    ∫ t in (0 : ℝ)..sep, (sep - t) * cos ((2 * π * u - π) * t)
      = sep ^ 2 / 2 * sincN (sep * (u - 1 / 2)) ^ 2 := by
  unfold sincN
  rw [integral_tri_cos, show (2 * π * u - π) * sep / 2 = π * (sep * (u - 1 / 2)) by ring]

/-- The first cross term, in terms of `sincN`. -/
lemma integral_half3 (u : ℝ) :
    ∫ t in (0 : ℝ)..sep, sin (π * sep - (π - 2 * π * u) * t)
      = π * sep ^ 2 * (u + 1 / 2) * sincN (sep * (u + 1 / 2)) * sincN (sep * (u - 1 / 2)) := by
  unfold sincN
  rw [integral_sin_sub,
    show π * sep - (π - 2 * π * u) * sep / 2 = π * (sep * (u + 1 / 2)) by ring,
    show (π - 2 * π * u) * sep / 2 = -(π * (sep * (u - 1 / 2))) by ring, sinc_neg,
    sin_eq_mul_sinc]
  ring

/-- The second cross term, in terms of `sincN`. -/
lemma integral_half4 (u : ℝ) :
    ∫ t in (0 : ℝ)..sep, sin (π * sep - (π + 2 * π * u) * t)
      = -(π * sep ^ 2 * (u - 1 / 2) * sincN (sep * (u + 1 / 2)) * sincN (sep * (u - 1 / 2))) := by
  unfold sincN
  rw [integral_sin_sub,
    show π * sep - (π + 2 * π * u) * sep / 2 = -(π * (sep * (u - 1 / 2))) by ring,
    show (π + 2 * π * u) * sep / 2 = π * (sep * (u + 1 / 2)) by ring, sin_neg,
    sin_eq_mul_sinc]
  ring

/-! ## The function `FMaj` -/

/-- The function whose Fourier transform is `gMaj`:
`FMaj t = (2γ/d²) (m cos(π t) + sin(π m)/π)` with `m = max(d - |t|, 0)`. -/
noncomputable def FMaj (t : ℝ) : ℝ :=
  2 * gammaM / sep ^ 2 * (max (sep - |t|) 0 * cos (π * t) + sin (π * max (sep - |t|) 0) / π)

lemma FMaj_neg (t : ℝ) : FMaj (-t) = FMaj t := by
  unfold FMaj
  rw [abs_neg, mul_neg, cos_neg]

lemma FMaj_eq_zero {t : ℝ} (ht : sep ≤ |t|) : FMaj t = 0 := by
  unfold FMaj
  rw [max_eq_right (by linarith : sep - |t| ≤ 0)]
  simp

lemma FMaj_of_mem {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ sep) :
    FMaj t = 2 * gammaM / sep ^ 2 * ((sep - t) * cos (π * t) + sin (π * (sep - t)) / π) := by
  unfold FMaj
  rw [abs_of_nonneg h0, max_eq_left (by linarith : (0 : ℝ) ≤ sep - t)]

lemma FMaj_zero : FMaj 0 = LMaj := by
  have hs := sep_ne_zero
  have hp := pi_ne_zero
  have hx : π * sep ≠ 0 := mul_ne_zero hp hs
  unfold FMaj LMaj sincN
  rw [abs_zero, sub_zero, max_eq_left sep_pos.le, mul_zero, cos_zero, sinc_of_ne_zero hx]
  field_simp

lemma continuous_FMaj : Continuous FMaj := by
  have hm : Continuous fun t : ℝ => max (sep - |t|) 0 :=
    (continuous_const.sub continuous_abs).max continuous_const
  have h : Continuous fun t : ℝ => 2 * gammaM / sep ^ 2
      * (max (sep - |t|) 0 * cos (π * t) + sin (π * max (sep - |t|) 0) / π) :=
    continuous_const.mul ((hm.mul (by fun_prop)).add
      ((continuous_sin.comp (continuous_const.mul hm)).div_const π))
  exact h

lemma hasCompactSupport_FMaj : HasCompactSupport FMaj :=
  HasCompactSupport.intro (isCompact_Icc (a := -sep) (b := sep)) fun t ht => by
    apply FMaj_eq_zero
    by_contra hcon
    have h := abs_lt.mp (not_le.mp hcon)
    exact ht ⟨h.1.le, h.2.le⟩

lemma integrable_FMaj_mul_cos (u : ℝ) :
    Integrable fun t : ℝ => FMaj t * cos (2 * π * u * t) :=
  (continuous_FMaj.mul (by fun_prop)).integrable_of_hasCompactSupport
    hasCompactSupport_FMaj.mul_right

lemma integrable_FMaj_mul_sin (u : ℝ) :
    Integrable fun t : ℝ => FMaj t * sin (2 * π * u * t) :=
  (continuous_FMaj.mul (by fun_prop)).integrable_of_hasCompactSupport
    hasCompactSupport_FMaj.mul_right

/-! ## The cosine transform of `FMaj` is `gMaj` -/

lemma integral_FMaj_cos_half (u : ℝ) :
    ∫ t in (0 : ℝ)..sep, FMaj t * cos (2 * π * u * t) = gMaj u / 2 := by
  have hs := sep_ne_zero
  have hp := pi_ne_zero
  have hcongr : ∀ t ∈ Set.uIcc (0 : ℝ) sep, FMaj t * cos (2 * π * u * t) =
      gammaM / sep ^ 2 * ((sep - t) * cos ((2 * π * u + π) * t))
      + gammaM / sep ^ 2 * ((sep - t) * cos ((2 * π * u - π) * t))
      + gammaM / (sep ^ 2 * π) * sin (π * sep - (π - 2 * π * u) * t)
      + gammaM / (sep ^ 2 * π) * sin (π * sep - (π + 2 * π * u) * t) := by
    intro t ht
    rw [Set.uIcc_of_le sep_pos.le] at ht
    rw [FMaj_of_mem ht.1 ht.2]
    have c1 : cos ((2 * π * u + π) * t)
        = cos (2 * π * u * t) * cos (π * t) - sin (2 * π * u * t) * sin (π * t) := by
      rw [add_mul, cos_add]
    have c2 : cos ((2 * π * u - π) * t)
        = cos (2 * π * u * t) * cos (π * t) + sin (2 * π * u * t) * sin (π * t) := by
      rw [sub_mul, cos_sub]
    have s1 : sin (π * sep - (π - 2 * π * u) * t)
        = sin (π * (sep - t)) * cos (2 * π * u * t)
          + cos (π * (sep - t)) * sin (2 * π * u * t) := by
      rw [show π * sep - (π - 2 * π * u) * t = π * (sep - t) + 2 * π * u * t by ring, sin_add]
    have s2 : sin (π * sep - (π + 2 * π * u) * t)
        = sin (π * (sep - t)) * cos (2 * π * u * t)
          - cos (π * (sep - t)) * sin (2 * π * u * t) := by
      rw [show π * sep - (π + 2 * π * u) * t = π * (sep - t) - 2 * π * u * t by ring, sin_sub]
    rw [c1, c2, s1, s2]
    field_simp
    ring
  rw [intervalIntegral.integral_congr hcongr]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_half1 u, integral_half2 u, integral_half3 u, integral_half4 u]
  · unfold gMaj
    field_simp
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- The cosine transform of `FMaj` is the majorant. -/
theorem integral_FMaj_mul_cos (u : ℝ) : ∫ t, FMaj t * cos (2 * π * u * t) = gMaj u := by
  have hsupp : Function.support (fun t : ℝ => FMaj t * cos (2 * π * u * t))
      ⊆ Set.Ioc (-sep) sep := by
    intro t ht
    rw [Function.mem_support] at ht
    have hF : FMaj t ≠ 0 := left_ne_zero_of_mul ht
    have hlt : |t| < sep := by
      by_contra hcon
      exact hF (FMaj_eq_zero (not_lt.mp hcon))
    exact ⟨(abs_lt.mp hlt).1, (abs_lt.mp hlt).2.le⟩
  have hcont : Continuous fun t : ℝ => FMaj t * cos (2 * π * u * t) :=
    continuous_FMaj.mul (by fun_prop)
  have hneg : ∫ t in (-sep)..0, FMaj t * cos (2 * π * u * t)
      = ∫ t in (0 : ℝ)..sep, FMaj t * cos (2 * π * u * t) := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := sep)
      (f := fun t : ℝ => FMaj t * cos (2 * π * u * t))
    rw [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [FMaj_neg, mul_neg, cos_neg]
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupp,
    ← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable (-sep) 0)
      (hcont.intervalIntegrable 0 sep), hneg, integral_FMaj_cos_half]
  ring

/-- The sine transform of the even function `FMaj` vanishes. -/
lemma integral_FMaj_mul_sin (u : ℝ) : ∫ t, FMaj t * sin (2 * π * u * t) = 0 := by
  have h := integral_neg_eq_self (fun t : ℝ => FMaj t * sin (2 * π * u * t)) volume
  simp only [FMaj_neg, mul_neg, sin_neg, integral_neg] at h
  linarith

/-! ## Fourier inversion -/

/-- `FMaj` as a complex-valued function. -/
noncomputable def FMajC (t : ℝ) : ℂ := (FMaj t : ℂ)

lemma continuous_FMajC : Continuous FMajC :=
  Complex.continuous_ofReal.comp continuous_FMaj

lemma integrable_FMajC : Integrable FMajC :=
  (continuous_FMaj.integrable_of_hasCompactSupport hasCompactSupport_FMaj).ofReal

/-- The Fourier transform of `FMaj` is the majorant. -/
theorem fourier_FMajC (u : ℝ) : 𝓕 FMajC u = ((gMaj u : ℝ) : ℂ) := by
  have hc := integrable_FMaj_mul_cos u
  have hs := integrable_FMaj_mul_sin u
  have hpt : ∀ t : ℝ, Complex.exp (((-2 * π * t * u : ℝ) : ℂ) * Complex.I) • FMajC t
      = ((FMaj t * cos (2 * π * u * t) : ℝ) : ℂ)
        - ((FMaj t * sin (2 * π * u * t) : ℝ) : ℂ) * Complex.I := by
    intro t
    rw [smul_eq_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show -2 * π * t * u = -(2 * π * u * t) by ring, cos_neg, sin_neg]
    unfold FMajC
    push_cast
    ring
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [hpt]
  rw [integral_sub hc.ofReal (hs.ofReal.mul_const _), integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal, integral_FMaj_mul_sin,
    integral_FMaj_mul_cos]
  simp

/-- **Fourier inversion for the majorant**: the cosine transform of `gMaj` is `FMaj`. -/
theorem integral_gMaj_mul_cos (t : ℝ) : ∫ u, gMaj u * cos (2 * π * t * u) = FMaj t := by
  have hF : 𝓕 FMajC = fun u : ℝ => ((gMaj u : ℝ) : ℂ) := funext fourier_FMajC
  have hinv : 𝓕⁻ (𝓕 FMajC) t = FMajC t :=
    MeasureTheory.Integrable.fourierInv_fourier_eq integrable_FMajC
      (by rw [hF]; exact integrable_gMaj.ofReal) continuous_FMajC.continuousAt
  rw [hF, Real.fourierInv_eq'] at hinv
  have hc := integrable_gMaj_mul_cos t
  have hs := integrable_gMaj_mul_sin t
  have hpt : ∀ v : ℝ, Complex.exp (((2 * π * inner ℝ v t : ℝ) : ℂ) * Complex.I)
        • ((gMaj v : ℝ) : ℂ)
      = ((gMaj v * cos (2 * π * t * v) : ℝ) : ℂ)
        + ((gMaj v * sin (2 * π * t * v) : ℝ) : ℂ) * Complex.I := by
    intro v
    have hin : inner ℝ v t = t * v := by simp
    rw [hin, smul_eq_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show 2 * π * (t * v) = 2 * π * t * v by ring]
    push_cast
    ring
  simp_rw [hpt] at hinv
  rw [integral_add hc.ofReal (hs.ofReal.mul_const _), integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal] at hinv
  have hre := congrArg Complex.re hinv
  rw [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero,
    add_zero] at hre
  exact hre.trans (Complex.ofReal_re _)

end Simple673.Majorant

namespace Simple673

open Majorant

/-- `∫ gMaj = LMaj`. -/
theorem integral_gMaj : ∫ u, gMaj u = LMaj := by
  have h := integral_gMaj_mul_cos 0
  simp only [mul_zero, zero_mul, cos_zero, mul_one] at h
  rw [h, FMaj_zero]

/-- The cosine transform of `gMaj` vanishes at frequencies `|t| ≥ d`. -/
theorem integral_gMaj_cos (t : ℝ) (ht : sep ≤ |t|) :
    ∫ u, gMaj u * cos (2 * π * t * u) = 0 := by
  rw [integral_gMaj_mul_cos, FMaj_eq_zero ht]

end Simple673
