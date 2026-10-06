/-
Simple673/ZeroKernel/Kernel.lean — the kernel of the realised window is close to `K`.

With `φ` the window realising `vProf` at height `T`, `L` the bandwidth and `Φ = (φ²)^`:

* `abs_VPhiR_sub_le`: `|Φ(r) - (2/5) L K(r L / 2π)| ≤ 2` for all real `r`. The ramp changes `φ²`
  only on a set of measure `2w = 2` (upstream `edge_estimate`); the sharp profile integral is
  `(2/5) L K(r L / 2π)` by the integral formula for `K` and the substitution `u = L s`.
* `abs_av_mul_sub_le`, `av_lower`: the case `r = 0`, `|a L - (2/5) L| ≤ 2`, so `a ≥ 2/5 - 2/L`.
* `abs_VPhiR_div_sub_K_le`: `|Φ(r)/(a L) - K(r L / 2π)| ≤ 24 / L` once `L ≥ 40`.

The integral formula for `K` is a hypothesis (`hK`), proved in another layer. The algebra behind
the normalised comparison is `Distinct839.ZeroKernel.abs_div_sub_le_aux`
(`Distinct839/ZeroKernel/Kernel.lean`), which does not depend on the window.
-/
import Distinct839.ZeroKernel.Kernel
import Simple673.ZeroKernel.Window

open scoped BigOperators
open Real Filter Topology MeasureTheory Zeta23

noncomputable section

namespace Simple673.ZeroKernel

variable {lam cW T : ℝ}

/-- The transform of the sharp profile `vProf(u/L) · 1_{|u| ≤ L/2}` is `(2/5) L K(r L / 2π)`. -/
lemma integral_sharp_eq
    (hK : ∀ t : ℝ, K t = ∫ u in (-(1:ℝ)/2)..(1/2), fCos u * Real.cos (2 * π * t * u))
    {L : ℝ} (hL : 0 < L) (r : ℝ) :
    ∫ u in Set.Icc (-(L / 2)) (L / 2), vProf (u / L) * Real.cos (r * u)
      = 2 / 5 * L * K (r * L / (2 * π)) := by
  have hL0 : L ≠ 0 := hL.ne'
  have hcongr : ∫ u in (-(L / 2))..(L / 2), vProf (u / L) * Real.cos (r * u)
      = ∫ u in (-(L / 2))..(L / 2), vProf (u / L) * Real.cos (r * (L * (u / L))) := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    have e : L * (u / L) = u := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ hL0]
    show vProf (u / L) * Real.cos (r * u) = vProf (u / L) * Real.cos (r * (L * (u / L)))
    rw [e]
  have hscale : ∫ u in (-(L / 2))..(L / 2), vProf (u / L) * Real.cos (r * (L * (u / L)))
      = L * ∫ s in (-(1:ℝ)/2)..(1/2), vProf s * Real.cos (r * (L * s)) :=
    XiPrime.integral_scale (g := fun s => vProf s * Real.cos (r * (L * s))) hL
  have hprof : ∫ s in (-(1:ℝ)/2)..(1/2), vProf s * Real.cos (r * (L * s))
      = 2 / 5 * ∫ s in (-(1:ℝ)/2)..(1/2), fCos s * Real.cos (2 * π * (r * L / (2 * π)) * s) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    have e : 2 * π * (r * L / (2 * π)) * s = r * (L * s) := by
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ (by positivity : (2 * π : ℝ) ≠ 0)]
      ring
    show 2 / 5 * fCos s * Real.cos (r * (L * s))
      = 2 / 5 * (fCos s * Real.cos (2 * π * (r * L / (2 * π)) * s))
    rw [e]
    ring
  calc ∫ u in Set.Icc (-(L / 2)) (L / 2), vProf (u / L) * Real.cos (r * u)
      = ∫ u in (-(L / 2))..(L / 2), vProf (u / L) * Real.cos (r * u) := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by linarith : -(L / 2) ≤ L / 2)]
    _ = L * ∫ s in (-(1:ℝ)/2)..(1/2), vProf s * Real.cos (r * (L * s)) := hcongr.trans hscale
    _ = L * (2 / 5 * K (r * L / (2 * π))) := by rw [hprof, ← hK (r * L / (2 * π))]
    _ = 2 / 5 * L * K (r * L / (2 * π)) := by ring

/-- **Kernel comparison.** `|Φ(r) - (2/5) L K(r L / 2π)| ≤ 2` for the realised window. -/
theorem abs_VPhiR_sub_le
    (hK : ∀ t : ℝ, K t = ∫ u in (-(1:ℝ)/2)..(1/2), fCos u * Real.cos (2 * π * t * u))
    (hW : AdmWindow (phiW lam T) ((Pst lam).L T) 1 cW) (r : ℝ) :
    |AdmWindow.VPhiR (phiW lam T) r - 2 / 5 * (Pst lam).L T * K (r * (Pst lam).L T / (2 * π))|
      ≤ 2 := by
  have hL : 0 < (Pst lam).L T := hW.L_pos
  have hwL : 2 * (1:ℝ) ≤ (Pst lam).L T := hW.two_w_le
  have hϱ : TaperProfile stdProfile := taperProfile_stdProfile
  have hwin : ∫ u, phiW lam T u ^ 2 * Real.cos (r * u)
      = ∫ u, vProf (u / (Pst lam).L T) * Real.cos (r * u)
          * Taper.phi stdProfile ((Pst lam).L T) 1 u ^ 2 :=
    integral_congr_ae (ae_of_all _ fun u => by
      show phiW lam T u ^ 2 * Real.cos (r * u)
        = vProf (u / (Pst lam).L T) * Real.cos (r * u)
          * Taper.phi stdProfile ((Pst lam).L T) 1 u ^ 2
      rw [phiW_sq]
      ring)
  have hcore := XiPrime.edge_estimate
    (h := fun u => vProf (u / (Pst lam).L T) * Real.cos (r * u))
    (p := fun u => Taper.phi stdProfile ((Pst lam).L T) 1 u ^ 2) hL one_pos hwL
    (fun u => by
      show |vProf (u / (Pst lam).L T) * Real.cos (r * u)| ≤ 1
      rw [abs_mul]
      calc |vProf (u / (Pst lam).L T)| * |Real.cos (r * u)| ≤ 1 * 1 :=
            mul_le_mul (abs_vProf_le_one _) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
        _ = 1 := mul_one 1)
    (fun u => sq_nonneg _)
    (fun u => pow_le_one₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u))
    (fun u hu => by
      show Taper.phi stdProfile ((Pst lam).L T) 1 u ^ 2 = 1
      rw [Taper.phi_eq_one hϱ one_pos hu, one_pow])
    (fun u hu => by
      show Taper.phi stdProfile ((Pst lam).L T) 1 u ^ 2 = 0
      rw [Taper.phi_eq_zero hϱ one_pos hu, zero_pow two_ne_zero])
    ((Taper.phi_continuous hϱ one_pos hwL).pow 2)
    ((vProf_continuous.comp (continuous_id.div_const _)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
  rw [Distinct839.ZeroKernel.VPhiR_eq_integral hW, hwin, ← integral_sharp_eq hK hL r]
  calc _ ≤ 2 * 1 := hcore
    _ = 2 := mul_one 2

/-- `|a L - (2/5) L| ≤ 2`: the case `r = 0` of the kernel comparison. -/
theorem abs_av_mul_sub_le
    (hK : ∀ t : ℝ, K t = ∫ u in (-(1:ℝ)/2)..(1/2), fCos u * Real.cos (2 * π * t * u))
    (hW : AdmWindow (phiW lam T) ((Pst lam).L T) 1 cW) :
    |AdmWindow.av (phiW lam T) ((Pst lam).L T) * (Pst lam).L T - 2 / 5 * (Pst lam).L T| ≤ 2 := by
  have h := abs_VPhiR_sub_le hK hW 0
  rw [hW.VPhiR_zero, zero_mul, zero_div, K_zero, mul_one] at h
  exact h

/-- `a ≥ 2/5 - 2/L`. -/
lemma av_lower
    (hK : ∀ t : ℝ, K t = ∫ u in (-(1:ℝ)/2)..(1/2), fCos u * Real.cos (2 * π * t * u))
    (hW : AdmWindow (phiW lam T) ((Pst lam).L T) 1 cW) :
    2 / 5 - 2 / (Pst lam).L T ≤ AdmWindow.av (phiW lam T) ((Pst lam).L T) := by
  have hL : 0 < (Pst lam).L T := hW.L_pos
  have h := (abs_le.mp (abs_av_mul_sub_le hK hW)).1
  refine le_of_mul_le_mul_right ?_ hL
  have e : (2 / 5 - 2 / (Pst lam).L T) * (Pst lam).L T = 2 / 5 * (Pst lam).L T - 2 := by
    rw [sub_mul, div_mul_cancel₀ _ hL.ne']
  rw [e]
  linarith

/-- `a ≥ 1/4` once `L ≥ 40`. -/
lemma av_ge_quarter
    (hK : ∀ t : ℝ, K t = ∫ u in (-(1:ℝ)/2)..(1/2), fCos u * Real.cos (2 * π * t * u))
    (hW : AdmWindow (phiW lam T) ((Pst lam).L T) 1 cW) (hL40 : 40 ≤ (Pst lam).L T) :
    1 / 4 ≤ AdmWindow.av (phiW lam T) ((Pst lam).L T) := by
  have h := av_lower hK hW
  have h2 : 2 / (Pst lam).L T ≤ 2 / 40 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL40
  linarith

/-- **Normalised kernel comparison.** `|Φ(r)/(a L) - K(r L / 2π)| ≤ 24/L` once `L ≥ 40`. -/
theorem abs_VPhiR_div_sub_K_le
    (hK : ∀ t : ℝ, K t = ∫ u in (-(1:ℝ)/2)..(1/2), fCos u * Real.cos (2 * π * t * u))
    (hW : AdmWindow (phiW lam T) ((Pst lam).L T) 1 cW) (hL40 : 40 ≤ (Pst lam).L T) (r : ℝ) :
    |AdmWindow.VPhiR (phiW lam T) r
          / (AdmWindow.av (phiW lam T) ((Pst lam).L T) * (Pst lam).L T)
        - K (r * (Pst lam).L T / (2 * π))| ≤ 24 / (Pst lam).L T :=
  Distinct839.ZeroKernel.abs_div_sub_le_aux hW.L_pos (av_ge_quarter hK hW hL40)
    (abs_VPhiR_sub_le hK hW r) (abs_av_mul_sub_le hK hW) (abs_K_le _)

end Simple673.ZeroKernel
