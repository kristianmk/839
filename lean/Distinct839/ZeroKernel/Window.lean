/-
Distinct839/ZeroKernel/Window.lean — the realised window and its dictionary.

At height `T` the profile `vProf` is realised by the window
`φ(u) = √(vProf(u/L)) · ϱ_ramp(u)` (upstream `Params.phiV`), with base parameters
`Pst lam = paramsOf stdProfile lam` (ramp width `w = 1`). This file identifies the objects of
`Pfam lam T` appearing in `gramKappa` with the window-class data of `φ`:
`φ̂ = AdmWindow.vHatR φ`, `a = AdmWindow.av φ L`, and writes `Φ = (φ²)^` as a cosine integral,
`Φ(r) = ∫ φ(u)² cos(r u) du`, with `φ(u)² = vProf(u/L) · ϱ_ramp(u)²`.
-/
import Zeta23.XiPrime.QuarticWindow.Moments
import Distinct839.ZeroKernel.Profile

open scoped BigOperators
open Real Filter Topology MeasureTheory Zeta23

noncomputable section

namespace Distinct839.ZeroKernel

/-! ## Base parameters and the window -/

/-- The base parameters: standard taper profile, exponent `lam`, ramp width `1`. -/
abbrev Pst (lam : ℝ) : Params := paramsOf stdProfile lam

/-- The window realising `vProf` at height `T`: `φ(u) = √(vProf(u/L)) · ϱ_ramp(u)`. -/
abbrev phiW (lam T : ℝ) : ℝ → ℝ := (Pst lam).phiV vProf T

lemma Pst_valid {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) : (Pst lam).Valid :=
  paramsOf_valid taperProfile_stdProfile h0 h1

/-- `φ(u)² = vProf(u/L) · ϱ_ramp(u)²`. -/
lemma phiW_sq (lam T u : ℝ) :
    phiW lam T u ^ 2
      = vProf (u / (Pst lam).L T) * Taper.phi stdProfile ((Pst lam).L T) 1 u ^ 2 := by
  show (Real.sqrt (max 0 (vProf (u / (Pst lam).L T)))
      * Taper.phi stdProfile ((Pst lam).L T) 1 u) ^ 2 = _
  rw [mul_pow, Real.sq_sqrt (le_max_left _ _), max_eq_right (vProf_nonneg _)]

/-! ## Dictionary for `Pfam lam T` -/

lemma Pfam_phiHatR {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) (T : ℝ) :
    (Pfam lam T).phiHatR T = AdmWindow.vHatR (phiW lam T) :=
  Params.atV_phiHatR T (Pst_valid h0 h1) vProf_even

lemma Pfam_a {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) (T : ℝ) :
    (Pfam lam T).a T = AdmWindow.av (phiW lam T) ((Pst lam).L T) :=
  Params.atV_a T (Pst_valid h0 h1) vProf_even

/-- `gramKappa` of the realised family in terms of the window-class data of `φ`. -/
lemma gramKappa_Pfam {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) (T γ γ' : ℝ) :
    gramKappa (Pfam lam T) T γ γ'
      = (AdmWindow.av (phiW lam T) ((Pst lam).L T) * (Pst lam).L T ^ 2)⁻¹ *
        ∑ k : Fin ((Pst lam).d T),
          AdmWindow.vHatR (phiW lam T)
              (γ - (T + (((k : ℕ) : ℤ) : ℝ) * (2 * π / (Pst lam).L T)))
            * AdmWindow.vHatR (phiW lam T)
              (γ' - (T + (((k : ℕ) : ℤ) : ℝ) * (2 * π / (Pst lam).L T))) := by
  unfold gramKappa
  rw [Pfam_phiHatR h0 h1, Pfam_a h0 h1]
  rfl

/-- The difference of two positions in bandwidth units. -/
lemma ypos_sub (lam T γ γ' : ℝ) :
    ypos (Pfam lam T) T γ - ypos (Pfam lam T) T γ' = (γ - γ') * (Pst lam).L T / (2 * π) := by
  show γ * (Pst lam).L T / (2 * π) - γ' * (Pst lam).L T / (2 * π) = _
  ring

/-! ## The transform of `φ²` as a cosine integral -/

/-- The real part of the transform of a real, continuous, compactly supported function is its
cosine transform. -/
lemma re_paperFT_ofReal {g : ℝ → ℝ} (hg : Continuous g) (hs : HasCompactSupport g) (r : ℝ) :
    (paperFT (fun u => (g u : ℂ)) r).re = ∫ u, g u * Real.cos (r * u) := by
  have hint : Integrable (fun u : ℝ => (g u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (Complex.continuous_ofReal.comp hg).mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
    · refine hs.mono fun u hu => ?_
      rw [Function.mem_support] at hu ⊢
      intro h0
      apply hu
      rw [h0, Complex.ofReal_zero, zero_mul]
  have h := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply] at h
  rw [paperFT_def, ← h]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  have e : Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  show ((g u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))).re = g u * Real.cos (r * u)
  rw [e, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- `Φ(r) = ∫ v(u)² cos(r u) du` for a window of the class. -/
lemma VPhiR_eq_integral {v : ℝ → ℝ} {L w c : ℝ} (hW : AdmWindow v L w c) (r : ℝ) :
    AdmWindow.VPhiR v r = ∫ u, v u ^ 2 * Real.cos (r * u) :=
  re_paperFT_ofReal hW.sq_continuous hW.sq_hasCompactSupport r

/-- Integrability of the integrand of the cosine form. -/
lemma integrable_sq_mul_cos {v : ℝ → ℝ} {L w c : ℝ} (hW : AdmWindow v L w c) (r : ℝ) :
    Integrable (fun u => v u ^ 2 * Real.cos (r * u)) := by
  refine Continuous.integrable_of_hasCompactSupport
    (hW.sq_continuous.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))) ?_
  refine hW.sq_hasCompactSupport.mono fun u hu => ?_
  rw [Function.mem_support] at hu ⊢
  intro h0
  apply hu
  rw [h0, zero_mul]

end Distinct839.ZeroKernel
