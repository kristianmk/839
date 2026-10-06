/-
Line889/ZeroKernel/Window.lean — the realised window and its dictionary.

At height `T` the profile `vProf` is realised by the window
`φ(u) = √(vProf(u/L)) · ϱ_ramp(u)` (upstream `Params.phiV`), with base parameters
`Pst lam = paramsOf stdProfile lam` (ramp width `w = 1`). This file identifies the objects of
`Pfam lam T` appearing in `gramKappa` with the window-class data of `φ`:
`φ̂ = AdmWindow.vHatR φ`, `a = AdmWindow.av φ L`, and records `φ(u)² = vProf(u/L) · ϱ_ramp(u)²`.

The cosine form of `Φ = (φ²)^`, `Φ(r) = ∫ φ(u)² cos(r u) du`, holds for every window of the
class; it is `Distinct839.ZeroKernel.VPhiR_eq_integral` (with `integrable_sq_mul_cos`) of
`Distinct839/ZeroKernel/Window.lean`, which this file imports for the later files.
-/
import Zeta23.XiPrime.QuarticWindow.Moments
import Distinct839.ZeroKernel.Window
import Line889.ZeroKernel.Profile

open scoped BigOperators
open Real Filter Topology MeasureTheory Zeta23

noncomputable section

namespace Line889.ZeroKernel

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
  unfold Distinct839.gramKappa
  rw [Pfam_phiHatR h0 h1, Pfam_a h0 h1]
  rfl

/-- The difference of two positions in bandwidth units. -/
lemma ypos_sub (lam T γ γ' : ℝ) :
    ypos (Pfam lam T) T γ - ypos (Pfam lam T) T γ' = (γ - γ') * (Pst lam).L T / (2 * π) := by
  show γ * (Pst lam).L T / (2 * π) - γ' * (Pst lam).L T / (2 * π) = _
  ring

end Line889.ZeroKernel
