/-
Distinct839/ZetaMoments/Moments.lean — the two moments of the ζ zero-side matrix, for an arbitrary
admissible profile family.

`zeta23` proves the two moments of the prime-side matrix for any admissible window family and any
coefficient family with (H1)–(H3) (`Zeta23.XiPrime.coeffMoments_atV`), and the counting endgame
for any window family whose zero-side matrix has these two moments
(`Zeta23.XiPrime.dist_bound_of_gzMoments_family`). For ζ the link between the two is missing
upstream. This file closes it:

* `ZetaMoments.Gz_atV_eq_GpC`: at a height where the window is admissible, the zero-side matrix of
  ζ equals the prime-side matrix with the coefficients `−Λ` (Weil's explicit formula, through
  `ZeroConfig.Gz_eq_Gp`, and `GpC_zetaCoeff_eq_Gp`);
* `gzMoments_atV_zeta`: `GzMoments zetaZeroConfig (P.atV v) c∞⁻¹` from the window facts only
  (admissibility of the family and the limit `c∞` of the ratio constant). Every ζ-specific input
  (explicit formula, Riemann–von Mangoldt, Γ-facts, Montgomery–Vaughan, [prop:PP], the
  Chebyshev–Mertens estimates) is discharged here by the theorems of `zeta23`;
* `gzMoments_atV_zeta_std`: the same for the standard parameters `paramsOf stdProfile lam`;
* `gzMoments_atV_zeta_quartic`: the quartic profile of `zeta23` satisfies the hypotheses, which
  shows that they are consistent.
-/
import Distinct839.ZetaMoments.Coeff
import Zeta23.XiPrime.PrimeSide.Final
import Zeta23.Final

open Filter Topology

noncomputable section

namespace Distinct839

open Zeta23 Zeta23.XiPrime

/-- **The H-EF bridge at one height**: if the window `(P.atV v T).phi T` is admissible, the zero-side
matrix of ζ equals the general prime-side matrix with the coefficients `−Λ`. -/
theorem ZetaMoments.Gz_atV_eq_GpC {P : Params} {v : ℝ → ℝ} {cW T : ℝ}
    (hW : AdmWindow ((P.atV v T).phi T) (P.L T) P.w cW) :
    zetaZeroConfig.Gz (P.atV v T) T = (P.atV v T).GpC T (zetaCoeffFamily.c T) := by
  rw [GpC_zetaCoeff_eq_Gp]
  exact zetaZeroConfig.Gz_eq_Gp (P.atV v T) T paperInputs_zeta.EF hW.L_pos hW.vC_contDiff
    (closure_minimal hW.support_subset isClosed_Icc)

/-- **The two moments of the ζ zero-side matrix for an admissible profile family.**

For valid parameters `P` with `λ < 1` and a profile `v` whose windows `(P.atV v T).phi T` are
eventually admissible (`AdmFamily`, with `b ≥ 1/8`), if the ratio constant
`cRatio(λ₁; a_T, b_T, J_T)` with diagonal density `D(s) = s` tends to `c∞ > 0`, then for every
`δ > 0` eventually `(1 − δ) N(T, 2T) ≤ tr Ĝ` and `‖Ĝ‖²_F ≤ (c∞⁻¹ + δ) N(T, 2T)`, where `Ĝ` is the
zero-side matrix of the zeros of ζ in hat units. No hypothesis about ζ remains. -/
theorem gzMoments_atV_zeta {P : Params} {v : ℝ → ℝ} {cW cinf : ℝ}
    (hP : P.Valid) (hlam1 : P.lam < 1)
    (hwin : AdmFamily P (fun T => (P.atV v T).phi T) cW)
    (hc0 : 0 < cinf)
    (hc : Tendsto (fun T => ThmD.cRatio (P.lam1 T) ((P.atV v T).a T) ((P.atV v T).b T)
        (JD (fun s => s) ((P.atV v T).g T) (P.L T) (l T))) atTop (𝓝 cinf)) :
    GzMoments zetaZeroConfig (P.atV v) cinf⁻¹ := by
  -- the prime side, for the coefficient family of ζ
  have hCM : CoeffMoments zetaZeroConfig (P.atV v) zetaCoeffFamily cinf⁻¹ :=
    coeffMoments_atV hP hlam1 hwin zetaCoeffFamily_hyps gammaFacts MV.mv_hilbert ppInput_of_PP
      riemannVonMangoldt_zeta hc0 hc
  -- the explicit formula identifies the zero side with the prime side, eventually
  obtain ⟨T₀, hT₀⟩ := hwin
  have hGz : ∀ᶠ T in atTop,
      zetaZeroConfig.Gz (P.atV v T) T = (P.atV v T).GpC T (zetaCoeffFamily.c T) := by
    filter_upwards [eventually_ge_atTop T₀] with T hT
    exact ZetaMoments.Gz_atV_eq_GpC (hT₀ T hT).1
  refine ⟨fun δ hδ => ?_, fun δ hδ => ?_⟩
  · filter_upwards [hCM.1 δ hδ, hGz] with T hT hG
    rw [hG]
    exact hT.1
  · filter_upwards [hCM.2 δ hδ, hGz] with T hT hG
    rw [hG]
    exact hT

/-- **`gzMoments_atV_zeta` for the standard parameters** `P = paramsOf stdProfile lam`
(taper profile `stdProfile`, ramp width `1`), `0 < lam < 1`. -/
theorem gzMoments_atV_zeta_std {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {v : ℝ → ℝ} {cW cinf : ℝ}
    (hwin : AdmFamily (paramsOf stdProfile lam)
      (fun T => ((paramsOf stdProfile lam).atV v T).phi T) cW)
    (hc0 : 0 < cinf)
    (hc : Tendsto (fun T => ThmD.cRatio ((paramsOf stdProfile lam).lam1 T)
        (((paramsOf stdProfile lam).atV v T).a T) (((paramsOf stdProfile lam).atV v T).b T)
        (JD (fun s => s) (((paramsOf stdProfile lam).atV v T).g T) ((paramsOf stdProfile lam).L T)
          (l T))) atTop (𝓝 cinf)) :
    GzMoments zetaZeroConfig ((paramsOf stdProfile lam).atV v) cinf⁻¹ :=
  gzMoments_atV_zeta (paramsOf_valid taperProfile_stdProfile h0 h1.le) h1 hwin hc0 hc

/-- **Sanity instance: the quartic profile.** The hypotheses of `gzMoments_atV_zeta_std` hold for the
quartic profile `vQuartic` of `zeta23`, with `c∞ = cWin(D, λ, vQuartic)`, `D(s) = s`
(admissibility: `admFamily_atV_quartic`; limit: `tendsto_cRatio_quartic`). -/
theorem gzMoments_atV_zeta_quartic {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    GzMoments zetaZeroConfig ((paramsOf stdProfile lam).atV vQuartic)
      (cWin (fun s => s) lam vQuartic)⁻¹ := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  have hD0 : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ (fun s : ℝ => s) x := fun x hx => hx.1
  exact gzMoments_atV_zeta_std h0 h1 (admFamily_atV_quartic hP) (cWin_vQuartic_pos hD0 h0 h1.le)
    (tendsto_cRatio_quartic (D := fun s => s) hP continuousOn_id hD0)

end Distinct839
