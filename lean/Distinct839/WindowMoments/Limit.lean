/-
Distinct839/WindowMoments/Limit.lean — the ratio constant of the realised window `vProf`.

For a valid parameter set `P` and an even `UnitProfile` `v` (continuous, values in `[0, 1]`),
the window `φ_v = P.phiV v T` realised by `P.atV v` has `φ_v² = winSq v P.ϱ L w`
(`phiV_sq`). With the estimates of `Ramp.lean`:

* `a_T → ∫v`, `b_T → ∫v²` at rate `2w/L` (`atV_a_close`, `atV_b_close`),
* `|g_T(y) - L · vConv v (y/L)| ≤ 4w` on `[0, L]`, and `g_T` is continuous (`atV_g_close`),

so the upstream limit theorems `XiPrime.tendsto_JT_of_autocorr_close` and
`XiPrime.tendsto_cRatio_cWin` give
`cRatio(λ₁(T); a_T, b_T, J_T) → cWin D λ v` (`tendsto_cRatio_atV`). This is the argument of the
upstream quartic window (`Zeta23/XiPrime/Window/Quartic.lean`), for a general profile.

The deliverables, for `P = paramsOf stdProfile lam` and `v = vProf`, `D(s) = s`:
`tendsto_cRatio_vProf` (the hypothesis `hc` of `gzMoments_atV_zeta` with
`cinf = cWin (fun s => s) lam vProf`) and `cWin_vProf_pos`. The window class `AdmWindow` is not
needed for these limits; `tendsto_cRatio_vProf` keeps it in its signature only to match the
interface it was requested with.
-/
import Distinct839.WindowMoments.Ramp
import Distinct839.ZeroKernel.Profile
import Zeta23.XiPrime.PrimeSide.Traces

open Real Set MeasureTheory Filter Topology Zeta23

noncomputable section

namespace Distinct839.WindowMoments

variable {P : Params} {v : ℝ → ℝ}

/-! ## The realised window -/

/-- `φ_v(u)² = v(u/L) · ramp(u)²` for the realised window `φ_v = P.phiV v T`. -/
lemma phiV_sq (hv : UnitProfile v) (T u : ℝ) :
    P.phiV v T u ^ 2 = winSq v P.ϱ (P.L T) P.w u := by
  show (Real.sqrt (max 0 (v (u / P.L T))) * Taper.phi P.ϱ (P.L T) P.w u) ^ 2 = _
  rw [mul_pow, Real.sq_sqrt (le_max_left _ _), max_eq_right (hv.nonneg _)]
  rfl

lemma phiV_sq_fun (hv : UnitProfile v) (T : ℝ) :
    (fun u => P.phiV v T u ^ 2) = winSq v P.ϱ (P.L T) P.w :=
  funext (phiV_sq hv T)

/-- `a_T` of `P.atV v` is within `2w/L` of `∫v`. -/
theorem atV_a_close (hP : P.Valid) (hv : UnitProfile v) (hev : ∀ s, v (-s) = v s) {T : ℝ}
    (hwL : 2 * P.w ≤ P.L T) :
    |(P.atV v T).a T - ∫ s in (-(1:ℝ)/2)..(1/2), v s| ≤ 2 * P.w / P.L T := by
  have hw : 0 < P.w := by linarith [hP.one_le_w]
  rw [Params.atV_a T hP hev]
  show |(P.L T)⁻¹ * (∫ u, P.phiV v T u ^ 2) - _| ≤ _
  rw [phiV_sq_fun hv T]
  exact abs_integral_winSq_sub_le hv hP.taper hw hwL

/-- `b_T` of `P.atV v` is within `2w/L` of `∫v²`. -/
theorem atV_b_close (hP : P.Valid) (hv : UnitProfile v) (hev : ∀ s, v (-s) = v s) {T : ℝ}
    (hwL : 2 * P.w ≤ P.L T) :
    |(P.atV v T).b T - ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2| ≤ 2 * P.w / P.L T := by
  have hw : 0 < P.w := by linarith [hP.one_le_w]
  rw [Params.atV_b T hP hev]
  show |(P.L T)⁻¹ * (∫ u, P.phiV v T u ^ 4) - _| ≤ _
  have h4 : (fun u => P.phiV v T u ^ 4) = fun u => winSq v P.ϱ (P.L T) P.w u ^ 2 := by
    funext u
    rw [← phiV_sq hv T u]
    ring
  rw [h4]
  exact abs_integral_winSq_sq_sub_le hv hP.taper hw hwL

/-- `g_T` of `P.atV v` is the autocorrelation of `winSq`. -/
lemma atV_g_eq (hP : P.Valid) (hv : UnitProfile v) (hev : ∀ s, v (-s) = v s) (T : ℝ) :
    (P.atV v T).g T = Params.autocorr (winSq v P.ϱ (P.L T) P.w) := by
  show AdmWindow.gv ((P.atV v T).phi T) = _
  rw [Params.atV_phi_valid T hP hev]
  show Params.autocorr (fun u => P.phiV v T u ^ 2) = _
  rw [phiV_sq_fun hv T]

/-- `|g_T(y) - L · vConv v (y/L)| ≤ 4w` for `0 ≤ y ≤ L`. -/
theorem atV_g_close (hP : P.Valid) (hv : UnitProfile v) (hev : ∀ s, v (-s) = v s) {T : ℝ}
    (hwL : 2 * P.w ≤ P.L T) {y : ℝ} (hy : y ∈ Icc (0:ℝ) (P.L T)) :
    |(P.atV v T).g T y - P.L T * XiPrime.vConv v (y / P.L T)| ≤ 4 * P.w := by
  have hw : 0 < P.w := by linarith [hP.one_le_w]
  rw [atV_g_eq hP hv hev T]
  exact abs_autocorr_winSq_sub_le hv hP.taper hw hwL hy.1 hy.2

/-- `g_T` is continuous. -/
lemma atV_g_continuous (hP : P.Valid) (hv : UnitProfile v) (hev : ∀ s, v (-s) = v s) {T : ℝ}
    (hwL : 2 * P.w ≤ P.L T) : Continuous ((P.atV v T).g T) := by
  have hw : 0 < P.w := by linarith [hP.one_le_w]
  rw [atV_g_eq hP hv hev T]
  exact Taper.autocorr_continuous_of_support _ (M := P.L T / 2)
    (winSq_continuous hv hP.taper hw hwL) (fun u hu => winSq_eq_zero hP.taper hw hu)

/-! ## The limit of the ratio constant -/

/-- **Ratio limit for a general profile.** For a valid `P`, an even `UnitProfile` `v` and a
density `D` continuous on `[0, 1]`, `cRatio(λ₁(T); a_T, b_T, J_T) → cWin D λ v` for the data of
`P.atV v`, provided the limit has a positive denominator. -/
theorem tendsto_cRatio_atV (hP : P.Valid) (hv : UnitProfile v) (hev : ∀ s, v (-s) = v s)
    {D : ℝ → ℝ} (hD : ContinuousOn D (Icc 0 1))
    (hden : 0 < (∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) + P.lam * XiPrime.jWin D P.lam v) :
    Tendsto (fun T => ThmD.cRatio (P.lam1 T) ((P.atV v T).a T) ((P.atV v T).b T)
      (XiPrime.JD D ((P.atV v T).g T) (P.L T) (l T))) atTop (𝓝 (XiPrime.cWin D P.lam v)) := by
  have hev8 := XiPrime.eventually_w8 hP
  have ha : Tendsto (fun T => (P.atV v T).a T) atTop (𝓝 (∫ s in (-(1:ℝ)/2)..(1/2), v s)) :=
    ThmD.tendsto_of_close hP.lam_pos (C := 2) (by
      filter_upwards [hev8] with T hT
      exact atV_a_close hP hv hev (by linarith [hP.one_le_w]))
  have hb : Tendsto (fun T => (P.atV v T).b T) atTop (𝓝 (∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2)) :=
    ThmD.tendsto_of_close hP.lam_pos (C := 2) (by
      filter_upwards [hev8] with T hT
      exact atV_b_close hP hv hev (by linarith [hP.one_le_w]))
  have hgc : ∀ᶠ T in atTop, Continuous ((P.atV v T).g T) := by
    filter_upwards [hev8] with T hT
    exact atV_g_continuous hP hv hev (by linarith [hP.one_le_w])
  have hg : ∀ᶠ T in atTop, ∀ y ∈ Icc (0:ℝ) (P.L T),
      |(P.atV v T).g T y - P.L T * XiPrime.vConv v (y / P.L T)| ≤ 4 * P.w := by
    filter_upwards [hev8] with T hT y hy
    exact atV_g_close hP hv hev (by linarith [hP.one_le_w]) hy
  have hJ := XiPrime.tendsto_JT_of_autocorr_close (v := v) (g := fun T => (P.atV v T).g T)
    hP hD hv.continuous hgc hg
  exact XiPrime.tendsto_cRatio_cWin hP.lam_pos (ThmD.tendsto_lam1 hP.lam_pos) ha hb hJ hden

/-! ## The profile `vProf` -/

lemma unitProfile_vProf : UnitProfile vProf :=
  ⟨ZeroKernel.vProf_continuous, ZeroKernel.vProf_nonneg, ZeroKernel.vProf_le_one⟩

lemma integral_vProf_pos : 0 < ∫ s in (-(1:ℝ)/2)..(1/2), vProf s :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    (ZeroKernel.vProf_continuous.intervalIntegrable _ _)
    (fun x _ => ZeroKernel.vProf_pos x) (by norm_num)

lemma integral_vProf_sq_pos : 0 < ∫ s in (-(1:ℝ)/2)..(1/2), vProf s ^ 2 :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    ((ZeroKernel.vProf_continuous.pow 2).intervalIntegrable _ _)
    (fun x _ => pow_pos (ZeroKernel.vProf_pos x) 2) (by norm_num)

/-- `𝒥(λ; vProf) ≥ 0` for `D(s) = s` and every `λ ≥ 0`. -/
lemma jWin_id_vProf_nonneg {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ XiPrime.jWin (fun s => s) lam vProf := by
  unfold XiPrime.jWin
  refine mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg zero_le_one fun r hr => ?_)
  exact mul_nonneg (mul_nonneg hlam hr.1)
    (XiPrime.vConv_nonneg (fun s _ => ZeroKernel.vProf_nonneg s) hr)

/-- The ratio limit for `vProf` at the standard parameters, without the window class. -/
theorem tendsto_cRatio_atV_vProf {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    Tendsto (fun T => ThmD.cRatio ((paramsOf stdProfile lam).lam1 T)
      (((paramsOf stdProfile lam).atV vProf T).a T) (((paramsOf stdProfile lam).atV vProf T).b T)
      (XiPrime.JD (fun s => s) (((paramsOf stdProfile lam).atV vProf T).g T)
        ((paramsOf stdProfile lam).L T) (l T))) atTop
      (𝓝 (XiPrime.cWin (fun s => s) lam vProf)) :=
  tendsto_cRatio_atV (paramsOf_valid taperProfile_stdProfile h0 h1) unitProfile_vProf
    ZeroKernel.vProf_even continuousOn_id
    (add_pos_of_pos_of_nonneg integral_vProf_sq_pos
      (mul_nonneg h0.le (jWin_id_vProf_nonneg h0.le)))

end Distinct839.WindowMoments

namespace Distinct839

open Distinct839.WindowMoments

/-- **The ratio constant of the realised window.** With `P = paramsOf stdProfile lam` and the
diagonal density `D(s) = s`, `cRatio(λ₁(T); a_T, b_T, J_T) → cWin D λ vProf` for the data of
`P.atV vProf`. This is the hypothesis `hc` of `gzMoments_atV_zeta` with
`cinf = cWin (fun s => s) lam vProf`. The window class hypothesis is not used (the estimates
need only continuity and `0 ≤ vProf ≤ 1`); it is kept to match the requested interface. -/
theorem tendsto_cRatio_vProf {lam : ℝ} (hlam : 1 / 2 ≤ lam) (hlam1 : lam < 1) {cW : ℝ}
    (_hAdm : ∀ T, 8 * (paramsOf stdProfile lam).w ≤ (paramsOf stdProfile lam).L T →
      AdmWindow ((paramsOf stdProfile lam).phiV vProf T) ((paramsOf stdProfile lam).L T)
        (paramsOf stdProfile lam).w cW) :
    Tendsto (fun T => ThmD.cRatio ((paramsOf stdProfile lam).lam1 T)
      (((paramsOf stdProfile lam).atV vProf T).a T) (((paramsOf stdProfile lam).atV vProf T).b T)
      (XiPrime.JD (fun s => s) (((paramsOf stdProfile lam).atV vProf T).g T)
        ((paramsOf stdProfile lam).L T) (l T))) atTop
      (𝓝 (XiPrime.cWin (fun s => s) lam vProf)) :=
  tendsto_cRatio_atV_vProf (by linarith) hlam1.le

/-- **Positivity of the limit constant**: `cWin (fun s => s) λ vProf > 0` for `λ > 0`. -/
theorem cWin_vProf_pos {lam : ℝ} (hlam : 0 < lam) : 0 < XiPrime.cWin (fun s => s) lam vProf :=
  XiPrime.cWin_pos integral_vProf_pos.ne' integral_vProf_sq_pos (jWin_id_vProf_nonneg hlam.le) hlam

end Distinct839
