/-
Simple673/WindowSide/Limit.lean — the ratio constant of the realised window `vProf`.

For a valid parameter set `P` and an even `UnitProfile` `v` (continuous, values in `[0, 1]`),
the generic theorem `Distinct839.WindowMoments.tendsto_cRatio_atV` gives
`cRatio(λ₁(T); a_T, b_T, J_T) → cWin D λ v` for the data of `P.atV v`, provided the limit has a
positive denominator (`a_T → ∫v`, `b_T → ∫v²` at rate `2w/L`, and `g_T` is within `4w` of
`L · vConv v (·/L)`; see `Distinct839/WindowMoments/Ramp.lean` and `Limit.lean`, which are
imported unchanged).

This file applies it to the profile `vProf` with `P = paramsOf stdProfile lam` and the diagonal
density `D(s) = s`:

* `WindowSide.tendsto_cRatio_atV_vProf`: the limit, with `cinf = cWin (fun s => s) lam vProf`
  (the hypothesis `hc` of `Distinct839.gzMoments_atV_zeta_std`);
* `WindowSide.cWin_vProf_pos`: the limit is positive (its hypothesis `hc0`).

The deliverable `windowMoments : WindowMomentsStatement` (`Spec2.lean`) is the pair. The window
class `AdmWindow` is not needed for these limits. This is the last section of
`Distinct839/WindowMoments/Limit.lean` ("The profile `vProf`") for the profile of the second
window.
-/
import Distinct839.WindowMoments.Limit
import Simple673.WindowSide.Profile
import Simple673.Spec2

open Real Set MeasureTheory Filter Topology Zeta23

noncomputable section

namespace Simple673

namespace WindowSide

/-! ## The profile `vProf` -/

/-- `vProf` is continuous with values in `[0, 1]`. -/
lemma unitProfile_vProf : Distinct839.WindowMoments.UnitProfile vProf :=
  ⟨continuous_vProf, fun s => (vProf_pos s).le, vProf_le_one⟩

lemma integral_vProf_pos : 0 < ∫ s in (-(1:ℝ)/2)..(1/2), vProf s :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    (continuous_vProf.intervalIntegrable _ _)
    (fun x _ => vProf_pos x) (by norm_num)

lemma integral_vProf_sq_pos : 0 < ∫ s in (-(1:ℝ)/2)..(1/2), vProf s ^ 2 :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_vProf.pow 2).intervalIntegrable _ _)
    (fun x _ => pow_pos (vProf_pos x) 2) (by norm_num)

/-- `𝒥(λ; vProf) ≥ 0` for `D(s) = s` and every `λ ≥ 0`. -/
lemma jWin_id_vProf_nonneg {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ XiPrime.jWin (fun s => s) lam vProf := by
  unfold XiPrime.jWin
  refine mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg zero_le_one fun r hr => ?_)
  exact mul_nonneg (mul_nonneg hlam hr.1)
    (XiPrime.vConv_nonneg (fun s _ => (vProf_pos s).le) hr)

/-- **The ratio constant of the realised window.** With `P = paramsOf stdProfile lam` and the
diagonal density `D(s) = s`, `cRatio(λ₁(T); a_T, b_T, J_T) → cWin D λ vProf` for the data of
`P.atV vProf`. -/
theorem tendsto_cRatio_atV_vProf {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    Tendsto (fun T => ThmD.cRatio ((paramsOf stdProfile lam).lam1 T)
      (((paramsOf stdProfile lam).atV vProf T).a T) (((paramsOf stdProfile lam).atV vProf T).b T)
      (XiPrime.JD (fun s => s) (((paramsOf stdProfile lam).atV vProf T).g T)
        ((paramsOf stdProfile lam).L T) (l T))) atTop
      (𝓝 (XiPrime.cWin (fun s => s) lam vProf)) :=
  Distinct839.WindowMoments.tendsto_cRatio_atV (paramsOf_valid taperProfile_stdProfile h0 h1)
    unitProfile_vProf vProf_even continuousOn_id
    (add_pos_of_pos_of_nonneg integral_vProf_sq_pos
      (mul_nonneg h0.le (jWin_id_vProf_nonneg h0.le)))

/-- **Positivity of the limit constant**: `cWin (fun s => s) λ vProf > 0` for `λ > 0`. -/
theorem cWin_vProf_pos {lam : ℝ} (hlam : 0 < lam) : 0 < XiPrime.cWin (fun s => s) lam vProf :=
  XiPrime.cWin_pos integral_vProf_pos.ne' integral_vProf_sq_pos (jWin_id_vProf_nonneg hlam.le) hlam

end WindowSide

/-! ## The deliverable -/

/-- **Layer W2, moments of the realised window.** For `0 < lam ≤ 1` the ratio constant of the
realised window tends to `cWin (fun s => s) lam vProf`, and this limit is positive. -/
theorem windowMoments : WindowMomentsStatement := fun _lam h0 h1 =>
  ⟨WindowSide.cWin_vProf_pos h0, WindowSide.tendsto_cRatio_atV_vProf h0 h1⟩

end Simple673
