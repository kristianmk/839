/-
Line889/Window/Admissible.lean — the realised six-harmonic window (third window) is admissible.

Upstream realises a profile `v` at height `T` as `φ_v(u) = √(max 0 (v(u/L))) · φ(u)`
(`Zeta23.Params.phiV`), with `φ` the ramp taper of width `w`. For `v = vProf = (2/5) fCos` this is
`phiM (mV L) ϱ L w` with `mV L u = √(vProf(u/L))` (`vProf > 0`, so the `max` is inactive). The
factor `mV L` is not monotone, so it is fed to the bounded-variation version `TVFactor` of
`Distinct839/Window/TVWindow.lean` (which does not depend on the window and is imported), with

* `A = 1`, `B = 17`: `|m'| ≤ 1/L`, `|m''| ≤ 17/L²`, from `m·m = h`, `h(u) = vProf(u/L)`,
  `|h'| ≤ (2/5)·(22/10)/L`, `|h''| ≤ (2/5)·36/L²` and `m ≥ 1/2`;
* `μ = 0.63`: on the ramps `|u/L| ∈ [3/8, 1/2]`, where `vProf ≤ (2/5)·0.892 ≤ 0.63²`;
* `τ₁ = 0.37`: `∫_{-L/2}^{L/2} |m'| = ∫_{-1/2}^{1/2} |vProf'|/(2√vProf)`, bounded pointwise by
  `0.27·fCos'² + 0.125` (from `z ≤ z²/(1/2) + 1/8`) and `∫ fCos'² ≤ 0.907`;
* `τ₂ = 0.40`: `∫_{-L/2}^{L/2} |(m²)'| = ∫_{-1/2}^{1/2} |vProf'| ≤ 0.27·∫ fCos'² + 0.15`.

The budgets are `τ₁ + 2μ = 1.63 ≤ 2` and `τ₂ + 2μ² = 1.1938 ≤ 2`.

The constants lie between those of the second window (`Simple673/Window/Admissible.lean`:
`B = 15`, `τ₁ = 0.26`, `τ₂ = 0.29`) and those of the first (`Distinct839/Window/Admissible.lean`:
`A = 2`, `B = 60`, `τ₁ = 0.60`, `τ₂ = 0.63`). No other layer depends on their values.
-/
import Line889.Window.Profile
import Line889.Spec2
import Distinct839.Window.TVWindow
import Zeta23.XiPrime.QuarticWindow.Moments
import Zeta23.Main

open Real Set MeasureTheory Filter Topology
open Zeta23 Zeta23.XiPrime

noncomputable section

namespace Line889.Window

/-! ### The profile and its derivative -/

/-- `vProf' = (2/5) fCos'`. -/
def vProf1 (s : ℝ) : ℝ := 2 / 5 * fCos1 s

lemma hasDerivAt_vProf (s : ℝ) : HasDerivAt vProf (vProf1 s) s :=
  (hasDerivAt_fCos s).const_mul (2 / 5)

variable {L w : ℝ}

/-- `h(u) = vProf(u/L)`. -/
def hV (L u : ℝ) : ℝ := vProf (u / L)

/-- The modulating factor `m(u) = √(vProf(u/L))`, written with the upstream `max 0` guard so that
`P.phiV vProf T = phiM (mV (P.L T)) P.ϱ (P.L T) P.w` holds by `rfl`. -/
def mV (L u : ℝ) : ℝ := √(max 0 (vProf (u / L)))

lemma hV_pos (u : ℝ) : 0 < hV L u := vProf_pos _

lemma mV_eq (u : ℝ) : mV L u = √(hV L u) := by
  rw [mV, max_eq_right (vProf_pos _).le]; rfl

lemma mV_mul_self (u : ℝ) : mV L u * mV L u = hV L u := by
  rw [mV_eq, Real.mul_self_sqrt (hV_pos u).le]

lemma mV_sq (u : ℝ) : mV L u ^ 2 = hV L u := by rw [sq, mV_mul_self]

lemma mV_nonneg (u : ℝ) : 0 ≤ mV L u := Real.sqrt_nonneg _

/-- `m ≥ 1/2` (in fact `m ≥ √0.306 ≥ 0.553`; `1/2` is all that is used). -/
lemma half_le_mV (u : ℝ) : 1 / 2 ≤ mV L u := by
  rw [mV_eq, Real.le_sqrt (by norm_num) (hV_pos u).le]
  have := vProf_ge (u / L)
  unfold hV
  linarith

lemma mV_le_one (u : ℝ) : mV L u ≤ 1 := by
  rw [mV_eq, Real.sqrt_le_left (by norm_num)]
  have := vProf_le (u / L)
  unfold hV
  linarith

lemma mV_even (u : ℝ) : mV L (-u) = mV L u := by
  simp only [mV, neg_div, vProf_even]

lemma hasDerivAt_hV (u : ℝ) : HasDerivAt (hV L) (vProf1 (u / L) / L) u := by
  have h := (hasDerivAt_vProf (u / L)).comp u ((hasDerivAt_id' u).div_const L)
  refine h.congr_deriv ?_
  ring

lemma deriv_hV : deriv (hV L) = fun u => vProf1 (u / L) / L :=
  funext fun u => (hasDerivAt_hV u).deriv

lemma hasDerivAt_deriv_hV (u : ℝ) :
    HasDerivAt (deriv (hV L)) (2 / 5 * fCos2 (u / L) / L / L) u := by
  rw [deriv_hV]
  have h := (((hasDerivAt_fCos1 (u / L)).comp u ((hasDerivAt_id' u).div_const L)).const_mul
    (2 / 5)).div_const L
  refine h.congr_deriv ?_
  ring

/-- `|h'| ≤ (2/5)·(22/10)/L = 0.88/L ≤ 1/L`. -/
lemma abs_deriv_hV_le (hL : 0 < L) (u : ℝ) : |deriv (hV L) u| ≤ 1 / L := by
  rw [(hasDerivAt_hV u).deriv, abs_div, abs_of_pos hL, vProf1, abs_mul]
  apply div_le_div_of_nonneg_right _ hL.le
  have := abs_fCos1_le (u / L)
  rw [abs_of_pos (by norm_num : (0:ℝ) < 2 / 5)]
  linarith

/-- `|h''| ≤ (2/5)·36/L² = 14.4/L² ≤ 15/L²`. -/
lemma abs_deriv2_hV_le (hL : 0 < L) (u : ℝ) : |deriv (deriv (hV L)) u| ≤ 15 / L ^ 2 := by
  rw [(hasDerivAt_deriv_hV u).deriv, show 2 / 5 * fCos2 (u / L) / L / L
    = 2 / 5 * fCos2 (u / L) / L ^ 2 by ring, abs_div, abs_of_pos (by positivity : 0 < L ^ 2),
    abs_mul]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have := abs_fCos2_le (u / L)
  rw [abs_of_pos (by norm_num : (0:ℝ) < 2 / 5)]
  linarith

lemma contDiff_mV : ContDiff ℝ 2 (mV L) := by
  have h : mV L = fun u => √(hV L u) := funext mV_eq
  rw [h]
  exact (contDiff_vProf.comp (contDiff_id.div_const L)).sqrt fun u => (hV_pos u).ne'

/-! ### Derivatives of `m = √h` through `m·m = h` -/

lemma deriv_mV_eq (u : ℝ) :
    deriv (mV L) u = deriv (hV L) u / (2 * mV L u) := by
  have hsm : ContDiffOn ℝ 2 (mV L) univ := contDiff_mV.contDiffOn
  have hev : (fun v => mV L v * mV L v) = hV L := funext mV_mul_self
  have hd : deriv (hV L) u = deriv (mV L) u * mV L u + mV L u * deriv (mV L) u := by
    rw [← hev]; exact deriv_mul_eq isOpen_univ hsm hsm (mem_univ u)
  have hf := half_le_mV (L := L) u
  rw [hd]
  field_simp
  ring

/-- `|m'| ≤ 1/L`. -/
lemma abs_deriv_mV_le (hL : 0 < L) (u : ℝ) : |deriv (mV L) u| ≤ 1 / L := by
  have hf := half_le_mV (L := L) u
  rw [deriv_mV_eq, abs_div, abs_of_pos (by linarith : 0 < 2 * mV L u)]
  exact (div_le_self (abs_nonneg _) (by linarith)).trans (abs_deriv_hV_le hL u)

/-- `|m''| ≤ 17/L²`. -/
lemma abs_deriv2_mV_le (hL : 0 < L) (u : ℝ) : |deriv (deriv (mV L)) u| ≤ 17 / L ^ 2 := by
  have hsm : ContDiffOn ℝ 2 (mV L) univ := contDiff_mV.contDiffOn
  have hev : (fun v => mV L v * mV L v) = hV L := funext mV_mul_self
  have hd2 : deriv (deriv (hV L)) u
      = deriv (deriv (mV L)) u * mV L u + 2 * (deriv (mV L) u * deriv (mV L) u)
        + mV L u * deriv (deriv (mV L)) u := by
    rw [← hev]; exact deriv2_mul_eq isOpen_univ hsm hsm (mem_univ u)
  have hf := half_le_mV (L := L) u
  have e : deriv (deriv (mV L)) u
      = (deriv (deriv (hV L)) u - 2 * (deriv (mV L) u * deriv (mV L) u)) / (2 * mV L u) := by
    rw [hd2]; field_simp; ring
  rw [e, abs_div, abs_of_pos (by linarith : 0 < 2 * mV L u)]
  have h1 := abs_deriv_mV_le hL u
  have h2 := abs_deriv2_hV_le hL u
  have hnum : |deriv (deriv (hV L)) u - 2 * (deriv (mV L) u * deriv (mV L) u)| ≤ 17 / L ^ 2 := by
    calc |deriv (deriv (hV L)) u - 2 * (deriv (mV L) u * deriv (mV L) u)|
        ≤ |deriv (deriv (hV L)) u| + |2 * (deriv (mV L) u * deriv (mV L) u)| := abs_sub _ _
      _ = |deriv (deriv (hV L)) u| + 2 * |deriv (mV L) u| ^ 2 := by
          rw [abs_mul, abs_two, abs_mul, sq]
      _ ≤ 15 / L ^ 2 + 2 * (1 / L) ^ 2 := by gcongr
      _ = 17 / L ^ 2 := by field_simp; ring
  calc |deriv (deriv (hV L)) u - 2 * (deriv (mV L) u * deriv (mV L) u)| / (2 * mV L u)
      ≤ |deriv (deriv (hV L)) u - 2 * (deriv (mV L) u * deriv (mV L) u)| :=
        div_le_self (abs_nonneg _) (by linarith)
    _ ≤ 17 / L ^ 2 := hnum

/-! ### The edge bound -/

/-- On the ramps `L/2 - w ≤ |u| ≤ L/2` (so `|u/L| ∈ [3/8, 1/2]` when `8w ≤ L`), `m ≤ 0.63`:
`vProf ≤ (2/5)·0.892 = 0.3568 ≤ 0.63² = 0.3969`. -/
lemma mV_le_edge (hL : 0 < L) (hwL : 8 * w ≤ L) {u : ℝ} (h1 : L / 2 - w ≤ |u|) (h2 : |u| ≤ L / 2) :
    mV L u ≤ 63 / 100 := by
  have hs1 : 3 / 8 ≤ |u / L| := by
    rw [abs_div, abs_of_pos hL, le_div_iff₀ hL]; linarith
  have hs2 : |u / L| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hL, div_le_iff₀ hL]; linarith
  have hf := fCos_le_edge hs1 hs2
  rw [mV_eq, Real.sqrt_le_left (by norm_num)]
  unfold hV vProf
  linarith

/-! ### Total variation of `m` and `m²` -/

/-- `|vProf'|/(2√vProf)`, the integrand of the total variation of `√vProf`. -/
def gV1 (s : ℝ) : ℝ := |2 / 5 * fCos1 s| / (2 * √(vProf s))

lemma sqrt_vProf_pos (s : ℝ) : 0 < √(vProf s) := Real.sqrt_pos.mpr (vProf_pos s)

lemma continuous_gV1 : Continuous gV1 :=
  ((continuous_const.mul continuous_fCos1).abs).div
    (continuous_const.mul continuous_vProf.sqrt) fun s => (mul_pos two_pos (sqrt_vProf_pos s)).ne'

lemma abs_deriv_mV_eq (hL : 0 < L) (u : ℝ) : |deriv (mV L) u| = L⁻¹ * gV1 (u / L) := by
  rw [deriv_mV_eq, (hasDerivAt_hV u).deriv, mV_eq, gV1, vProf1, hV,
    abs_div, abs_div, abs_of_pos hL, abs_of_pos (mul_pos two_pos (sqrt_vProf_pos _))]
  field_simp

/-- Pointwise `gV1 ≤ 0.27 fCos'² + 0.125` (from `z ≤ z²/(1/2) + 1/8` and `vProf ≥ 0.306`:
`(2/5)²/(4·0.306)/(1/2) = 40/153 ≤ 27/100`). -/
lemma gV1_le (s : ℝ) : gV1 s ≤ 27 / 100 * fCos1 s ^ 2 + 1 / 8 := by
  have hv := vProf_ge s
  have hy := sqrt_vProf_pos s
  have hz2 : gV1 s ^ 2 = (2 / 5 * fCos1 s) ^ 2 / (4 * vProf s) := by
    rw [gV1, div_pow, sq_abs, mul_pow, mul_pow, Real.sq_sqrt (vProf_pos s).le]
    ring
  have hz : gV1 s ≤ gV1 s ^ 2 / (1 / 2) + 1 / 8 := by nlinarith [sq_nonneg (gV1 s - 1 / 4)]
  calc gV1 s ≤ gV1 s ^ 2 / (1 / 2) + 1 / 8 := hz
    _ = (2 / 5 * fCos1 s) ^ 2 / (4 * vProf s) / (1 / 2) + 1 / 8 := by rw [hz2]
    _ ≤ (2 / 5 * fCos1 s) ^ 2 / (4 * (306 / 1000)) / (1 / 2) + 1 / 8 := by gcongr
    _ = 40 / 153 * fCos1 s ^ 2 + 1 / 8 := by ring
    _ ≤ 27 / 100 * fCos1 s ^ 2 + 1 / 8 := by nlinarith [sq_nonneg (fCos1 s)]

/-- `∫ gV1 ≤ 0.27·0.907 + 0.125 = 0.36989 ≤ 0.37`. -/
lemma integral_gV1_le : ∫ s in (-(1:ℝ)/2)..(1/2), gV1 s ≤ 37 / 100 := by
  have hc : Continuous fun s => 27 / 100 * fCos1 s ^ 2 + 1 / 8 :=
    (continuous_const.mul (continuous_fCos1.pow 2)).add continuous_const
  have i1 : IntervalIntegrable (fun s => 27 / 100 * fCos1 s ^ 2) volume (-(1:ℝ)/2) (1/2) :=
    (continuous_const.mul (continuous_fCos1.pow 2)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun _ : ℝ => (1 / 8 : ℝ)) volume (-(1:ℝ)/2) (1/2) :=
    continuous_const.intervalIntegrable _ _
  calc ∫ s in (-(1:ℝ)/2)..(1/2), gV1 s
      ≤ ∫ s in (-(1:ℝ)/2)..(1/2), (27 / 100 * fCos1 s ^ 2 + 1 / 8) :=
        intervalIntegral.integral_mono_on (by norm_num) (continuous_gV1.intervalIntegrable _ _)
          (hc.intervalIntegrable _ _) fun s _ => gV1_le s
    _ = 27 / 100 * (∫ s in (-(1:ℝ)/2)..(1/2), fCos1 s ^ 2) + 1 / 8 := by
        rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        norm_num
    _ ≤ 37 / 100 := by have := integral_fCos1_sq_le; linarith

/-- `∫_{-L/2}^{L/2} |m'| ≤ 0.37`. -/
lemma tv_mV (hL : 0 < L) : ∫ u in (-(L / 2))..(L / 2), |deriv (mV L) u| ≤ 37 / 100 := by
  simp_rw [abs_deriv_mV_eq hL]
  rw [intervalIntegral.integral_const_mul, integral_scale hL, ← mul_assoc, inv_mul_cancel₀ hL.ne',
    one_mul]
  exact integral_gV1_le

/-- Pointwise `|vProf'| ≤ 0.27 fCos'² + 0.15` (from `|x| ≤ x²/0.6 + 0.15`). -/
lemma abs_vProf1_le (s : ℝ) : |2 / 5 * fCos1 s| ≤ 27 / 100 * fCos1 s ^ 2 + 15 / 100 := by
  have h := sq_nonneg (|2 / 5 * fCos1 s| - 30 / 100)
  have h2 : |2 / 5 * fCos1 s| ^ 2 = 4 / 25 * fCos1 s ^ 2 := by rw [sq_abs]; ring
  nlinarith [sq_nonneg (fCos1 s)]

/-- `∫ |vProf'| ≤ 0.27·0.907 + 0.15 = 0.39489 ≤ 0.40`. -/
lemma integral_abs_vProf1_le : ∫ s in (-(1:ℝ)/2)..(1/2), |2 / 5 * fCos1 s| ≤ 40 / 100 := by
  have hc : Continuous fun s => 27 / 100 * fCos1 s ^ 2 + 15 / 100 :=
    (continuous_const.mul (continuous_fCos1.pow 2)).add continuous_const
  have i1 : IntervalIntegrable (fun s => 27 / 100 * fCos1 s ^ 2) volume (-(1:ℝ)/2) (1/2) :=
    (continuous_const.mul (continuous_fCos1.pow 2)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun _ : ℝ => (15 / 100 : ℝ)) volume (-(1:ℝ)/2) (1/2) :=
    continuous_const.intervalIntegrable _ _
  calc ∫ s in (-(1:ℝ)/2)..(1/2), |2 / 5 * fCos1 s|
      ≤ ∫ s in (-(1:ℝ)/2)..(1/2), (27 / 100 * fCos1 s ^ 2 + 15 / 100) :=
        intervalIntegral.integral_mono_on (by norm_num)
          ((continuous_const.mul continuous_fCos1).abs.intervalIntegrable _ _)
          (hc.intervalIntegrable _ _) fun s _ => abs_vProf1_le s
    _ = 27 / 100 * (∫ s in (-(1:ℝ)/2)..(1/2), fCos1 s ^ 2) + 15 / 100 := by
        rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        norm_num
    _ ≤ 40 / 100 := by have := integral_fCos1_sq_le; linarith

/-- `∫_{-L/2}^{L/2} |(m²)'| ≤ 0.40`. -/
lemma tv_sq_mV (hL : 0 < L) :
    ∫ u in (-(L / 2))..(L / 2), |deriv (fun u => mV L u ^ 2) u| ≤ 40 / 100 := by
  have hf : (fun u => mV L u ^ 2) = hV L := funext mV_sq
  have he : ∀ u, |deriv (hV L) u| = L⁻¹ * |2 / 5 * fCos1 (u / L)| := fun u => by
    rw [(hasDerivAt_hV u).deriv, vProf1, abs_div, abs_of_pos hL, div_eq_inv_mul]
  rw [hf]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,
    integral_scale (g := fun s => |2 / 5 * fCos1 s|) hL, ← mul_assoc, inv_mul_cancel₀ hL.ne',
    one_mul]
  exact integral_abs_vProf1_le

/-! ### The bounded-variation factor -/

/-- **`mV L` is a modulating factor of bounded variation** with `A = 1`, `B = 17`, `μ = 0.63`,
`τ₁ = 0.37`, `τ₂ = 0.40`. -/
theorem tvFactor_mV (hL : 0 < L) (hwL : 8 * w ≤ L) :
    Distinct839.Window.TVFactor (mV L) L w 1 17 (63 / 100) (37 / 100) (40 / 100) where
  A_nonneg := by norm_num
  B_nonneg := by norm_num
  contDiff := contDiff_mV
  even := mV_even
  nonneg := mV_nonneg
  le_one := fun u _ => mV_le_one u
  deriv_le := fun u _ => abs_deriv_mV_le hL u
  deriv2_le := fun u _ => abs_deriv2_mV_le hL u
  edge_le := fun _ h1 h2 => mV_le_edge hL hwL h1 h2
  tv := tv_mV hL
  tv_sq := tv_sq_mV hL
  budget := by norm_num
  budget_sq := by norm_num

/-- The realised window is the modulated taper with factor `mV` (`rfl`). -/
theorem phiV_vProf_eq (P : Params) (T : ℝ) :
    P.phiV vProf T = phiM (mV (P.L T)) P.ϱ (P.L T) P.w := rfl

/-- The window constant for general parameters: `cMod ϱ 1 17` (upstream's constant for a modulated
ramp whose factor has `|m'| ≤ 1/L`, `|m''| ≤ 17/L²`). -/
def cVProf (ϱ : ℝ → ℝ) : ℝ := cMod ϱ 1 17

/-- The window class for general valid parameters: the realised window `P.phiV vProf T` is
admissible at every height with `8w ≤ L_T`, with constant `cVProf P.ϱ`. -/
theorem admWindow_phiV_vProf {P : Params} (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T) :
    AdmWindow (P.phiV vProf T) (P.L T) P.w (cVProf P.ϱ) := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  rw [phiV_vProf_eq]
  exact (tvFactor_mV hL hwL).admWindow hP.taper hP.one_le_w hwL

end Line889.Window

namespace Line889

open Window

/-- The window constant of the third window at the standard taper:
`cWvProf = cMod stdProfile 1 17 = cRho stdProfile + 1 + 1² + 17`. -/
def cWvProf : ℝ := cMod stdProfile 1 17

/-- **The third window is admissible.** For `P = paramsOf stdProfile lam`
(`w = 1`, `L_T = λ log(T/2π)`) and every height `T` with `8w ≤ L_T`, the realised window
`φ_v(u) = √(vProf(u/L_T)) · φ_ramp(u)` satisfies the upstream window class `AdmWindow` with the
fixed constant `cWvProf`. Only `0 < λ ≤ 1` is used. -/
theorem admWindow_vProf {lam : ℝ} (hlam : 1 / 2 ≤ lam) (hlam1 : lam < 1) : AdmAt lam cWvProf :=
  fun _ hwL =>
    admWindow_phiV_vProf (paramsOf_valid taperProfile_stdProfile (by linarith) hlam1.le) hwL

/-- **Layer Window**: one constant serves all bandwidths `1/2 ≤ λ < 1`. -/
theorem windowStatement : WindowStatement :=
  ⟨cWvProf, fun _ h h1 => admWindow_vProf h h1⟩

end Line889
