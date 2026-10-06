/-
Distinct839/WindowMoments/Ramp.lean — moments of a ramped profile against the sharp profile.

Let `v` be a continuous profile with values in `[0, 1]` (`UnitProfile v`), `ϱ` a taper profile
and `ramp = Taper.phi ϱ L w` the ramp of width `w` (equal to `1` on `|u| ≤ L/2 - w`, to `0` on
`|u| ≥ L/2`, with values in `[0, 1]`). The square of the window `√(v(u/L)) · ramp(u)` is
`winSq v ϱ L w u = v(u/L) · ramp(u)²`, and it differs from the sharp profile
`sharp v L u = 1_{[-L/2, L/2]}(u) · v(u/L)` only on the two ramps, of total length `2w`.
Hence, for `2w ≤ L`:

* `abs_integral_winSq_sub_le`:  `|L⁻¹ ∫ winSq - ∫_{-1/2}^{1/2} v| ≤ 2w/L`;
* `abs_integral_winSq_sq_sub_le`: `|L⁻¹ ∫ winSq² - ∫_{-1/2}^{1/2} v²| ≤ 2w/L`;
* `abs_autocorr_winSq_sub_le`: `|(winSq ⋆ winSq)(y) - L · vConv v (y/L)| ≤ 4w` for `0 ≤ y ≤ L`.

This is the argument of the upstream quartic window (`Zeta23/XiPrime/QuarticWindow/Moments.lean`:
`aQ_close`, `bQ_close`, `autocorr_phiMQsq_close`), written for a general profile: only continuity
and the bounds `0 ≤ v ≤ 1` are used. The edge estimate and the substitution are the upstream
`XiPrime.edge_estimate` and `XiPrime.integral_scale`.
-/
import Zeta23.XiPrime.Window.Quartic

open Real Set MeasureTheory Filter Topology Zeta23

noncomputable section

namespace Distinct839.WindowMoments

/-- Profiles handled here: continuous, with values in `[0, 1]`. -/
structure UnitProfile (v : ℝ → ℝ) : Prop where
  continuous : Continuous v
  nonneg : ∀ s, 0 ≤ v s
  le_one : ∀ s, v s ≤ 1

variable {v ϱ : ℝ → ℝ} {L w : ℝ}

/-- The square of the ramped window: `v(u/L) · ramp(u)²`. -/
def winSq (v ϱ : ℝ → ℝ) (L w : ℝ) (u : ℝ) : ℝ := v (u / L) * Taper.phi ϱ L w u ^ 2

/-- The sharp profile `1_{[-L/2, L/2]}(u) · v(u/L)`. -/
def sharp (v : ℝ → ℝ) (L : ℝ) (u : ℝ) : ℝ :=
  (Icc (-(L / 2)) (L / 2)).indicator (fun u => v (u / L)) u

/-! ## Elementary properties -/

lemma winSq_nonneg (hv : UnitProfile v) (u : ℝ) : 0 ≤ winSq v ϱ L w u :=
  mul_nonneg (hv.nonneg _) (sq_nonneg _)

lemma winSq_le_one (hv : UnitProfile v) (hϱ : TaperProfile ϱ) (u : ℝ) : winSq v ϱ L w u ≤ 1 := by
  unfold winSq
  calc v (u / L) * Taper.phi ϱ L w u ^ 2 ≤ 1 * 1 :=
        mul_le_mul (hv.le_one _) (pow_le_one₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u))
          (sq_nonneg _) zero_le_one
    _ = 1 := mul_one 1

lemma abs_winSq_le_one (hv : UnitProfile v) (hϱ : TaperProfile ϱ) (u : ℝ) :
    |winSq v ϱ L w u| ≤ 1 := by
  rw [abs_of_nonneg (winSq_nonneg hv u)]
  exact winSq_le_one hv hϱ u

lemma winSq_continuous (hv : UnitProfile v) (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (winSq v ϱ L w) :=
  (hv.continuous.comp (continuous_id.div_const L)).mul ((Taper.phi_continuous hϱ hw hwL).pow 2)

lemma winSq_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : L / 2 ≤ |u|) :
    winSq v ϱ L w u = 0 := by
  unfold winSq
  rw [Taper.phi_eq_zero hϱ hw hu]
  ring

lemma winSq_hasCompactSupport (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    HasCompactSupport (winSq v ϱ L w) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(L / 2)) (b := L / 2)) fun u hu => ?_
  apply winSq_eq_zero hϱ hw
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
  rcases hu with hu | hu
  · exact le_trans (by linarith) (neg_le_abs u)
  · exact le_trans (by linarith) (le_abs_self u)

lemma winSq_sq (u : ℝ) :
    winSq v ϱ L w u ^ 2 = v (u / L) ^ 2 * Taper.phi ϱ L w u ^ 4 := by
  unfold winSq
  ring

lemma sharp_nonneg (hv : UnitProfile v) (u : ℝ) : 0 ≤ sharp v L u :=
  Set.indicator_nonneg (fun _ _ => hv.nonneg _) u

lemma abs_sharp_le_one (hv : UnitProfile v) (u : ℝ) : |sharp v L u| ≤ 1 := by
  rw [abs_of_nonneg (sharp_nonneg hv u)]
  unfold sharp
  by_cases hm : u ∈ Icc (-(L / 2)) (L / 2)
  · rw [Set.indicator_of_mem hm]
    exact hv.le_one _
  · rw [Set.indicator_of_notMem hm]
    exact zero_le_one

lemma sharp_measurable (hv : UnitProfile v) : Measurable (sharp v L) :=
  Measurable.indicator (hv.continuous.comp (continuous_id.div_const L)).measurable measurableSet_Icc

lemma sharp_integrable (hv : UnitProfile v) : Integrable (sharp v L) :=
  (integrable_indicator_iff measurableSet_Icc).mpr
    (((hv.continuous.comp (continuous_id.div_const L)).continuousOn).integrableOn_compact
      isCompact_Icc)

/-- Substitution `u = L s` on the sharp window. -/
lemma setIntegral_Icc_comp_div {g : ℝ → ℝ} (hL : 0 < L) :
    ∫ u in Icc (-(L / 2)) (L / 2), g (u / L) = L * ∫ s in (-(1:ℝ)/2)..(1/2), g s := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2)]
  exact XiPrime.integral_scale hL

/-! ## The first two moments -/

/-- `|L⁻¹ ∫ v(u/L) ramp(u)² du - ∫_{-1/2}^{1/2} v| ≤ 2w/L`. -/
theorem abs_integral_winSq_sub_le (hv : UnitProfile v) (hϱ : TaperProfile ϱ) (hw : 0 < w)
    (hwL : 2 * w ≤ L) :
    |L⁻¹ * (∫ u, winSq v ϱ L w u) - ∫ s in (-(1:ℝ)/2)..(1/2), v s| ≤ 2 * w / L := by
  have hL : 0 < L := by linarith
  have hcore : |(∫ u, v (u / L) * Taper.phi ϱ L w u ^ 2)
      - ∫ u in Icc (-(L / 2)) (L / 2), v (u / L)| ≤ 2 * w :=
    XiPrime.edge_estimate (h := fun u => v (u / L)) (p := fun u => Taper.phi ϱ L w u ^ 2) hL hw hwL
      (fun u => by
        show |v (u / L)| ≤ 1
        rw [abs_of_nonneg (hv.nonneg _)]
        exact hv.le_one _)
      (fun u => sq_nonneg _)
      (fun u => pow_le_one₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u))
      (fun u hu => by
        show Taper.phi ϱ L w u ^ 2 = 1
        rw [Taper.phi_eq_one hϱ hw hu, one_pow])
      (fun u hu => by
        show Taper.phi ϱ L w u ^ 2 = 0
        rw [Taper.phi_eq_zero hϱ hw hu, zero_pow two_ne_zero])
      ((Taper.phi_continuous hϱ hw hwL).pow 2) (hv.continuous.comp (continuous_id.div_const L))
  rw [setIntegral_Icc_comp_div hL] at hcore
  have e : L⁻¹ * (∫ u, winSq v ϱ L w u) - ∫ s in (-(1:ℝ)/2)..(1/2), v s
      = L⁻¹ * ((∫ u, v (u / L) * Taper.phi ϱ L w u ^ 2)
          - L * ∫ s in (-(1:ℝ)/2)..(1/2), v s) := by
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul]
    rfl
  rw [e, abs_mul, abs_of_pos (inv_pos.mpr hL)]
  calc L⁻¹ * |(∫ u, v (u / L) * Taper.phi ϱ L w u ^ 2) - L * ∫ s in (-(1:ℝ)/2)..(1/2), v s|
      ≤ L⁻¹ * (2 * w) := mul_le_mul_of_nonneg_left hcore (inv_nonneg.mpr hL.le)
    _ = 2 * w / L := by rw [div_eq_inv_mul]

/-- `|L⁻¹ ∫ v(u/L)² ramp(u)⁴ du - ∫_{-1/2}^{1/2} v²| ≤ 2w/L`. -/
theorem abs_integral_winSq_sq_sub_le (hv : UnitProfile v) (hϱ : TaperProfile ϱ) (hw : 0 < w)
    (hwL : 2 * w ≤ L) :
    |L⁻¹ * (∫ u, winSq v ϱ L w u ^ 2) - ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2| ≤ 2 * w / L := by
  have hL : 0 < L := by linarith
  have hcore : |(∫ u, v (u / L) ^ 2 * Taper.phi ϱ L w u ^ 4)
      - ∫ u in Icc (-(L / 2)) (L / 2), v (u / L) ^ 2| ≤ 2 * w :=
    XiPrime.edge_estimate (h := fun u => v (u / L) ^ 2) (p := fun u => Taper.phi ϱ L w u ^ 4) hL
      hw hwL
      (fun u => by
        show |v (u / L) ^ 2| ≤ 1
        rw [abs_of_nonneg (sq_nonneg _)]
        exact pow_le_one₀ (hv.nonneg _) (hv.le_one _))
      (fun u => by positivity)
      (fun u => pow_le_one₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u))
      (fun u hu => by
        show Taper.phi ϱ L w u ^ 4 = 1
        rw [Taper.phi_eq_one hϱ hw hu, one_pow])
      (fun u hu => by
        show Taper.phi ϱ L w u ^ 4 = 0
        rw [Taper.phi_eq_zero hϱ hw hu]
        norm_num)
      ((Taper.phi_continuous hϱ hw hwL).pow 4)
      ((hv.continuous.comp (continuous_id.div_const L)).pow 2)
  rw [setIntegral_Icc_comp_div (g := fun s => v s ^ 2) hL] at hcore
  have hsq : ∫ u, winSq v ϱ L w u ^ 2 = ∫ u, v (u / L) ^ 2 * Taper.phi ϱ L w u ^ 4 :=
    integral_congr_ae (ae_of_all _ fun u => winSq_sq u)
  have e : L⁻¹ * (∫ u, winSq v ϱ L w u ^ 2) - ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2
      = L⁻¹ * ((∫ u, v (u / L) ^ 2 * Taper.phi ϱ L w u ^ 4)
          - L * ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) := by
    rw [hsq, mul_sub, ← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul]
  rw [e, abs_mul, abs_of_pos (inv_pos.mpr hL)]
  calc L⁻¹ * |(∫ u, v (u / L) ^ 2 * Taper.phi ϱ L w u ^ 4)
          - L * ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2|
      ≤ L⁻¹ * (2 * w) := mul_le_mul_of_nonneg_left hcore (inv_nonneg.mpr hL.le)
    _ = 2 * w / L := by rw [div_eq_inv_mul]

/-! ## The autocorrelation -/

/-- The autocorrelation of the sharp profile: `∫ sharp(u) sharp(u + y) du = L · vConv v (y/L)`
for `0 ≤ y ≤ L`. -/
theorem sharp_autocorr_eq (hL : 0 < L) {y : ℝ} (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    ∫ u, sharp v L u * sharp v L (u + y) = L * XiPrime.vConv v (y / L) := by
  have hind : ∀ u : ℝ, sharp v L u * sharp v L (u + y)
      = (Icc (-(L / 2)) (L / 2 - y)).indicator (fun u => v (u / L) * v ((u + y) / L)) u := by
    intro u
    unfold sharp
    by_cases hu : u ∈ Icc (-(L / 2)) (L / 2 - y)
    · have hu1 : u ∈ Icc (-(L / 2)) (L / 2) := ⟨hu.1, by linarith [hu.2]⟩
      have hu2 : u + y ∈ Icc (-(L / 2)) (L / 2) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
      rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu1, Set.indicator_of_mem hu2]
    · rw [Set.indicator_of_notMem hu]
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with hu | hu
      · rw [Set.indicator_of_notMem (s := Icc (-(L / 2)) (L / 2)) (a := u)
          (by rw [Set.mem_Icc]; intro h; linarith [h.1]), zero_mul]
      · rw [Set.indicator_of_notMem (s := Icc (-(L / 2)) (L / 2)) (a := u + y)
          (by rw [Set.mem_Icc]; intro h; linarith [h.2]), mul_zero]
  rw [integral_congr_ae (ae_of_all _ hind), integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(L / 2) ≤ L / 2 - y)]
  have hsub := intervalIntegral.integral_comp_div (a := -(L / 2)) (b := L / 2 - y)
    (f := fun s => v s * v (s + y / L)) hL.ne'
  have e1 : -(L / 2) / L = -(1:ℝ)/2 := by field_simp
  have e2 : (L / 2 - y) / L = 1/2 - y / L := by field_simp
  rw [e1, e2, smul_eq_mul] at hsub
  unfold XiPrime.vConv
  rw [← hsub]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [add_div]

/-- `‖winSq - sharp‖₁ ≤ 2w`. -/
theorem integral_abs_winSq_sub_sharp_le (hv : UnitProfile v) (hϱ : TaperProfile ϱ) (hw : 0 < w)
    (hwL : 2 * w ≤ L) :
    ∫ u, |winSq v ϱ L w u - sharp v L u| ≤ 2 * w := by
  have hL : 0 < L := by linarith
  set maj : ℝ → ℝ := fun u => (Icc (-(L / 2)) (-(L / 2) + w)).indicator (1 : ℝ → ℝ) u
      + (Icc (L / 2 - w) (L / 2)).indicator (1 : ℝ → ℝ) u with hmaj
  have hint1 : ∀ a b : ℝ, Integrable ((Icc a b).indicator (1 : ℝ → ℝ)) := fun a b =>
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hImaj : Integrable maj := (hint1 _ _).add (hint1 _ _)
  have hind0 : ∀ (s : Set ℝ) (u : ℝ), 0 ≤ s.indicator (1 : ℝ → ℝ) u := fun s u =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) u
  have hpt : ∀ u : ℝ, |winSq v ϱ L w u - sharp v L u| ≤ maj u := by
    intro u
    have hmaj0 : 0 ≤ maj u := add_nonneg (hind0 _ u) (hind0 _ u)
    rcases le_or_gt |u| (L / 2 - w) with hpl | hedge
    · -- on the core the two agree
      have huIcc : u ∈ Icc (-(L / 2)) (L / 2) := by
        rw [abs_le] at hpl
        exact ⟨by linarith [hpl.1], by linarith [hpl.2]⟩
      unfold winSq sharp
      rw [Taper.phi_eq_one hϱ hw hpl, one_pow, mul_one, Set.indicator_of_mem huIcc, sub_self,
        abs_zero]
      exact hmaj0
    · rcases le_or_gt |u| (L / 2) with hin | hout
      · -- on a ramp both lie in `[0, 1]`, and the majorant is `1`
        have hbound : |winSq v ϱ L w u - sharp v L u| ≤ 1 := by
          have h1 := winSq_nonneg (ϱ := ϱ) (L := L) (w := w) hv u
          have h2 := winSq_le_one (L := L) (w := w) hv hϱ u
          have h3 := sharp_nonneg (L := L) hv u
          have h4 := (abs_le.mp (abs_sharp_le_one (L := L) hv u)).2
          rw [abs_le]
          constructor <;> linarith
        have hone : (1:ℝ) ≤ maj u := by
          show (1:ℝ) ≤ (Icc (-(L / 2)) (-(L / 2) + w)).indicator (1 : ℝ → ℝ) u
            + (Icc (L / 2 - w) (L / 2)).indicator (1 : ℝ → ℝ) u
          rcases le_or_gt u 0 with hneg | hpos
          · have habs : |u| = -u := abs_of_nonpos hneg
            rw [habs] at hin hedge
            have hu1 : u ∈ Icc (-(L / 2)) (-(L / 2) + w) := ⟨by linarith, by linarith⟩
            have := hind0 (Icc (L / 2 - w) (L / 2)) u
            rw [Set.indicator_of_mem hu1, Pi.one_apply]
            linarith
          · have habs : |u| = u := abs_of_pos hpos
            rw [habs] at hin hedge
            have hu1 : u ∈ Icc (L / 2 - w) (L / 2) := ⟨by linarith, by linarith⟩
            have := hind0 (Icc (-(L / 2)) (-(L / 2) + w)) u
            rw [Set.indicator_of_mem hu1, Pi.one_apply]
            linarith
        linarith
      · -- outside both vanish
        have h1 : winSq v ϱ L w u = 0 := winSq_eq_zero hϱ hw hout.le
        have h2 : sharp v L u = 0 := by
          unfold sharp
          apply Set.indicator_of_notMem
          intro hm
          have : |u| ≤ L / 2 := abs_le.mpr ⟨hm.1, hm.2⟩
          linarith
        rw [h1, h2, sub_zero, abs_zero]
        exact hmaj0
  calc ∫ u, |winSq v ϱ L w u - sharp v L u|
      ≤ ∫ u, maj u :=
        integral_mono_of_nonneg (ae_of_all _ fun u => abs_nonneg _) hImaj (ae_of_all _ hpt)
    _ = 2 * w := by
        rw [hmaj, integral_add (hint1 _ _) (hint1 _ _),
          integral_indicator_one measurableSet_Icc, integral_indicator_one measurableSet_Icc,
          measureReal_def, measureReal_def, Real.volume_Icc, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
        ring

/-- **The autocorrelation of the ramped window.** For `0 ≤ y ≤ L`,
`|(winSq ⋆ winSq)(y) - L · vConv v (y/L)| ≤ 4w`. -/
theorem abs_autocorr_winSq_sub_le (hv : UnitProfile v) (hϱ : TaperProfile ϱ) (hw : 0 < w)
    (hwL : 2 * w ≤ L) {y : ℝ} (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    |Params.autocorr (winSq v ϱ L w) y - L * XiPrime.vConv v (y / L)| ≤ 4 * w := by
  have hL : 0 < L := by linarith
  set h : ℝ → ℝ := winSq v ϱ L w with hhdef
  set k : ℝ → ℝ := sharp v L with hkdef
  have hh1 : ∀ u, |h u| ≤ 1 := abs_winSq_le_one hv hϱ
  have hk1 : ∀ u, |k u| ≤ 1 := abs_sharp_le_one hv
  have hk_meas : Measurable k := sharp_measurable hv
  have hint_h : Integrable h :=
    (winSq_continuous hv hϱ hw hwL).integrable_of_hasCompactSupport (winSq_hasCompactSupport hϱ hw)
  have hint_k : Integrable k := sharp_integrable hv
  have hint_d : Integrable (fun u => h u - k u) := hint_h.sub hint_k
  have hint_hy : Integrable (fun u => h (u + y)) := hint_h.comp_add_right y
  have hint_ky : Integrable (fun u => k (u + y)) := hint_k.comp_add_right y
  have hint_dy : Integrable (fun u => h (u + y) - k (u + y)) := hint_hy.sub hint_ky
  have hmeas_hy : AEStronglyMeasurable (fun u => h (u + y)) volume := hint_hy.aestronglyMeasurable
  have hint_p1 : Integrable (fun u => (h u - k u) * h (u + y)) := by
    have := hint_d.bdd_mul (c := 1) hmeas_hy (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hh1 (u + y))
    exact this.congr (ae_of_all _ fun u => by ring)
  have hint_p2 : Integrable (fun u => k u * (h (u + y) - k (u + y))) :=
    hint_dy.bdd_mul (c := 1) hk_meas.aestronglyMeasurable (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hk1 u)
  have hint_hh : Integrable (fun u => h u * h (u + y)) := by
    have := hint_h.bdd_mul (c := 1) hmeas_hy (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hh1 (u + y))
    exact this.congr (ae_of_all _ fun u => by ring)
  have hint_kk : Integrable (fun u => k u * k (u + y)) :=
    hint_ky.bdd_mul (c := 1) hk_meas.aestronglyMeasurable (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hk1 u)
  have hCk : ∫ u, k u * k (u + y) = L * XiPrime.vConv v (y / L) := sharp_autocorr_eq hL hy0 hyL
  have hdecomp : Params.autocorr h y - L * XiPrime.vConv v (y / L)
      = (∫ u, (h u - k u) * h (u + y)) + ∫ u, k u * (h (u + y) - k (u + y)) := by
    have e1 : Params.autocorr h y - L * XiPrime.vConv v (y / L)
        = ∫ u, (h u * h (u + y) - k u * k (u + y)) := by
      rw [show Params.autocorr h y = ∫ u, h u * h (u + y) from rfl, ← hCk,
        integral_sub hint_hh hint_kk]
    rw [e1, ← integral_add hint_p1 hint_p2]
    exact integral_congr_ae (ae_of_all _ fun u => by ring)
  have hd2w : ∫ u, |h u - k u| ≤ 2 * w := integral_abs_winSq_sub_sharp_le hv hϱ hw hwL
  have hb1 : |∫ u, (h u - k u) * h (u + y)| ≤ 2 * w := by
    calc |∫ u, (h u - k u) * h (u + y)| ≤ ∫ u, |(h u - k u) * h (u + y)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ u, |h u - k u| := by
          refine integral_mono_of_nonneg (ae_of_all _ fun u => abs_nonneg _) hint_d.abs
            (ae_of_all _ fun u => ?_)
          show |(h u - k u) * h (u + y)| ≤ |h u - k u|
          rw [abs_mul]
          calc |h u - k u| * |h (u + y)| ≤ |h u - k u| * 1 :=
                mul_le_mul_of_nonneg_left (hh1 (u + y)) (abs_nonneg _)
            _ = |h u - k u| := mul_one _
      _ ≤ 2 * w := hd2w
  have hb2 : |∫ u, k u * (h (u + y) - k (u + y))| ≤ 2 * w := by
    have htrans : ∫ u, |h (u + y) - k (u + y)| = ∫ u, |h u - k u| :=
      integral_add_right_eq_self (fun u => |h u - k u|) y
    calc |∫ u, k u * (h (u + y) - k (u + y))|
        ≤ ∫ u, |k u * (h (u + y) - k (u + y))| := abs_integral_le_integral_abs
      _ ≤ ∫ u, |h (u + y) - k (u + y)| := by
          refine integral_mono_of_nonneg (ae_of_all _ fun u => abs_nonneg _) hint_dy.abs
            (ae_of_all _ fun u => ?_)
          show |k u * (h (u + y) - k (u + y))| ≤ |h (u + y) - k (u + y)|
          rw [abs_mul]
          calc |k u| * |h (u + y) - k (u + y)| ≤ 1 * |h (u + y) - k (u + y)| :=
                mul_le_mul_of_nonneg_right (hk1 u) (abs_nonneg _)
            _ = _ := one_mul _
      _ = ∫ u, |h u - k u| := htrans
      _ ≤ 2 * w := hd2w
  calc |Params.autocorr h y - L * XiPrime.vConv v (y / L)|
      = |(∫ u, (h u - k u) * h (u + y)) + ∫ u, k u * (h (u + y) - k (u + y))| := by rw [hdecomp]
    _ ≤ |∫ u, (h u - k u) * h (u + y)| + |∫ u, k u * (h (u + y) - k (u + y))| := abs_add_le _ _
    _ ≤ 4 * w := by linarith

end Distinct839.WindowMoments
