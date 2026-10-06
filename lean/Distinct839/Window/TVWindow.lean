/-
Distinct839/Window/TVWindow.lean — a modulated ramp taper of bounded variation is an admissible
window.

Upstream (`Zeta23/XiPrime/QuarticWindow/ModWindow.lean`, `admWindow_phiM`) proves that
`φ_m = m · φ` (`φ = Taper.phi ϱ L w`, the ramp taper) is a `Zeta23.AdmWindow` when the modulating
factor `m` is nonincreasing on `[0, L/2]`: the total variation of a unimodal function is twice its
maximum. The six-harmonic profile is not monotone, so here the two total-variation fields are
proved from explicit bounds instead (structure `TVFactor`):

  `∫ |(m φ)'|   ≤ ∫_{-L/2}^{L/2} |m'|    + μ  ∫ |φ'|    ≤ τ₁ + 2μ  ≤ 2`,
  `∫ |(m² φ²)'| ≤ ∫_{-L/2}^{L/2} |(m²)'| + μ² ∫ |(φ²)'| ≤ τ₂ + 2μ² ≤ 2`,

where `μ` bounds `m` on the two ramps `L/2 - w ≤ |u| ≤ L/2`, the only place where `φ' ≠ 0`
(`integral_abs_deriv_mul_le_tv`). The second-derivative fields are proved as upstream does, from
`integral_abs_deriv2_mul_le` (which does not use monotonicity), with the same window constant
`cMod ϱ A B`. The factor is assumed `C²` on all of `ℝ` (true for the six-harmonic profile, which is
positive everywhere), which removes the neighbourhood bookkeeping of the upstream version.
-/
import Zeta23.XiPrime.QuarticWindow.ModWindow

open Real Set MeasureTheory Filter Topology
open Zeta23 Zeta23.XiPrime

noncomputable section

namespace Distinct839.Window

/-- A modulating factor of bounded variation, in the `u`-variable (support of the window
`[-L/2, L/2]`). `A`, `B` bound the first two derivatives on the core (they enter the window
constant `cMod ϱ A B`), `μ` bounds `m` on the two ramps, `τ₁` and `τ₂` bound the total variation
of `m` and `m²` on the core. No monotonicity is assumed. -/
structure TVFactor (m : ℝ → ℝ) (L w A B μ τ₁ τ₂ : ℝ) : Prop where
  A_nonneg : 0 ≤ A
  B_nonneg : 0 ≤ B
  contDiff : ContDiff ℝ 2 m
  even : ∀ u, m (-u) = m u
  nonneg : ∀ u, 0 ≤ m u
  le_one : ∀ u, |u| ≤ L / 2 → m u ≤ 1
  deriv_le : ∀ u, |u| ≤ L / 2 → |deriv m u| ≤ A / L
  deriv2_le : ∀ u, |u| ≤ L / 2 → |deriv (deriv m) u| ≤ B / L ^ 2
  edge_le : ∀ u, L / 2 - w ≤ |u| → |u| ≤ L / 2 → m u ≤ μ
  tv : ∫ u in (-(L / 2))..(L / 2), |deriv m u| ≤ τ₁
  tv_sq : ∫ u in (-(L / 2))..(L / 2), |deriv (fun u => m u ^ 2) u| ≤ τ₂
  budget : τ₁ + 2 * μ ≤ 2
  budget_sq : τ₂ + 2 * μ ^ 2 ≤ 2

variable {m ϱ : ℝ → ℝ} {L w A B μ τ₁ τ₂ : ℝ}

/-! ### The ramp taper is constant off the two ramps -/

/-- `φ' = 0` on the plateau `|u| < L/2 - w` and outside the support `|u| > L/2`. -/
lemma deriv_taper_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ}
    (hu : |u| < L / 2 - w ∨ L / 2 < |u|) : deriv (Taper.phi ϱ L w) u = 0 := by
  rcases hu with hu | hu
  · have hopen : IsOpen {v : ℝ | |v| < L / 2 - w} := continuous_abs.isOpen_preimage _ isOpen_Iio
    have hev : Taper.phi ϱ L w =ᶠ[nhds u] fun _ => (1:ℝ) := by
      filter_upwards [hopen.mem_nhds hu] with v hv using Taper.phi_eq_one hϱ hw (le_of_lt hv)
    rw [hev.deriv_eq, deriv_const]
  · have hopen : IsOpen {v : ℝ | L / 2 < |v|} := continuous_abs.isOpen_preimage _ isOpen_Ioi
    have hev : Taper.phi ϱ L w =ᶠ[nhds u] fun _ => (0:ℝ) := by
      filter_upwards [hopen.mem_nhds hu] with v hv using Taper.phi_eq_zero hϱ hw (le_of_lt hv)
    rw [hev.deriv_eq, deriv_const]

/-- `(φ²)' = 0` off the two ramps. -/
lemma deriv_taper_sq_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) {u : ℝ}
    (hu : |u| < L / 2 - w ∨ L / 2 < |u|) :
    deriv (fun u => Taper.phi ϱ L w u ^ 2) u = 0 := by
  have hd : HasDerivAt (Taper.phi ϱ L w) (deriv (Taper.phi ϱ L w) u) u :=
    (((Taper.phi_contDiff hϱ hw hwL).differentiable (by norm_num)) u).hasDerivAt
  have h2 : HasDerivAt (fun u => Taper.phi ϱ L w u ^ 2)
      (↑2 * Taper.phi ϱ L w u ^ (2 - 1) * deriv (Taper.phi ϱ L w) u) u := hd.pow 2
  rw [h2.deriv, deriv_taper_eq_zero hϱ hw hu, mul_zero]

/-! ### Total variation of a product with a ramp-like factor -/

/-- **Total variation of `F · G`.** If `G` is `C¹`, `0 ≤ G ≤ 1`, `G = 0` for `|u| ≥ L/2`, `G' = 0`
off the two ramps `L/2 - w ≤ |u| ≤ L/2`, and `F` is `C¹` with `|F| ≤ ν` on the ramps, then
`∫ |(F G)'| ≤ ∫_{-L/2}^{L/2} |F'| + ν ∫ |G'|`. -/
theorem integral_abs_deriv_mul_le_tv {F G : ℝ → ℝ} {ν : ℝ} (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) (hG0 : ∀ u, 0 ≤ G u) (hG1 : ∀ u, G u ≤ 1)
    (hGz : ∀ u, L / 2 ≤ |u| → G u = 0)
    (hG' : ∀ u, (|u| < L / 2 - w ∨ L / 2 < |u|) → deriv G u = 0)
    (hFe : ∀ u, L / 2 - w ≤ |u| → |u| ≤ L / 2 → |F u| ≤ ν) :
    ∫ u, |deriv (fun u => F u * G u) u|
      ≤ (∫ u in (-(L / 2))..(L / 2), |deriv F u|) + ν * ∫ u, |deriv G u| := by
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hF'c : Continuous (deriv F) := hF.continuous_deriv le_rfl
  have hG'c : Continuous (deriv G) := hG.continuous_deriv le_rfl
  have hGcs : HasCompactSupport G := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(L / 2)) (b := L / 2)) fun u hu => hGz u ?_
    rw [mem_Icc, not_and_or, not_le, not_le] at hu
    rcases hu with h | h
    · linarith [neg_abs_le u]
    · linarith [le_abs_self u]
  set I : ℝ → ℝ := (Icc (-(L / 2)) (L / 2)).indicator (fun u => |deriv F u|) with hI
  have hpt : ∀ u, |deriv (fun u => F u * G u) u| ≤ I u + ν * |deriv G u| := by
    intro u
    rw [deriv_fun_mul (hFd u) (hGd u)]
    rcases le_or_gt |u| (L / 2) with hu | hu
    · have hmem : u ∈ Icc (-(L / 2)) (L / 2) := abs_le.mp hu
      rw [hI, indicator_of_mem hmem]
      have h1 : |deriv F u * G u| ≤ |deriv F u| := by
        rw [abs_mul, abs_of_nonneg (hG0 u)]
        exact mul_le_of_le_one_right (abs_nonneg _) (hG1 u)
      have h2 : |F u * deriv G u| ≤ ν * |deriv G u| := by
        by_cases hd : deriv G u = 0
        · rw [hd]; simp
        · have hedge : L / 2 - w ≤ |u| := by
            by_contra hc
            exact hd (hG' u (Or.inl (lt_of_not_ge hc)))
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hFe u hedge hu) (abs_nonneg _)
      calc |deriv F u * G u + F u * deriv G u|
          ≤ |deriv F u * G u| + |F u * deriv G u| := abs_add_le _ _
        _ ≤ |deriv F u| + ν * |deriv G u| := add_le_add h1 h2
    · rw [hGz u hu.le, hG' u (Or.inr hu)]
      simp only [mul_zero, add_zero, abs_zero]
      exact indicator_nonneg (fun _ _ => abs_nonneg _) u
  have hIint : Integrable I := by
    rw [hI, integrable_indicator_iff measurableSet_Icc]
    exact (hF'c.abs.continuousOn).integrableOn_compact isCompact_Icc
  have hG'int : Integrable (fun u => |deriv G u|) := integrable_abs_of_cs hG'c hGcs.deriv
  calc ∫ u, |deriv (fun u => F u * G u) u|
      ≤ ∫ u, (I u + ν * |deriv G u|) :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
          (hIint.add (hG'int.const_mul ν)) (ae_of_all _ hpt)
    _ = (∫ u, I u) + ν * ∫ u, |deriv G u| := by
        rw [integral_add hIint (hG'int.const_mul ν), integral_const_mul]
    _ = (∫ u in (-(L / 2))..(L / 2), |deriv F u|) + ν * ∫ u, |deriv G u| := by
        rw [hI, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by linarith : -(L / 2) ≤ L / 2)]

/-! ### The window `m · φ` -/

namespace TVFactor

variable (hm : TVFactor m L w A B μ τ₁ τ₂)
include hm

lemma abs_le_one (u : ℝ) (hu : |u| ≤ L / 2) : |m u| ≤ 1 := by
  rw [abs_of_nonneg (hm.nonneg u)]; exact hm.le_one u hu

lemma phiM_even (u : ℝ) : phiM m ϱ L w (-u) = phiM m ϱ L w u := by
  simp only [phiM, hm.even, Taper.phi_even]

lemma phiM_nonneg (hϱ : TaperProfile ϱ) (u : ℝ) : 0 ≤ phiM m ϱ L w u :=
  mul_nonneg (hm.nonneg u) (Taper.phi_nonneg hϱ u)

lemma phiM_le_one (hϱ : TaperProfile ϱ) (hw : 0 < w) (u : ℝ) : phiM m ϱ L w u ≤ 1 := by
  rcases le_or_gt (L / 2) |u| with hu | hu
  · rw [phiM_eq_zero hϱ hw hu]; exact zero_le_one
  · calc phiM m ϱ L w u ≤ 1 * 1 :=
          mul_le_mul (hm.le_one u hu.le) (Taper.phi_le_one hϱ u) (Taper.phi_nonneg hϱ u)
            zero_le_one
      _ = 1 := mul_one 1

lemma phiM_contDiff (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 2 (phiM m ϱ L w) :=
  hm.contDiff.mul ((Taper.phi_contDiff hϱ hw hwL).of_le (by norm_num))

/-- `∫ |(m φ)'| ≤ τ₁ + 2μ ≤ 2`. -/
theorem integral_abs_deriv_phiM_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, |deriv (phiM m ϱ L w) u| ≤ 2 := by
  have hL : 0 ≤ L := by linarith
  have h := integral_abs_deriv_mul_le_tv (F := m) (G := Taper.phi ϱ L w) (ν := μ) hL
    (hm.contDiff.of_le (by norm_num)) ((Taper.phi_contDiff hϱ hw hwL).of_le (by norm_num))
    (Taper.phi_nonneg hϱ) (Taper.phi_le_one hϱ) (fun u hu => Taper.phi_eq_zero hϱ hw hu)
    (fun u hu => deriv_taper_eq_zero hϱ hw hu)
    (fun u h1 h2 => by rw [abs_of_nonneg (hm.nonneg u)]; exact hm.edge_le u h1 h2)
  rw [Taper.integral_abs_deriv_phi hϱ hw hwL] at h
  have := hm.tv
  have := hm.budget
  calc ∫ u, |deriv (phiM m ϱ L w) u| ≤ (∫ u in (-(L / 2))..(L / 2), |deriv m u|) + μ * 2 := h
    _ ≤ 2 := by linarith

/-- `∫ |(m² φ²)'| ≤ τ₂ + 2μ² ≤ 2`. -/
theorem integral_abs_deriv_phiM_sq_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, |deriv (fun u => phiM m ϱ L w u ^ 2) u| ≤ 2 := by
  have hL : 0 ≤ L := by linarith
  have hfun : (fun u => phiM m ϱ L w u ^ 2) = fun u => m u ^ 2 * Taper.phi ϱ L w u ^ 2 := by
    funext u; simp only [phiM]; ring
  rw [hfun]
  have hφ1 : ContDiff ℝ 1 (Taper.phi ϱ L w) := (Taper.phi_contDiff hϱ hw hwL).of_le (by norm_num)
  have h := integral_abs_deriv_mul_le_tv (F := fun u => m u ^ 2)
    (G := fun u => Taper.phi ϱ L w u ^ 2) (ν := μ ^ 2) (w := w) hL
    ((hm.contDiff.of_le (by norm_num)).pow 2) (hφ1.pow 2)
    (fun u => sq_nonneg _)
    (fun u => by
      calc Taper.phi ϱ L w u ^ 2 ≤ 1 ^ 2 :=
            pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 2
        _ = 1 := one_pow 2)
    (fun u hu => by simp only [Taper.phi_eq_zero hϱ hw hu, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow])
    (fun u hu => deriv_taper_sq_eq_zero hϱ hw hwL hu)
    (fun u h1 h2 => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (hm.nonneg u) (hm.edge_le u h1 h2) 2)
  rw [Taper.integral_abs_deriv_phi_sq hϱ hw hwL] at h
  have := hm.tv_sq
  have := hm.budget_sq
  calc ∫ u, |deriv (fun u => m u ^ 2 * Taper.phi ϱ L w u ^ 2) u|
      ≤ (∫ u in (-(L / 2))..(L / 2), |deriv (fun u => m u ^ 2) u|) + μ ^ 2 * 2 := h
    _ ≤ 2 := by linarith

/-- `‖(m φ)″‖₁ ≤ cMod ϱ A B / w` (the upstream argument, `integral_abs_deriv2_phiM_le`). -/
theorem integral_abs_deriv2_phiM_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ u, |deriv (deriv (phiM m ϱ L w)) u| ≤ cMod ϱ A B / w := by
  have hw0 : 0 < w := by linarith
  have h2wL : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hmain := integral_abs_deriv2_mul_le (F := m) (G := Taper.phi ϱ L w) (L := L) one_pos
    (div_nonneg hm.A_nonneg hL.le) (div_nonneg hm.B_nonneg (sq_nonneg L)) hm.contDiff.contDiffOn
    hm.abs_le_one hm.deriv_le hm.deriv2_le
    ((Taper.phi_contDiff hϱ hw0 h2wL).of_le (by norm_num)) (Taper.phi_hasCompactSupport hϱ hw0)
    (fun u hu => Taper.phi_eq_zero hϱ hw0 hu.le) (hm.phiM_contDiff hϱ hw0 h2wL)
    (phiM_hasCompactSupport hϱ hw0)
  have hI0 := integral_abs_phi_le hϱ hw0 h2wL
  have hI1 : ∫ u, |deriv (Taper.phi ϱ L w) u| = 2 := Taper.integral_abs_deriv_phi hϱ hw0 h2wL
  have hI2 : ∫ u, |deriv (deriv (Taper.phi ϱ L w)) u| = 2 * Taper.l1Deriv2 ϱ / w :=
    Taper.integral_abs_deriv2_phi hϱ hw0 h2wL
  rw [hI1, hI2] at hmain
  have hc := Taper.two_mul_l1Deriv2_le_cRho hϱ
  have hA := hm.A_nonneg
  have hB := hm.B_nonneg
  refine hmain.trans ?_
  have e1 : B / L ^ 2 * ∫ u, |Taper.phi ϱ L w u| ≤ B / w := by
    calc B / L ^ 2 * ∫ u, |Taper.phi ϱ L w u| ≤ B / L ^ 2 * L := by gcongr
      _ = B / L := by field_simp
      _ ≤ B / w := div_le_div_of_nonneg_left hB hw0 (by linarith)
  have e2 : 2 * (A / L) * 2 ≤ A / w := by
    rw [show 2 * (A / L) * 2 = 4 * A / L by ring, div_le_div_iff₀ hL hw0]; nlinarith
  have e3 : 2 * Taper.l1Deriv2 ϱ / w ≤ Taper.cRho ϱ / w := div_le_div_of_nonneg_right hc hw0.le
  have e4 : 0 ≤ A ^ 2 / w := by positivity
  calc B / L ^ 2 * (∫ u, |Taper.phi ϱ L w u|) + 2 * (A / L) * 2 + 2 * Taper.l1Deriv2 ϱ / w
      ≤ B / w + A / w + Taper.cRho ϱ / w + A ^ 2 / w := by linarith
    _ = cMod ϱ A B / w := by simp only [cMod]; ring

/-- `‖(m² φ²)″‖₁ ≤ cMod ϱ A B / w` (the upstream argument, `integral_abs_deriv2_phiM_sq_le`). -/
theorem integral_abs_deriv2_phiM_sq_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ u, |deriv (deriv (fun u => phiM m ϱ L w u ^ 2)) u| ≤ cMod ϱ A B / w := by
  have hw0 : 0 < w := by linarith
  have h2wL : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hU : IsOpen (univ : Set ℝ) := isOpen_univ
  have hsm : ContDiffOn ℝ 2 m univ := hm.contDiff.contDiffOn
  have hsm2 : ContDiff ℝ 2 (fun u => m u * m u) := hm.contDiff.mul hm.contDiff
  have hA := hm.A_nonneg
  have hB := hm.B_nonneg
  have hF0 : ∀ u, |u| ≤ L / 2 → |m u * m u| ≤ 1 := fun u hu => by
    rw [abs_mul]; have := hm.abs_le_one u hu; nlinarith [abs_nonneg (m u)]
  have hF1 : ∀ u, |u| ≤ L / 2 → |deriv (fun u => m u * m u) u| ≤ 2 * A / L := fun u hu => by
    rw [deriv_mul_eq hU hsm hsm (mem_univ u)]
    have h0 := hm.abs_le_one u hu
    have h1 := hm.deriv_le u hu
    calc |deriv m u * m u + m u * deriv m u| = 2 * (|m u| * |deriv m u|) := by
          rw [show deriv m u * m u + m u * deriv m u = 2 * (m u * deriv m u) by ring, abs_mul,
            abs_mul, abs_two]
      _ ≤ 2 * (1 * (A / L)) := by gcongr
      _ = 2 * A / L := by ring
  have hF2 : ∀ u, |u| ≤ L / 2 →
      |deriv (deriv (fun u => m u * m u)) u| ≤ (2 * B + 2 * A ^ 2) / L ^ 2 := fun u hu => by
    rw [deriv2_mul_eq hU hsm hsm (mem_univ u)]
    have h0 := hm.abs_le_one u hu
    have h1 := hm.deriv_le u hu
    have h2 := hm.deriv2_le u hu
    have hd0 := abs_nonneg (deriv m u)
    calc |deriv (deriv m) u * m u + 2 * (deriv m u * deriv m u) + m u * deriv (deriv m) u|
        ≤ |deriv (deriv m) u * m u| + |2 * (deriv m u * deriv m u)| + |m u * deriv (deriv m) u| :=
          abs_add_three _ _ _
      _ = 2 * (|deriv (deriv m) u| * |m u|) + 2 * (|deriv m u| * |deriv m u|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two]; ring
      _ ≤ 2 * (B / L ^ 2 * 1) + 2 * (A / L * (A / L)) := by gcongr
      _ = (2 * B + 2 * A ^ 2) / L ^ 2 := by field_simp
  have hφ := Taper.phi_contDiff hϱ hw0 h2wL
  have hG : ContDiff ℝ 2 (fun u => Taper.phi ϱ L w u ^ 2) := (hφ.pow 2).of_le (by norm_num)
  have hGcs : HasCompactSupport (fun u => Taper.phi ϱ L w u ^ 2) :=
    (Taper.phi_hasCompactSupport hϱ (L := L) hw0).comp_left (g := fun t => t ^ 2) (by norm_num)
  have hGzero : ∀ u, L / 2 < |u| → Taper.phi ϱ L w u ^ 2 = 0 := fun u hu => by
    rw [Taper.phi_eq_zero hϱ hw0 hu.le, zero_pow two_ne_zero]
  have hH : ContDiff ℝ 2 (fun u => (m u * m u) * (Taper.phi ϱ L w u ^ 2)) := by
    rw [← phiM_sq_eq]; exact (hm.phiM_contDiff hϱ hw0 h2wL).pow 2
  have hHcs : HasCompactSupport (fun u => (m u * m u) * (Taper.phi ϱ L w u ^ 2)) := by
    rw [← phiM_sq_eq]
    exact (phiM_hasCompactSupport hϱ hw0).comp_left (g := fun t => t ^ 2) (by norm_num)
  have hmain := integral_abs_deriv2_mul_le (F := fun u => m u * m u)
    (G := fun u => Taper.phi ϱ L w u ^ 2) (L := L) one_pos (by positivity : (0:ℝ) ≤ 2 * A / L)
    (by positivity : (0:ℝ) ≤ (2 * B + 2 * A ^ 2) / L ^ 2) hsm2.contDiffOn hF0 hF1 hF2 hG hGcs
    hGzero hH hHcs
  rw [phiM_sq_eq]
  have hI0 := integral_abs_phi_sq_le hϱ hw0 h2wL
  have hI1 : ∫ u, |deriv (fun u => Taper.phi ϱ L w u ^ 2) u| = 2 :=
    Taper.integral_abs_deriv_phi_sq hϱ hw0 h2wL
  have hI2 : ∫ u, |deriv (deriv (fun u => Taper.phi ϱ L w u ^ 2)) u| ≤ Taper.cRho ϱ / w :=
    Taper.integral_abs_deriv2_phi_sq_le hϱ hw h2wL
  rw [hI1] at hmain
  refine hmain.trans ?_
  have e1 : (2 * B + 2 * A ^ 2) / L ^ 2 * ∫ u, |Taper.phi ϱ L w u ^ 2| ≤ (B + A ^ 2) / w := by
    calc (2 * B + 2 * A ^ 2) / L ^ 2 * ∫ u, |Taper.phi ϱ L w u ^ 2|
        ≤ (2 * B + 2 * A ^ 2) / L ^ 2 * L := by gcongr
      _ = (2 * B + 2 * A ^ 2) / L := by field_simp
      _ ≤ (B + A ^ 2) / w := by rw [div_le_div_iff₀ hL hw0]; nlinarith
  have e2 : 2 * (2 * A / L) * 2 ≤ A / w := by
    rw [show 2 * (2 * A / L) * 2 = 8 * A / L by ring, div_le_div_iff₀ hL hw0]; nlinarith
  calc (2 * B + 2 * A ^ 2) / L ^ 2 * (∫ u, |Taper.phi ϱ L w u ^ 2|) + 2 * (2 * A / L) * 2
        + ∫ u, |deriv (deriv (fun u => Taper.phi ϱ L w u ^ 2)) u|
      ≤ (B + A ^ 2) / w + A / w + Taper.cRho ϱ / w := by linarith
    _ = cMod ϱ A B / w := by simp only [cMod]; ring

/-- **A modulated ramp taper of bounded variation is an admissible window.** -/
theorem admWindow (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    AdmWindow (phiM m ϱ L w) L w (cMod ϱ A B) where
  one_le_w := hw
  w8 := hwL
  four_le_c := four_le_cMod hϱ hm.A_nonneg hm.B_nonneg
  even := hm.phiM_even
  nonneg := hm.phiM_nonneg hϱ
  le_one := hm.phiM_le_one hϱ (by linarith)
  contDiff := hm.phiM_contDiff hϱ (by linarith) (by linarith)
  support := fun _ hu => phiM_eq_zero hϱ (by linarith) hu
  l1_deriv := hm.integral_abs_deriv_phiM_le hϱ (by linarith) (by linarith)
  l1_deriv_sq := hm.integral_abs_deriv_phiM_sq_le hϱ (by linarith) (by linarith)
  l1_deriv2 := hm.integral_abs_deriv2_phiM_le hϱ hw hwL
  l1_deriv2_sq := hm.integral_abs_deriv2_phiM_sq_le hϱ hw hwL

end TVFactor

end Distinct839.Window
