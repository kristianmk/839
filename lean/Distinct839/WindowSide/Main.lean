/-
Distinct839/WindowSide/Main.lean — the window-side bookkeeping for the profile `vProf`.

The window at height `T` is `φ_v = √(v(u/L))·φ(u)` with `v = vProf` (`P.phiV vProf T`), where `φ`
is the taper of the parameters `P`. Given that these windows are admissible (`AdmWindow`, the
hypothesis `hAdm`, proved in `Distinct839/Window/`), this file supplies the remaining inputs of the
generic second-moment theorem `gzMoments_atV_zeta` and of the generic zero side:

* `WindowSide.av_vProf_close`, `WindowSide.bv_vProf_close`: `|a_T − ∫v| ≤ 2w/L` and
  `|b_T − ∫v²| ≤ 2w/L`. The window differs from the sharp cutoff only on the two ramps of width
  `w` (`Zeta23.XiPrime.edge_estimate`).
* `eventually_a_vProf`: `a_T ≥ 1/4` eventually (`a_T → ∫v = 2/5`);
  `eventually_b_vProf`: `b_T ≥ 1/8` eventually (`∫v² ≥ (∫v)² = 4/25`);
* `admFamily_vProf`: the family `(P.atV vProf T).phi T` is an `AdmFamily`;
* `windowZeroSide_vProf`: the zero side for the zeros of ζ (`windowZeroSide_atV_of`).

The theorems hold for any valid parameters `P`. The `_std` versions are the case
`P = paramsOf stdProfile lam`.
-/
import Distinct839.WindowSide.Profile
import Zeta23.XiPrime.QuarticWindow.Moments
import Zeta23.XiPrime.QuarticWindow.ZeroSide
import Zeta23.XiPrime.PrimeSide.Concrete
import Zeta23.Final

open Filter MeasureTheory

noncomputable section

namespace Distinct839

open Zeta23 Zeta23.XiPrime

namespace WindowSide

variable {P : Params}

/-! ## Moments of a profile window against the sharp cutoff -/

/-- For a continuous profile `g` with `|g| ≤ 1` and `n ≥ 1`:
`|L⁻¹ ∫ g(u/L) φ(u)ⁿ du − ∫_{−1/2}^{1/2} g| ≤ 2w/L`. -/
theorem moment_close (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) {g : ℝ → ℝ}
    (hgc : Continuous g) (hg : ∀ s, |g s| ≤ 1) {n : ℕ} (hn : n ≠ 0) :
    |(P.L T)⁻¹ * (∫ u, g (u / P.L T) * Taper.phi P.ϱ (P.L T) P.w u ^ n)
        - ∫ s in (-(1:ℝ)/2)..(1/2), g s| ≤ 2 * P.w / P.L T := by
  have hw0 : 0 < P.w := by linarith [hP.one_le_w]
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hwL : 2 * P.w ≤ P.L T := by linarith
  have hϱ := hP.taper
  have hsub : ∫ s in (-(1:ℝ)/2)..(1/2), g s
      = (P.L T)⁻¹ * ∫ u in Set.Icc (-(P.L T / 2)) (P.L T / 2), g (u / P.L T) := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -(P.L T / 2) ≤ P.L T / 2),
      integral_scale (g := g) hL, inv_mul_cancel_left₀ hL.ne']
  have hcore := edge_estimate (h := fun u => g (u / P.L T))
    (p := fun u => Taper.phi P.ϱ (P.L T) P.w u ^ n) hL hw0 hwL
    (fun u => hg _) (fun u => pow_nonneg (Taper.phi_nonneg hϱ u) n)
    (fun u => pow_le_one₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u))
    (fun u hu => by
      show Taper.phi P.ϱ (P.L T) P.w u ^ n = 1
      rw [Taper.phi_eq_one hϱ hw0 hu, one_pow])
    (fun u hu => by
      show Taper.phi P.ϱ (P.L T) P.w u ^ n = 0
      rw [Taper.phi_eq_zero hϱ hw0 hu, zero_pow hn])
    ((Taper.phi_continuous hϱ hw0 hwL).pow n) (hgc.comp (continuous_id.div_const _))
  rw [hsub]
  have e : (P.L T)⁻¹ * (∫ u, g (u / P.L T) * Taper.phi P.ϱ (P.L T) P.w u ^ n)
        - (P.L T)⁻¹ * ∫ u in Set.Icc (-(P.L T / 2)) (P.L T / 2), g (u / P.L T)
      = (P.L T)⁻¹ * ((∫ u, g (u / P.L T) * Taper.phi P.ϱ (P.L T) P.w u ^ n)
        - ∫ u in Set.Icc (-(P.L T / 2)) (P.L T / 2), g (u / P.L T)) := by ring
  rw [e, abs_mul, abs_of_pos (inv_pos.mpr hL)]
  calc (P.L T)⁻¹ * |(∫ u, g (u / P.L T) * Taper.phi P.ϱ (P.L T) P.w u ^ n)
        - ∫ u in Set.Icc (-(P.L T / 2)) (P.L T / 2), g (u / P.L T)|
      ≤ (P.L T)⁻¹ * (2 * P.w) := mul_le_mul_of_nonneg_left hcore (inv_pos.mpr hL).le
    _ = 2 * P.w / P.L T := by rw [div_eq_inv_mul]

/-! ## The window `φ_v` for `v = vProf` -/

/-- `φ_v² = v(u/L)·φ²` (no clipping, since `vProf > 0`). -/
theorem phiV_vProf_sq (P : Params) (T u : ℝ) :
    P.phiV vProf T u ^ 2 = vProf (u / P.L T) * Taper.phi P.ϱ (P.L T) P.w u ^ 2 := by
  rw [Params.phiV_eq, mul_pow, Real.sq_sqrt (le_max_left _ _), max_eq_right (vProf_pos _).le]

/-- `φ_v⁴ = v(u/L)²·φ⁴`. -/
theorem phiV_vProf_pow_four (P : Params) (T u : ℝ) :
    P.phiV vProf T u ^ 4 = vProf (u / P.L T) ^ 2 * Taper.phi P.ϱ (P.L T) P.w u ^ 4 := by
  have e : P.phiV vProf T u ^ 4 = (P.phiV vProf T u ^ 2) ^ 2 := by ring
  rw [e, phiV_vProf_sq]
  ring

/-- `|a_T − 2/5| ≤ 2w/L`, with `a_T = L⁻¹ ∫ φ_v²` and `∫ vProf = 2/5`. -/
theorem av_vProf_close (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) :
    |AdmWindow.av (P.phiV vProf T) (P.L T) - 2 / 5| ≤ 2 * P.w / P.L T := by
  have h := moment_close hP h8 continuous_vProf abs_vProf_le_one two_ne_zero
  rw [integral_vProf] at h
  have e : ∫ u, P.phiV vProf T u ^ 2 = ∫ u, vProf (u / P.L T) * Taper.phi P.ϱ (P.L T) P.w u ^ 2 :=
    integral_congr_ae (ae_of_all _ fun u => phiV_vProf_sq P T u)
  unfold AdmWindow.av
  rw [e]
  exact h

/-- `|b_T − ∫ vProf²| ≤ 2w/L`, with `b_T = L⁻¹ ∫ φ_v⁴`. -/
theorem bv_vProf_close (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) :
    |AdmWindow.bv (P.phiV vProf T) (P.L T) - ∫ s in (-(1:ℝ)/2)..(1/2), vProf s ^ 2|
      ≤ 2 * P.w / P.L T := by
  have hg : ∀ s, |vProf s ^ 2| ≤ 1 := fun s => by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (vProf_pos s).le (vProf_le_one s)
  have h := moment_close (g := fun s => vProf s ^ 2) hP h8 (continuous_vProf.pow 2) hg
    (n := 4) (by norm_num)
  have e : ∫ u, P.phiV vProf T u ^ 4
      = ∫ u, vProf (u / P.L T) ^ 2 * Taper.phi P.ϱ (P.L T) P.w u ^ 4 :=
    integral_congr_ae (ae_of_all _ fun u => phiV_vProf_pow_four P T u)
  unfold AdmWindow.bv
  rw [e]
  exact h

/-- `L ≥ 100 w` eventually. -/
theorem eventually_L_ge_hundred (hP : P.Valid) : ∀ᶠ T in atTop, 100 * P.w ≤ P.L T :=
  (Params.tendsto_L_of_valid hP).eventually_ge_atTop _

/-- At a height with `L ≥ 100 w`: `a_T ≥ 2/5 − 1/50 ≥ 1/4`. -/
theorem av_vProf_ge (hP : P.Valid) {T : ℝ} (hT : 100 * P.w ≤ P.L T) :
    1 / 4 ≤ AdmWindow.av (P.phiV vProf T) (P.L T) := by
  have hw1 := hP.one_le_w
  have hL : 0 < P.L T := by linarith
  have h := (abs_le.mp (av_vProf_close hP (by linarith))).1
  have hr : 2 * P.w / P.L T ≤ 1 / 50 := by rw [div_le_iff₀ hL]; linarith
  linarith

/-- At a height with `L ≥ 100 w`: `b_T ≥ 4/25 − 1/50 ≥ 1/8`. -/
theorem bv_vProf_ge (hP : P.Valid) {T : ℝ} (hT : 100 * P.w ≤ P.L T) :
    1 / 8 ≤ AdmWindow.bv (P.phiV vProf T) (P.L T) := by
  have hw1 := hP.one_le_w
  have hL : 0 < P.L T := by linarith
  have h := (abs_le.mp (bv_vProf_close hP (by linarith))).1
  have hr : 2 * P.w / P.L T ≤ 1 / 50 := by rw [div_le_iff₀ hL]; linarith
  have hsq := integral_vProf_sq_ge
  linarith

end WindowSide

open WindowSide

/-! ## The deliverables, for any valid parameters -/

/-- **`a_T ≥ 1/4` eventually** for the profile `vProf`. -/
theorem eventually_a_vProf {P : Params} (hP : P.Valid) :
    ∀ᶠ T in atTop, 1 / 4 ≤ (P.atV vProf T).a T := by
  filter_upwards [eventually_L_ge_hundred hP] with T hT
  rw [Params.atV_a T hP vProf_even]
  exact av_vProf_ge hP hT

/-- **`b_T ≥ 1/8` eventually** for the profile `vProf`. -/
theorem eventually_b_vProf {P : Params} (hP : P.Valid) :
    ∀ᶠ T in atTop, 1 / 8 ≤ AdmWindow.bv (P.phiV vProf T) (P.L T) := by
  filter_upwards [eventually_L_ge_hundred hP] with T hT
  exact bv_vProf_ge hP hT

/-- **The windows of `vProf` form an admissible family**, given that each window with `8w ≤ L` is
admissible. -/
theorem admFamily_vProf {P : Params} (hP : P.Valid) {cW : ℝ}
    (hAdm : ∀ T : ℝ, 8 * P.w ≤ P.L T → AdmWindow (P.phiV vProf T) (P.L T) P.w cW) :
    AdmFamily P (fun T => (P.atV vProf T).phi T) cW := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (eventually_L_ge_hundred hP)
  refine ⟨T₀, fun T hT => ?_⟩
  have hL := hT₀ T hT
  have h8 : 8 * P.w ≤ P.L T := by linarith [hP.one_le_w]
  show AdmWindow ((P.atV vProf T).phi T) (P.L T) P.w cW
    ∧ 1 / 8 ≤ AdmWindow.bv ((P.atV vProf T).phi T) (P.L T)
  rw [Params.atV_phi_valid T hP vProf_even]
  exact ⟨hAdm T h8, bv_vProf_ge hP hL⟩

/-- **The zero side for the zeros of ζ and the profile `vProf`** (`windowZeroSide_atV_of` with
`riemannVonMangoldt_zeta`). -/
theorem windowZeroSide_vProf {P : Params} (hP : P.Valid) {cW : ℝ}
    (hAdm : ∀ T : ℝ, 8 * P.w ≤ P.L T → AdmWindow (P.phiV vProf T) (P.L T) P.w cW) :
    WindowZeroSide zetaZeroConfig P (P.atV vProf) :=
  windowZeroSide_atV_of hP vProf_even hAdm (eventually_a_vProf hP) zetaZeroConfig
    riemannVonMangoldt_zeta

/-! ## The same for the standard parameters `paramsOf stdProfile lam` -/

section Std

variable {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1)
include h0 h1

theorem eventually_a_vProf_std :
    ∀ᶠ T in atTop, 1 / 4 ≤ ((paramsOf stdProfile lam).atV vProf T).a T :=
  eventually_a_vProf (paramsOf_valid taperProfile_stdProfile h0 h1)

theorem eventually_b_vProf_std :
    ∀ᶠ T in atTop, 1 / 8 ≤ AdmWindow.bv ((paramsOf stdProfile lam).phiV vProf T)
      ((paramsOf stdProfile lam).L T) :=
  eventually_b_vProf (paramsOf_valid taperProfile_stdProfile h0 h1)

theorem admFamily_vProf_std {cW : ℝ}
    (hAdm : ∀ T : ℝ, 8 * (paramsOf stdProfile lam).w ≤ (paramsOf stdProfile lam).L T →
      AdmWindow ((paramsOf stdProfile lam).phiV vProf T) ((paramsOf stdProfile lam).L T)
        (paramsOf stdProfile lam).w cW) :
    AdmFamily (paramsOf stdProfile lam) (fun T => ((paramsOf stdProfile lam).atV vProf T).phi T)
      cW :=
  admFamily_vProf (paramsOf_valid taperProfile_stdProfile h0 h1) hAdm

theorem windowZeroSide_vProf_std {cW : ℝ}
    (hAdm : ∀ T : ℝ, 8 * (paramsOf stdProfile lam).w ≤ (paramsOf stdProfile lam).L T →
      AdmWindow ((paramsOf stdProfile lam).phiV vProf T) ((paramsOf stdProfile lam).L T)
        (paramsOf stdProfile lam).w cW) :
    WindowZeroSide zetaZeroConfig (paramsOf stdProfile lam) ((paramsOf stdProfile lam).atV vProf) :=
  windowZeroSide_vProf (paramsOf_valid taperProfile_stdProfile h0 h1) hAdm

end Std

end Distinct839
