/-
Distinct839/Assembly/Certificate.lean — the count certificate for the constant `q`.

Function-abstract asymptotic bookkeeping, modelled on the upstream
`Zeta23.XiPrime.count_certificate_c3_fn`. All quantities are arbitrary real functions of the
height `T`: `N` (zeros with multiplicity), `lower` (distinct zeros), `tr` and `fr` (trace and
squared Frobenius norm of `Ĝ`), `B` (size of the tail), `Err` (the collected `o(N)` terms).

From the seam inequality

    2c·tr − fr − B(2c + 2√fr + B) ≤ (ν + b)·N + μ·lower + Err

and the moment bounds `tr ≥ (1 − δ)N`, `fr ≤ (κ + δ)N` with `κ ≤ C₀`, it follows that
`(q − ε)·N ≤ lower` eventually, because `2c − ν − b − C₀ = q·μ`.
-/
import Mathlib
import Distinct839.Assembly.Constants

noncomputable section

open Filter Asymptotics Topology Real

namespace Distinct839.Assembly

/-- **Count certificate for `q = 1645064/1960733`.** -/
theorem count_certificate_839 {κ : ℝ} (hκ : κ ≤ energyC0) {N tr fr B lower Err : ℝ → ℝ}
    (hfr0 : ∀ᶠ T in atTop, 0 ≤ fr T)
    (h0 : ∀ᶠ T in atTop,
      2 * clipC * tr T - fr T - B T * (2 * clipC + 2 * Real.sqrt (fr T) + B T)
        ≤ (nuC + spanB) * N T + muC * lower T + Err T)
    (hB0 : ∀ᶠ T in atTop, 0 ≤ B T)
    (hBto : Tendsto B atTop (𝓝 0))
    (hErr : Err =o[atTop] N)
    (hNtop : Tendsto N atTop atTop)
    (htrace : ∀ δ > (0:ℝ), ∀ᶠ T in atTop, (1 - δ) * N T ≤ tr T)
    (hfrob : ∀ δ > (0:ℝ), ∀ᶠ T in atTop, fr T ≤ (κ + δ) * N T) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (qFinal - ε) * N T ≤ lower T := by
  intro ε hε
  have hμ := muC_pos
  have hc := clipC_pos
  have hC0 := energyC0_pos
  set δ : ℝ := muC * ε / (2 * clipC + 3) with hδdef
  have hδ : 0 < δ := by positivity
  have hδeq : (2 * clipC + 3) * δ = muC * ε := by
    simp only [hδdef]; field_simp
  set K : ℝ := energyC0 + δ with hKdef
  have hK : 0 < K := by positivity
  set M : ℝ := 2 * clipC + 2 * K + 3 with hMdef
  have hM : 0 < M := by positivity
  have hBsmall : ∀ᶠ T in atTop, B T ≤ δ / M :=
    hBto.eventually (eventually_le_nhds (by positivity))
  have hBone : ∀ᶠ T in atTop, B T ≤ 1 :=
    hBto.eventually (eventually_le_nhds (show (0:ℝ) < 1 by norm_num))
  have hmain : ∀ᶠ T in atTop, (qFinal - ε) * N T ≤ lower T := by
    filter_upwards [h0, hfr0, hB0, hBsmall, hBone, hErr.def hδ, hNtop.eventually_ge_atTop 1,
      htrace δ hδ, hfrob δ hδ] with T hA hfr hB hBs hB1 hE hN1 htr hfb
    have hN0 : 0 ≤ N T := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hN0] at hE
    have hE' : Err T ≤ δ * N T := (le_abs_self _).trans hE
    have hfb' : fr T ≤ K * N T :=
      hfb.trans (mul_le_mul_of_nonneg_right (by simp only [hKdef]; linarith) hN0)
    -- `√fr ≤ (K + 1)·N`
    have hsq : Real.sqrt (fr T) ≤ (K + 1) * N T := by
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      have h1 : 1 ≤ (K + 1) * N T := by nlinarith
      have h2 : (K + 1) * N T ≤ ((K + 1) * N T) ^ 2 := by nlinarith
      nlinarith
    -- the tail term is at most `δ·N`
    have hBterm : B T * (2 * clipC + 2 * Real.sqrt (fr T) + B T) ≤ δ * N T := by
      have hbr : 2 * clipC + 2 * Real.sqrt (fr T) + B T ≤ M * N T := by
        have e1 : 2 * clipC ≤ 2 * clipC * N T := by nlinarith
        simp only [hMdef]
        nlinarith
      have hbr0 : 0 ≤ 2 * clipC + 2 * Real.sqrt (fr T) + B T := by
        have := Real.sqrt_nonneg (fr T)
        positivity
      calc B T * (2 * clipC + 2 * Real.sqrt (fr T) + B T)
          ≤ (δ / M) * (M * N T) := mul_le_mul hBs hbr hbr0 (by positivity)
        _ = δ * N T := by field_simp
    have h2c : 2 * clipC * ((1 - δ) * N T) ≤ 2 * clipC * tr T :=
      mul_le_mul_of_nonneg_left htr (by linarith)
    have hq : qFinal * muC = 2 * clipC - nuC - energyC0 - spanB := by
      rw [qFinal_mul_muC]; have := two_clipC_sub_nuC; linarith
    have hid : muC * ((qFinal - ε) * N T)
        = (2 * clipC - nuC - energyC0 - spanB) * N T - (2 * clipC + 3) * δ * N T := by
      linear_combination (N T) * hq + (N T) * hδeq
    have key : muC * ((qFinal - ε) * N T) ≤ muC * lower T := by
      rw [hid]
      simp only [hKdef] at hfb'
      linarith
    exact le_of_mul_le_mul_left key hμ
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hmain
  exact ⟨T₀, fun T hT => hT₀ T hT⟩

end Distinct839.Assembly
