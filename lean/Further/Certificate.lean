/-
Further/Certificate.lean — the count certificate with general coefficients.

Function-abstract asymptotic bookkeeping, as in `Distinct839.Assembly.count_certificate_839` and
`Simple673.Assembly.count_certificate_673`, with the coefficients as parameters. All quantities
are arbitrary real functions of the height `T`: `N` (zeros with multiplicity), `lower` (the
count to be bounded from below), `tr` and `fr` (trace and squared Frobenius norm of `Ĝ`), `B`
(size of the tail), `Err` (the collected `o(N)` terms).

From the seam inequality

    a·tr − fr − B(a + 2√fr + B) ≤ ν·N + μ·lower + Err,          a ≥ 0,  μ > 0,

and the moment bounds `tr ≥ (1 − δ)N`, `fr ≤ (κ + δ)N` with `κ ≤ C₀`, it follows that

    ((a − ν − C₀)/μ − ε)·N ≤ lower      eventually.

The two older certificates are the cases `a = 2c`, `ν = ν₈₃₉ + b`, `μ = μ₈₃₉` and `a = 4`,
`ν = 2 + b`, `μ = 1 − x₁`.
-/
import Mathlib

noncomputable section

open Filter Asymptotics Topology Real

namespace Further

/-- **Count certificate with general coefficients.** -/
theorem count_certificate {a ν μ κ C₀ : ℝ} (ha : 0 ≤ a) (hμ : 0 < μ) (hC0 : 0 < C₀)
    (hκ : κ ≤ C₀) {N tr fr B lower Err : ℝ → ℝ}
    (hfr0 : ∀ᶠ T in atTop, 0 ≤ fr T)
    (h0 : ∀ᶠ T in atTop,
      a * tr T - fr T - B T * (a + 2 * Real.sqrt (fr T) + B T)
        ≤ ν * N T + μ * lower T + Err T)
    (hB0 : ∀ᶠ T in atTop, 0 ≤ B T)
    (hBto : Tendsto B atTop (𝓝 0))
    (hErr : Err =o[atTop] N)
    (hNtop : Tendsto N atTop atTop)
    (htrace : ∀ δ > (0:ℝ), ∀ᶠ T in atTop, (1 - δ) * N T ≤ tr T)
    (hfrob : ∀ δ > (0:ℝ), ∀ᶠ T in atTop, fr T ≤ (κ + δ) * N T) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, ((a - ν - C₀) / μ - ε) * N T ≤ lower T := by
  intro ε hε
  set δ : ℝ := μ * ε / (a + 3) with hδdef
  have hδ : 0 < δ := by positivity
  have hδeq : (a + 3) * δ = μ * ε := by
    simp only [hδdef]; field_simp
  set K : ℝ := C₀ + δ with hKdef
  have hK : 0 < K := by positivity
  set M : ℝ := a + 2 * K + 3 with hMdef
  have hM : 0 < M := by positivity
  have hBsmall : ∀ᶠ T in atTop, B T ≤ δ / M :=
    hBto.eventually (eventually_le_nhds (by positivity))
  have hBone : ∀ᶠ T in atTop, B T ≤ 1 :=
    hBto.eventually (eventually_le_nhds (show (0:ℝ) < 1 by norm_num))
  have hmain : ∀ᶠ T in atTop, ((a - ν - C₀) / μ - ε) * N T ≤ lower T := by
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
    have hBterm : B T * (a + 2 * Real.sqrt (fr T) + B T) ≤ δ * N T := by
      have hbr : a + 2 * Real.sqrt (fr T) + B T ≤ M * N T := by
        have e1 : a ≤ a * N T := le_mul_of_one_le_right ha hN1
        simp only [hMdef]
        nlinarith
      have hbr0 : 0 ≤ a + 2 * Real.sqrt (fr T) + B T := by
        have := Real.sqrt_nonneg (fr T)
        positivity
      calc B T * (a + 2 * Real.sqrt (fr T) + B T)
          ≤ (δ / M) * (M * N T) := mul_le_mul hBs hbr hbr0 (by positivity)
        _ = δ * N T := by field_simp
    have ha' : a * ((1 - δ) * N T) ≤ a * tr T := mul_le_mul_of_nonneg_left htr ha
    have hid : μ * (((a - ν - C₀) / μ - ε) * N T)
        = (a - ν - C₀) * N T - (a + 3) * δ * N T := by
      rw [hδeq]; field_simp
    have key : μ * (((a - ν - C₀) / μ - ε) * N T) ≤ μ * lower T := by
      rw [hid]
      simp only [hKdef] at hfb'
      linarith
    exact le_of_mul_le_mul_left key hμ
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hmain
  exact ⟨T₀, fun T hT => hT₀ T hT⟩

end Further
