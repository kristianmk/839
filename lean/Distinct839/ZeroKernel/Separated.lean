/-
Distinct839/ZeroKernel/Separated.lean — the Gram matrix of a separated set, at one height.

For real ordinates `γ_i`, real coefficients `x_i` and the realised window `φ` at height `T`:

  `∑_{i,j} x_i x_j κ(γ_i, γ_j) = (a L²)⁻¹ ∑_{0 ≤ k < d} (∑_i x_i φ̂(γ_i - τ_k))²`
  `  ≤ (a L²)⁻¹ ∑_{k ∈ ℤ} (∑_i x_i φ̂(γ_i - τ_k))² = (a L)⁻¹ ∑_{i,j} x_i x_j Φ(γ_i - γ_j)`
  `  = (a L)⁻¹ ∫ φ(u)² ∑_{i,j} x_i x_j cos((γ_i - γ_j) u) du`
  `  = a⁻¹ (2/5) ∫ w(s) ∑_{i,j} x_i x_j cos(2π (y_i - y_j) s) ds`,

with `w(s) = (5/2) φ(L s)²` and `y_i = γ_i L/2π` (substitution `u = L s`). The weight satisfies
`0 ≤ w ≤ fCos ≤ gMaj` on `|s| ≤ 1/2` (the ramp is at most `1`; `MajorantPointwise`) and `w = 0`
outside, so `SeparatedBound` bounds the last integral by `LMaj ∑ x_i²` when the `y_i` are
`sep`-separated (`sum_gramKappa_le`). No condition on the position of the ordinates is needed:
the truncated sum of squares is below the full one.
-/
import Distinct839.ZeroKernel.Kernel

open scoped BigOperators
open Real Filter Topology MeasureTheory Zeta23

noncomputable section

namespace Distinct839.ZeroKernel

/-- A nonnegative series dominates its partial sum over `0 ≤ k < d`. -/
lemma sum_fin_le_hasSum {f : ℤ → ℝ} {S : ℝ} (d : ℕ) (hf : HasSum f S) (h0 : ∀ k, 0 ≤ f k) :
    ∑ k : Fin d, f ((k : ℕ) : ℤ) ≤ S := by
  classical
  have e : ∑ k : Fin d, f ((k : ℕ) : ℤ)
      = ∑ k ∈ (Finset.range d).map Nat.castEmbedding, f k := by
    rw [Finset.sum_map]
    exact Fin.sum_univ_eq_sum_range (fun n : ℕ => f (n : ℤ)) d
  rw [e]
  exact sum_le_hasSum _ (fun k _ => h0 k) hf

/-- Poisson summation for the square of a linear combination of shifted transforms:
`∑_{k ∈ ℤ} (∑_i x_i φ̂(γ_i - τ_k))² = L ∑_{i,j} x_i x_j Φ(γ_i - γ_j)`. -/
lemma hasSum_sq_comb {v : ℝ → ℝ} {L w c : ℝ} (hW : AdmWindow v L w c) (T : ℝ)
    {ι : Type*} [Fintype ι] (γ x : ι → ℝ) :
    HasSum (fun k : ℤ => (∑ i, x i * AdmWindow.vHatR v (γ i - (T + k * (2 * π / L)))) ^ 2)
      (L * ∑ i, ∑ j, x i * x j * AdmWindow.VPhiR v (γ i - γ j)) := by
  have h : HasSum (fun k : ℤ => ∑ i, ∑ j, x i * x j *
        (AdmWindow.vHatR v (γ i - (T + k * (2 * π / L)))
          * AdmWindow.vHatR v (γ j - (T + k * (2 * π / L)))))
      (∑ i, ∑ j, x i * x j * (L * AdmWindow.VPhiR v (γ i - γ j))) :=
    hasSum_sum fun i _ => hasSum_sum fun j _ =>
      (hW.hasSum_vHatR_mul T (γ i) (γ j)).mul_left (x i * x j)
  convert h using 1
  · funext k
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- The quadratic form of `Φ` as an integral against `φ²`:
`∑_{i,j} x_i x_j Φ(γ_i - γ_j) = ∫ φ(u)² ∑_{i,j} x_i x_j cos((γ_i - γ_j) u) du`. -/
lemma sum_VPhiR_eq_integral {v : ℝ → ℝ} {L w c : ℝ} (hW : AdmWindow v L w c)
    {ι : Type*} [Fintype ι] (γ x : ι → ℝ) :
    ∑ i, ∑ j, x i * x j * AdmWindow.VPhiR v (γ i - γ j)
      = ∫ u, v u ^ 2 * ∑ i, ∑ j, x i * x j * Real.cos ((γ i - γ j) * u) := by
  have hint : ∀ i j,
      Integrable (fun u => x i * x j * (v u ^ 2 * Real.cos ((γ i - γ j) * u))) :=
    fun i j => (integrable_sq_mul_cos hW (γ i - γ j)).const_mul _
  calc ∑ i, ∑ j, x i * x j * AdmWindow.VPhiR v (γ i - γ j)
      = ∑ i, ∑ j, ∫ u, x i * x j * (v u ^ 2 * Real.cos ((γ i - γ j) * u)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [VPhiR_eq_integral hW, integral_const_mul]
    _ = ∫ u, ∑ i, ∑ j, x i * x j * (v u ^ 2 * Real.cos ((γ i - γ j) * u)) := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => hint i j]
    _ = ∫ u, v u ^ 2 * ∑ i, ∑ j, x i * x j * Real.cos ((γ i - γ j) * u) := by
        refine integral_congr_ae (ae_of_all _ fun u => ?_)
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring

/-- Substitution `u = L s`: `∫ g(u) du = L ∫ g(L s) ds` for `L > 0`. -/
lemma integral_eq_mul_integral_comp (g : ℝ → ℝ) {L : ℝ} (hL : 0 < L) :
    ∫ u, g u = L * ∫ s, g (L * s) := by
  rw [Measure.integral_comp_mul_left g L, smul_eq_mul, abs_of_pos (inv_pos.mpr hL), ← mul_assoc,
    mul_inv_cancel₀ hL.ne', one_mul]

/-- The weight of the separated-set bound: `w(s) = (5/2) φ(L s)²`. -/
def wSep (lam T : ℝ) (s : ℝ) : ℝ := 5 / 2 * phiW lam T ((Pst lam).L T * s) ^ 2

lemma wSep_nonneg (lam T s : ℝ) : 0 ≤ wSep lam T s := by
  unfold wSep
  positivity

lemma wSep_measurable {lam cW T : ℝ} (hW : AdmWindow (phiW lam T) ((Pst lam).L T) 1 cW) :
    Measurable (wSep lam T) := by
  have hc : Continuous (wSep lam T) :=
    continuous_const.mul ((hW.continuous.comp (continuous_const.mul continuous_id)).pow 2)
  exact hc.measurable

/-- `w ≤ gMaj`: on `|s| ≤ 1/2`, `w(s) = fCos(s) · ramp² ≤ fCos(s) ≤ gMaj(s)`; outside, `w = 0`. -/
lemma wSep_le_gMaj {lam cW T : ℝ} (hMP : MajorantPointwise)
    (hW : AdmWindow (phiW lam T) ((Pst lam).L T) 1 cW) (s : ℝ) :
    wSep lam T s ≤ gMaj s := by
  have hL : 0 < (Pst lam).L T := hW.L_pos
  by_cases hs : |s| ≤ 1 / 2
  · have hφ : phiW lam T ((Pst lam).L T * s) ^ 2 ≤ vProf s := by
      rw [phiW_sq, mul_div_cancel_left₀ s hL.ne']
      have h1 : 0 ≤ Taper.phi stdProfile ((Pst lam).L T) 1 ((Pst lam).L T * s) :=
        Taper.phi_nonneg taperProfile_stdProfile _
      have h2 : Taper.phi stdProfile ((Pst lam).L T) 1 ((Pst lam).L T * s) ≤ 1 :=
        Taper.phi_le_one taperProfile_stdProfile _
      calc vProf s * Taper.phi stdProfile ((Pst lam).L T) 1 ((Pst lam).L T * s) ^ 2
          ≤ vProf s * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ h1 h2) (vProf_nonneg s)
        _ = vProf s := mul_one _
    calc wSep lam T s = 5 / 2 * phiW lam T ((Pst lam).L T * s) ^ 2 := rfl
      _ ≤ 5 / 2 * vProf s := by linarith
      _ = fCos s := by unfold vProf; ring
      _ ≤ gMaj s := hMP s hs
  · have hs' : 1 / 2 < |s| := lt_of_not_ge hs
    have hfar : (Pst lam).L T / 2 ≤ |(Pst lam).L T * s| := by
      rw [abs_mul, abs_of_pos hL]
      nlinarith
    have h0 : phiW lam T ((Pst lam).L T * s) = 0 := hW.support _ hfar
    rw [wSep, h0]
    norm_num
    exact gMaj_nonneg s

/-- **The separated-set bound, at one height.** If the ordinates `γ_i` are `sep`-separated in
bandwidth units, then `∑_{i,j} x_i x_j κ(γ_i, γ_j) ≤ (2/(5a)) · LMaj · ∑ x_i²`. -/
theorem sum_gramKappa_le {lam cW T : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hW : AdmWindow (phiW lam T) ((Pst lam).L T) 1 cW)
    (ha : 0 < AdmWindow.av (phiW lam T) ((Pst lam).L T))
    (hMP : MajorantPointwise) (hSB : SeparatedBound)
    (ι : Type) [Fintype ι] (γ x : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → sep ≤ |ypos (Pfam lam T) T (γ i) - ypos (Pfam lam T) T (γ j)|) :
    ∑ i, ∑ j, x i * gramKappa (Pfam lam T) T (γ i) (γ j) * x j
      ≤ 2 / (5 * AdmWindow.av (phiW lam T) ((Pst lam).L T)) * LMaj * ∑ i, x i ^ 2 := by
  set L := (Pst lam).L T with hLdef
  set a := AdmWindow.av (phiW lam T) L with hadef
  set d := (Pst lam).d T with hddef
  have hL : 0 < L := hW.L_pos
  have hc : 0 < a * L ^ 2 := by positivity
  set F : ι → ℤ → ℝ := fun i k => AdmWindow.vHatR (phiW lam T) (γ i - (T + k * (2 * π / L)))
    with hFdef
  -- (A) the quadratic form is a truncated sum of squares
  have hA : ∑ i, ∑ j, x i * gramKappa (Pfam lam T) T (γ i) (γ j) * x j
      = (a * L ^ 2)⁻¹ * ∑ k : Fin d, (∑ i, x i * F i ((k : ℕ) : ℤ)) ^ 2 := by
    have hpt : ∀ i j, x i * gramKappa (Pfam lam T) T (γ i) (γ j) * x j
        = ∑ k : Fin d, (a * L ^ 2)⁻¹ * ((x i * F i ((k : ℕ) : ℤ)) * (x j * F j ((k : ℕ) : ℤ))) := by
      intro i j
      rw [gramKappa_Pfam h0 h1, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hFdef]
      ring
    rw [Finset.mul_sum]
    calc ∑ i, ∑ j, x i * gramKappa (Pfam lam T) T (γ i) (γ j) * x j
        = ∑ i, ∑ j, ∑ k : Fin d,
            (a * L ^ 2)⁻¹ * ((x i * F i ((k : ℕ) : ℤ)) * (x j * F j ((k : ℕ) : ℤ))) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j
      _ = ∑ i, ∑ k : Fin d, ∑ j,
            (a * L ^ 2)⁻¹ * ((x i * F i ((k : ℕ) : ℤ)) * (x j * F j ((k : ℕ) : ℤ))) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k : Fin d, ∑ i, ∑ j,
            (a * L ^ 2)⁻¹ * ((x i * F i ((k : ℕ) : ℤ)) * (x j * F j ((k : ℕ) : ℤ))) :=
          Finset.sum_comm
      _ = ∑ k : Fin d, (a * L ^ 2)⁻¹ * (∑ i, x i * F i ((k : ℕ) : ℤ)) ^ 2 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [sq (∑ i, x i * F i ((k : ℕ) : ℤ)), Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
  -- (B) truncated sum of squares below the full Poisson sum
  have hB : ∑ k : Fin d, (∑ i, x i * F i ((k : ℕ) : ℤ)) ^ 2
      ≤ L * ∑ i, ∑ j, x i * x j * AdmWindow.VPhiR (phiW lam T) (γ i - γ j) :=
    sum_fin_le_hasSum d (hasSum_sq_comb hW T γ x) (fun k => sq_nonneg _)
  -- (C), (D) the cosine form and the substitution `u = L s`
  set y : ι → ℝ := fun i => ypos (Pfam lam T) T (γ i) with hydef
  have hD : ∑ i, ∑ j, x i * x j * AdmWindow.VPhiR (phiW lam T) (γ i - γ j)
      = L * (2 / 5 * ∫ s, wSep lam T s *
          (∑ i, ∑ j, x i * x j * Real.cos (2 * π * (y i - y j) * s))) := by
    rw [sum_VPhiR_eq_integral hW γ x,
      integral_eq_mul_integral_comp
        (fun u => phiW lam T u ^ 2 * ∑ i, ∑ j, x i * x j * Real.cos ((γ i - γ j) * u)) hL]
    congr 1
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    have harg : ∀ i j, (γ i - γ j) * (L * s) = 2 * π * (y i - y j) * s := by
      intro i j
      have hLP : (Pfam lam T).L T = L := rfl
      simp only [hydef, ypos, hLP]
      field_simp
    simp only [harg, wSep]
    ring
  -- (E) the separated-set bound
  have hE : ∫ s, wSep lam T s * (∑ i, ∑ j, x i * x j * Real.cos (2 * π * (y i - y j) * s))
      ≤ LMaj * ∑ i, x i ^ 2 :=
    hSB ι y x (wSep lam T) hsep (wSep_measurable hW) (wSep_nonneg lam T) (wSep_le_gMaj hMP hW)
  -- assembly
  rw [hA]
  calc (a * L ^ 2)⁻¹ * ∑ k : Fin d, (∑ i, x i * F i ((k : ℕ) : ℤ)) ^ 2
      ≤ (a * L ^ 2)⁻¹ * (L * (L * (2 / 5 * (LMaj * ∑ i, x i ^ 2)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hc.le)
        refine hB.trans ?_
        rw [hD]
        gcongr
    _ = 2 / (5 * a) * LMaj * ∑ i, x i ^ 2 := by
        field_simp

end Distinct839.ZeroKernel
