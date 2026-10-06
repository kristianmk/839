/-
Distinct839/ZeroKernel/Bulk.lean — Gram entries of two ordinates in the bulk, at one height.

At height `T`, with `L` the bandwidth, `h = 2π/L` the grid step, `d = ⌊LT/2π⌋` and `a` the
normalisation of the realised window `φ`, the Gram entry of two real ordinates is
`κ(γ, γ') = (a L²)⁻¹ ∑_{0 ≤ k < d} φ̂(γ - τ_k) φ̂(γ' - τ_k)`. For `γ, γ'` in the bulk
`[T + √T, 2T - √T]`:

* the truncated Poisson sum differs from the full one, `L Φ(γ - γ')`, by at most
  `2 Z (c/(R h))²` with `R = √T/2` (`Leak.lean`); after division by `a L²` this is at most
  `8 Z c² / T`;
* `Φ(γ - γ')/(a L)` is within `24/L` of `K((γ - γ') L / 2π)` (`Kernel.lean`).

Together (`abs_gramKappa_sub_K_le`):
`|κ(γ, γ') - K(y - y')| ≤ 24/L + 8 Z c²/T` once `L ≥ 40` and `T ≥ 16`.
-/
import Distinct839.ZeroKernel.Kernel
import Distinct839.ZeroKernel.Leak

open scoped BigOperators
open Real Filter Topology MeasureTheory Zeta23

noncomputable section

namespace Distinct839.ZeroKernel

/-- The grid `T + k h`, `0 ≤ k < d`, `d = ⌊LT/2π⌋`, `h = 2π/L`, reaches `T - h`:
`T - h ≤ d h`. -/
lemma sub_le_floor_mul {L T : ℝ} (hL : 0 < L) :
    T - 2 * π / L ≤ (⌊L * T / (2 * π)⌋₊ : ℝ) * (2 * π / L) := by
  have h := Nat.lt_floor_add_one (L * T / (2 * π))
  have hh : 0 < 2 * π / L := by positivity
  have e : L * T / (2 * π) * (2 * π / L) = T := by
    field_simp
  have h2 : T < ((⌊L * T / (2 * π)⌋₊ : ℝ) + 1) * (2 * π / L) := by
    calc T = L * T / (2 * π) * (2 * π / L) := e.symm
      _ < ((⌊L * T / (2 * π)⌋₊ : ℝ) + 1) * (2 * π / L) := mul_lt_mul_of_pos_right h hh
  have e2 : ((⌊L * T / (2 * π)⌋₊ : ℝ) + 1) * (2 * π / L)
      = (⌊L * T / (2 * π)⌋₊ : ℝ) * (2 * π / L) + 2 * π / L := by ring
  linarith

/-- Splitting the error: `(a L²)⁻¹ S - k = (S - L Φ)/(a L²) + (Φ/(a L) - k)`. -/
lemma abs_inv_mul_sub_le {S Φ a L k E δ : ℝ} (hL : 0 < L) (ha : 0 < a)
    (h1 : |L * Φ - S| ≤ E) (h2 : |Φ / (a * L) - k| ≤ δ) :
    |(a * L ^ 2)⁻¹ * S - k| ≤ E / (a * L ^ 2) + δ := by
  have hc : 0 < a * L ^ 2 := by positivity
  have e : (a * L ^ 2)⁻¹ * S - k = -((L * Φ - S) / (a * L ^ 2)) + (Φ / (a * L) - k) := by
    field_simp
    ring
  rw [e]
  calc |-((L * Φ - S) / (a * L ^ 2)) + (Φ / (a * L) - k)|
      ≤ |-((L * Φ - S) / (a * L ^ 2))| + |Φ / (a * L) - k| := abs_add_le _ _
    _ = |L * Φ - S| / (a * L ^ 2) + |Φ / (a * L) - k| := by
        rw [abs_neg, abs_div, abs_of_pos hc]
    _ ≤ E / (a * L ^ 2) + δ := add_le_add (div_le_div_of_nonneg_right h1 hc.le) h2

/-- The leak bound after normalisation: `2 Z (c/(R h))² / (a L²) ≤ 8 Z c² / T` for
`R = √T/2`, `h = 2π/L` and `a ≥ 1/4`. -/
lemma leak_div_le {Z c a L T : ℝ} (hZ : 0 ≤ Z) (hL : 0 < L) (hT : 0 < T) (ha : 1 / 4 ≤ a) :
    2 * Z * (c / 1 / (Real.sqrt T / 2 * (2 * π / L))) ^ 2 / (a * L ^ 2)
      ≤ 8 * Z * c ^ 2 / T := by
  have hs : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT.le
  have hs0 : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have ha0 : 0 < a := by linarith
  have hpi : 3 < π := Real.pi_gt_three
  have e1 : c / 1 / (Real.sqrt T / 2 * (2 * π / L)) = c * L / (π * Real.sqrt T) := by
    field_simp
  have e2 : 2 * Z * (c / 1 / (Real.sqrt T / 2 * (2 * π / L))) ^ 2 / (a * L ^ 2)
      = 8 * Z * c ^ 2 / T * (1 / (4 * a * π ^ 2)) := by
    rw [e1, div_pow, mul_pow, mul_pow, hs]
    field_simp
    ring
  rw [e2]
  have hq : 1 / (4 * a * π ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  exact mul_le_of_le_one_right (by positivity) hq

/-- **Gram entries in the bulk, at one height.** For the realised window at height `T` with
`L ≥ 40` and `T ≥ 16`, and two ordinates in `[T + √T, 2T - √T]`,
`|κ(γ, γ') - K(y - y')| ≤ 24/L + 8 Z c²/T`, where `y = γ L/2π` and `Z = ∑_{k ∈ ℤ} 1/k²`. -/
theorem abs_gramKappa_sub_K_le {lam cW T : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hK : ∀ t : ℝ, K t = ∫ u in (-(1:ℝ)/2)..(1/2), fCos u * Real.cos (2 * π * t * u))
    (hW : AdmWindow (phiW lam T) ((Pst lam).L T) 1 cW)
    (hL40 : 40 ≤ (Pst lam).L T) (hT : 16 ≤ T) {γ γ' : ℝ}
    (hγ : T + D0 T ≤ γ) (hγ2 : γ ≤ 2 * T - D0 T)
    (hγ' : T + D0 T ≤ γ') (hγ'2 : γ' ≤ 2 * T - D0 T) :
    |gramKappa (Pfam lam T) T γ γ' - K (ypos (Pfam lam T) T γ - ypos (Pfam lam T) T γ')|
      ≤ 24 / (Pst lam).L T + 8 * zetaTwoZ * cW ^ 2 / T := by
  set L := (Pst lam).L T with hLdef
  have hL : 0 < L := by linarith
  have hT0 : 0 < T := by linarith
  -- the window radius `R = √T/2` dominates the grid step
  have hsT : 4 ≤ Real.sqrt T := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hT
  have hh : 2 * π / L ≤ 1 := by
    rw [div_le_one hL]
    linarith [Real.pi_lt_four]
  have hR : 2 * π / L ≤ Real.sqrt T / 2 := by linarith
  have hD0 : D0 T = Real.sqrt T := rfl
  rw [hD0] at hγ hγ2 hγ' hγ'2
  have hd : T - 2 * π / L ≤ ((Pst lam).d T : ℝ) * (2 * π / L) := sub_le_floor_mul hL
  have hup : ∀ x : ℝ, x ≤ 2 * T - Real.sqrt T →
      x ≤ T + ((Pst lam).d T : ℝ) * (2 * π / L) - Real.sqrt T / 2 := by
    intro x hx
    linarith
  have hlo : ∀ x : ℝ, T + Real.sqrt T ≤ x → T + Real.sqrt T / 2 ≤ x := by
    intro x hx
    linarith
  -- the leak
  have hleak := abs_poisson_sub_sum_le hW T ((Pst lam).d T) hR (hlo γ hγ) (hup γ hγ2)
    (hlo γ' hγ') (hup γ' hγ'2)
  -- the kernel
  have hker := abs_VPhiR_div_sub_K_le hK hW hL40 (γ - γ')
  have ha := av_ge_quarter hK hW hL40
  rw [gramKappa_Pfam h0 h1, ypos_sub]
  refine le_trans (abs_inv_mul_sub_le hL (by linarith) hleak hker) ?_
  rw [add_comm (24 / L)]
  exact add_le_add_left (leak_div_le zetaTwoZ_nonneg hL hT0 ha) _

end Distinct839.ZeroKernel
