/-
Simple673/ZeroKernel/Bulk.lean — Gram entries of two ordinates in the bulk, at one height.

At height `T`, with `L` the bandwidth, `h = 2π/L` the grid step, `d = ⌊LT/2π⌋` and `a` the
normalisation of the realised window `φ`, the Gram entry of two real ordinates is
`κ(γ, γ') = (a L²)⁻¹ ∑_{0 ≤ k < d} φ̂(γ - τ_k) φ̂(γ' - τ_k)`, `τ_k = T + k h`. Let `c = cW` be
the constant of the window class of `φ` and `Z = ∑_{k ∈ ℤ} 1/k²`. For `γ, γ'` in the bulk
`[T + √T, 2T - √T]`:

* the truncated Poisson sum differs from the full one, `L Φ(γ - γ')`, by at most
  `2 Z (c/(R h))²` with `R = √T/2` (`Distinct839/ZeroKernel/Leak.lean`, which holds for every
  window of the class; the ramp width is `1`); after division by `a L²` this is at most
  `8 Z c² / T`, because `a ≥ 1/4`;
* `Φ(γ - γ')/(a L)` is within `24/L` of `K((γ - γ') L / 2π)` (`Kernel.lean`).

Together (`abs_gramKappa_sub_K_le`):
`|κ(γ, γ') - K(y - y')| ≤ 24/L + 8 Z c²/T` once `L ≥ 40` and `T ≥ 16`.

The three elementary lemmas `sub_le_floor_mul`, `abs_inv_mul_sub_le`, `leak_div_le` of
`Distinct839/ZeroKernel/Bulk.lean` do not depend on the window and are used from there, as are
`zetaTwoZ` and `abs_poisson_sub_sum_le` of `Distinct839/ZeroKernel/Leak.lean`.
-/
import Distinct839.ZeroKernel.Bulk
import Distinct839.ZeroKernel.Leak
import Simple673.ZeroKernel.Kernel

open scoped BigOperators
open Real Filter Topology MeasureTheory Zeta23

noncomputable section

namespace Simple673.ZeroKernel

/-- **Gram entries in the bulk, at one height.** For the realised window at height `T` with
`L ≥ 40` and `T ≥ 16`, and two ordinates in `[T + √T, 2T - √T]`,
`|κ(γ, γ') - K(y - y')| ≤ 24/L + 8 Z c²/T`, where `y = γ L/2π`, `c = cW` is the constant of the
window class and `Z = ∑_{k ∈ ℤ} 1/k²`. -/
theorem abs_gramKappa_sub_K_le {lam cW T : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hK : ∀ t : ℝ, K t = ∫ u in (-(1:ℝ)/2)..(1/2), fCos u * Real.cos (2 * π * t * u))
    (hW : AdmWindow (phiW lam T) ((Pst lam).L T) 1 cW)
    (hL40 : 40 ≤ (Pst lam).L T) (hT : 16 ≤ T) {γ γ' : ℝ}
    (hγ : T + D0 T ≤ γ) (hγ2 : γ ≤ 2 * T - D0 T)
    (hγ' : T + D0 T ≤ γ') (hγ'2 : γ' ≤ 2 * T - D0 T) :
    |gramKappa (Pfam lam T) T γ γ' - K (ypos (Pfam lam T) T γ - ypos (Pfam lam T) T γ')|
      ≤ 24 / (Pst lam).L T + 8 * Distinct839.ZeroKernel.zetaTwoZ * cW ^ 2 / T := by
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
  have hd : T - 2 * π / L ≤ ((Pst lam).d T : ℝ) * (2 * π / L) :=
    Distinct839.ZeroKernel.sub_le_floor_mul hL
  have hup : ∀ x : ℝ, x ≤ 2 * T - Real.sqrt T →
      x ≤ T + ((Pst lam).d T : ℝ) * (2 * π / L) - Real.sqrt T / 2 := by
    intro x hx
    linarith
  have hlo : ∀ x : ℝ, T + Real.sqrt T ≤ x → T + Real.sqrt T / 2 ≤ x := by
    intro x hx
    linarith
  -- the leak
  have hleak := Distinct839.ZeroKernel.abs_poisson_sub_sum_le hW T ((Pst lam).d T) hR
    (hlo γ hγ) (hup γ hγ2) (hlo γ' hγ') (hup γ' hγ'2)
  -- the kernel
  have hker := abs_VPhiR_div_sub_K_le hK hW hL40 (γ - γ')
  have ha := av_ge_quarter hK hW hL40
  rw [gramKappa_Pfam h0 h1, ypos_sub]
  refine le_trans (Distinct839.ZeroKernel.abs_inv_mul_sub_le hL (by linarith) hleak hker) ?_
  rw [add_comm (24 / L)]
  exact add_le_add_left
    (Distinct839.ZeroKernel.leak_div_le Distinct839.ZeroKernel.zetaTwoZ_nonneg hL hT0 ha) _

end Simple673.ZeroKernel
