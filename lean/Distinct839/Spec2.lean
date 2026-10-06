/-
Distinct839/Spec2.lean — the interface statements of the zero side.

The profile `vProf` is realised at height `T` by the upstream parameter family
`Pfam lam T = (paramsOf stdProfile lam).atV vProf T`. The on-line zeros give vectors
`(φ̂(γ - τ_k))_{0 ≤ k < d}`; `gramKappa` is the normalised inner product of two of them, and
`ypos` the ordinate in units of the bandwidth. This file contains definitions only.
-/
import Zeta23.XiPrime.Assembly
import Distinct839.Spec

open scoped BigOperators
open Real Filter Topology Zeta23

noncomputable section

namespace Distinct839

/-- The family of parameter sets realising the profile `vProf` at bandwidth `lam`. -/
def Pfam (lam : ℝ) : ℝ → Params := (paramsOf stdProfile lam).atV vProf

/-- Normalised inner product of the evaluation vectors of two real ordinates:
`(a L²)⁻¹ ∑_{0 ≤ k < d} φ̂(γ - τ_k) φ̂(γ' - τ_k)`. -/
def gramKappa (P : Params) (T γ γ' : ℝ) : ℝ :=
  (P.a T * P.L T ^ 2)⁻¹ *
    ∑ k : Fin (P.d T), P.phiHatR T (γ - P.tau T ((k : ℕ) : ℤ)) * P.phiHatR T (γ' - P.tau T ((k : ℕ) : ℤ))

/-- Ordinate in units of the bandwidth: `γ L / (2π)`. -/
def ypos (P : Params) (T γ : ℝ) : ℝ := γ * P.L T / (2 * π)

/-- The Gram data of the realised window, for large `T`:
(1) for ordinates in the bulk `[T + √T, 2T - √T]` the Gram entries are within `η(T) → 0` of the
kernel values `K(y - y')`;
(2) on every finite set of ordinates that is `sep`-separated in bandwidth units, the Gram
matrix is bounded by `c/2`. -/
def GramDataStatement (lam : ℝ) : Prop :=
  (∃ η : ℝ → ℝ, Tendsto η atTop (𝓝 0) ∧ ∀ᶠ T in atTop, ∀ γ γ' : ℝ,
      T + D0 T ≤ γ → γ ≤ 2 * T - D0 T → T + D0 T ≤ γ' → γ' ≤ 2 * T - D0 T →
      |gramKappa (Pfam lam T) T γ γ' - K (ypos (Pfam lam T) T γ - ypos (Pfam lam T) T γ')| ≤ η T) ∧
  (∀ᶠ T in atTop, ∀ (ι : Type) [Fintype ι] (γ : ι → ℝ) (x : ι → ℝ),
      (∀ i j, i ≠ j → sep ≤ |ypos (Pfam lam T) T (γ i) - ypos (Pfam lam T) T (γ j)|) →
      ∑ i, ∑ j, x i * gramKappa (Pfam lam T) T (γ i) (γ j) * x j ≤ clipC / 2 * ∑ i, x i ^ 2)

end Distinct839
