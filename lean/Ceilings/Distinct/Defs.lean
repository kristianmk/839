/-
Ceilings/Distinct/Defs.lean — pair-energy certificates and the energy constant for the window of
`Distinct839` (the 83.90% theorem for distinct zeros).

* `PairCert r x₁ x₂ b`, `PairCertAll x₁ x₂ b`: the definitions of `Ceilings/Defs.lean` for the
  kernel `Distinct839.K` and the separation `Distinct839.sep = 17/20`, written out. The lower bound
  for the pair energy that the proof of the 83.90% theorem uses is of this kind, with the triple
  `(rewX, rewY, spanB)` and range six (`paper_certificate` in `Ceilings/Distinct/Paper.lean`).
* `energyC = A + B`: the energy constant `C(f)` of the window. It is the constant of the method:
  `energyC = Distinct839.kappa 1` (`energyC_eq_kappa_one`), the zeta second-moment constant of the
  window at bandwidth `λ = 1`; the proof of the theorem uses the upper bound
  `energyC < Distinct839.energyC0` (`energyC_lt`), the ceilings need the lower bound
  `1.332704958281 ≤ energyC` (`CloQ_le`, from `π > 3.14159265358979323846`).

A triple `(x₁, x₂, b)` gives, by the certificate principle of the paper, the constant
`(3 - energyC + x₂ - x₁ - b)/(2 - 2x₁ + x₂)`.
-/
import Ceilings.Defs
import Distinct839.Constant.Kappa

open scoped BigOperators
open Real

noncomputable section

namespace Ceilings

/-- **Pair-energy certificate of range `r`** for the window of `Distinct839`: for some constant
`C₃` and every labelled chain `y` with gaps at least `17/20` in an interval of length `R`,
`x₁ n₁ + x₂ n₂ - b R - C₃ ≤ ∑_{i ≠ j, |i - j| ≤ r} m_i m_j K(y_j - y_i)²`
(label `0`: simple point, multiplicity `1`; label `1`: double point, multiplicity `2`). -/
def PairCert (r : ℕ) (x₁ x₂ b : ℝ) : Prop :=
  ∃ C₃ : ℝ, ∀ (ℓ : ℕ) (y : Fin ℓ → ℝ) (lab : Fin ℓ → Fin 2) (R : ℝ),
    (∀ i j, i < j → Distinct839.sep ≤ y j - y i) → 0 ≤ R → (∀ i j, y j - y i ≤ R) →
    ∑ i : Fin ℓ, (if lab i = 0 then x₁ else x₂) - b * R - C₃
      ≤ ∑ i : Fin ℓ, ∑ j : Fin ℓ, if i ≠ j ∧ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ (r : ℤ) then
          Distinct839.mulOf (lab i) * Distinct839.mulOf (lab j) * Distinct839.K (y j - y i) ^ 2
        else 0

/-- **Pair-energy certificate, all pairs**, for the window of `Distinct839`. -/
def PairCertAll (x₁ x₂ b : ℝ) : Prop :=
  ∃ C₃ : ℝ, ∀ (ℓ : ℕ) (y : Fin ℓ → ℝ) (lab : Fin ℓ → Fin 2) (R : ℝ),
    (∀ i j, i < j → Distinct839.sep ≤ y j - y i) → 0 ≤ R → (∀ i j, y j - y i ≤ R) →
    ∑ i : Fin ℓ, (if lab i = 0 then x₁ else x₂) - b * R - C₃
      ≤ ∑ i : Fin ℓ, ∑ j : Fin ℓ,
          if i ≠ j then
            Distinct839.mulOf (lab i) * Distinct839.mulOf (lab j) * Distinct839.K (y j - y i) ^ 2
          else 0

/-- `PairCert` is the general definition for the kernel and the separation of `Distinct839`. -/
theorem pairCert_iff_for {r : ℕ} {x₁ x₂ b : ℝ} :
    PairCert r x₁ x₂ b ↔ PairCertFor Distinct839.K Distinct839.sep r x₁ x₂ b := Iff.rfl

theorem pairCertAll_iff_for {x₁ x₂ b : ℝ} :
    PairCertAll x₁ x₂ b ↔ PairCertAllFor Distinct839.K Distinct839.sep x₁ x₂ b := Iff.rfl

/-- A certificate of range `r` is a certificate of every range `r' ≥ r`: the terms of the pair
energy are nonnegative. -/
theorem PairCert.mono {r r' : ℕ} {x₁ x₂ b : ℝ} (hr : r ≤ r') (h : PairCert r x₁ x₂ b) :
    PairCert r' x₁ x₂ b :=
  PairCertFor.mono hr h

/-- A certificate of range `r` is a certificate for all pairs. -/
theorem PairCert.toAll {r : ℕ} {x₁ x₂ b : ℝ} (h : PairCert r x₁ x₂ b) : PairCertAll x₁ x₂ b :=
  PairCertFor.toAll h

/-! ## The energy constant -/

/-- The energy constant `C(f) = A + B` of the window of `Distinct839`:
`A = ∫ f² = 1 + ½ ∑ a_j²`, `B = ∬ |s - t| f(s) f(t) ds dt`. -/
def energyC : ℝ := Distinct839.Aconst + Distinct839.Bconst

/-- **`energyC` is the constant of the method**: the zeta second-moment constant `κ(λ)` of the
window (`Distinct839.kappa`, the inverse of the window functional of the upstream library) at
`λ = 1`. -/
theorem energyC_eq_kappa_one : energyC = Distinct839.kappa 1 := by
  rw [Distinct839.kappa_eq one_pos]
  unfold energyC
  ring

/-- The upper bound for `energyC` that the proof of the 83.90% theorem uses. -/
theorem energyC_lt : energyC < Distinct839.energyC0 := Distinct839.Aconst_add_Bconst_lt

/-- Rational lower bound for `energyC` (the value is `1.33270495828171…`). -/
def CloQ : ℚ := 1332704958281 / 1000000000000

/-- **Lower bound for the energy constant**, from `π > 3.14159265358979323846`. -/
theorem CloQ_le : ((CloQ : ℚ) : ℝ) ≤ energyC := by
  unfold energyC
  rw [Distinct839.Constant.Aconst_eq, Distinct839.Constant.Bconst_eq]
  have hπ := Real.pi_gt_d20
  have hπ2 : (3.14159265358979323846 : ℝ) ^ 2 ≤ π ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hπ.le 2
  have h : 250664498438947 / 1200000000000000 / π ^ 2
      ≤ 250664498438947 / 1200000000000000 / (3.14159265358979323846 : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hπ2
  have h2 : ((CloQ : ℚ) : ℝ) ≤ 408214524539 / 400000000000
      + (1 / 3 - 250664498438947 / 1200000000000000 / (3.14159265358979323846 : ℝ) ^ 2) := by
    unfold CloQ
    norm_num
  linarith

end Ceilings
