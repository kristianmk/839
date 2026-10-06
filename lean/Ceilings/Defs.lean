/-
Ceilings/Defs.lean — pair-energy certificates, for an arbitrary kernel.

The proofs of the bounds for distinct zeros (`Distinct839`) and for simple zeros on the critical
line (`Simple673`) bound a pair energy from below by a linear function of the numbers of points and
of the length of the configuration. This file defines what such a lower bound is, for a kernel `K`
and a separation `θ` that are parameters, so that the definitions do not depend on a window.

A *configuration* is an increasing chain `y : Fin ℓ → ℝ` with all gaps at least `θ`, contained in
an interval of length `R` (`y j - y i ≤ R` for all `i, j`), with labels `lab : Fin ℓ → Fin 2`
(label `0` is a simple point, label `1` a double point; the multiplicity is
`Distinct839.mulOf (lab i) ∈ {1, 2}`).

* `PairCertFor K θ r x₁ x₂ b`: for some constant `C₃` and all configurations,
  `x₁ n₁ + x₂ n₂ - b R - C₃ ≤ ∑_{i ≠ j, |i - j| ≤ r} m_i m_j K(y_j - y_i)²`,
  where `n₁`, `n₂` count the labels; the left side is written `∑ i, (if lab i = 0 then x₁ else x₂)`.
* `PairCertAllFor K θ x₁ x₂ b`: the same with all pairs `i ≠ j` on the right.
* `PairCert1For K θ r x b`, `PairCert1AllFor K θ x b`: the same for simple points only (no labels):
  `x ℓ - b R - C₃ ≤ ∑ K(y_j - y_i)²`.

The hypothesis `0 ≤ R` is part of the definitions (as in `Distinct839.TransferStatement`): without
it the empty configuration would make every triple with `b > 0` fail, and the definitions would be
empty.

The terms of the pair energy are nonnegative, so a certificate of range `r` is one of every larger
range (`PairCertFor.mono`) and one for all pairs (`PairCertFor.toAll`).
-/
import Distinct839.Defs

open scoped BigOperators

namespace Ceilings

open Distinct839 (mulOf)

/-- **Pair-energy certificate of range `r`** for the kernel `K` and the separation `θ`: for some
constant `C₃` and every `θ`-separated labelled chain in an interval of length `R`,
`x₁ n₁ + x₂ n₂ - b R - C₃` is at most the energy of the pairs at index distance at most `r`. -/
def PairCertFor (K : ℝ → ℝ) (θ : ℝ) (r : ℕ) (x₁ x₂ b : ℝ) : Prop :=
  ∃ C₃ : ℝ, ∀ (ℓ : ℕ) (y : Fin ℓ → ℝ) (lab : Fin ℓ → Fin 2) (R : ℝ),
    (∀ i j, i < j → θ ≤ y j - y i) → 0 ≤ R → (∀ i j, y j - y i ≤ R) →
    ∑ i : Fin ℓ, (if lab i = 0 then x₁ else x₂) - b * R - C₃
      ≤ ∑ i : Fin ℓ, ∑ j : Fin ℓ, if i ≠ j ∧ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ (r : ℤ) then
          mulOf (lab i) * mulOf (lab j) * K (y j - y i) ^ 2 else 0

/-- **Pair-energy certificate, all pairs**: as `PairCertFor`, with the energy of all pairs. -/
def PairCertAllFor (K : ℝ → ℝ) (θ : ℝ) (x₁ x₂ b : ℝ) : Prop :=
  ∃ C₃ : ℝ, ∀ (ℓ : ℕ) (y : Fin ℓ → ℝ) (lab : Fin ℓ → Fin 2) (R : ℝ),
    (∀ i j, i < j → θ ≤ y j - y i) → 0 ≤ R → (∀ i j, y j - y i ≤ R) →
    ∑ i : Fin ℓ, (if lab i = 0 then x₁ else x₂) - b * R - C₃
      ≤ ∑ i : Fin ℓ, ∑ j : Fin ℓ,
          if i ≠ j then mulOf (lab i) * mulOf (lab j) * K (y j - y i) ^ 2 else 0

/-- **Pair-energy certificate of range `r` for simple points**: for some constant `C₃` and every
`θ`-separated chain of `ℓ` points in an interval of length `R`, `x ℓ - b R - C₃` is at most the
energy of the pairs at index distance at most `r`. -/
def PairCert1For (K : ℝ → ℝ) (θ : ℝ) (r : ℕ) (x b : ℝ) : Prop :=
  ∃ C₃ : ℝ, ∀ (ℓ : ℕ) (y : Fin ℓ → ℝ) (R : ℝ),
    (∀ i j, i < j → θ ≤ y j - y i) → 0 ≤ R → (∀ i j, y j - y i ≤ R) →
    x * ℓ - b * R - C₃
      ≤ ∑ i : Fin ℓ, ∑ j : Fin ℓ, if i ≠ j ∧ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ (r : ℤ) then
          K (y j - y i) ^ 2 else 0

/-- **Pair-energy certificate for simple points, all pairs.** -/
def PairCert1AllFor (K : ℝ → ℝ) (θ : ℝ) (x b : ℝ) : Prop :=
  ∃ C₃ : ℝ, ∀ (ℓ : ℕ) (y : Fin ℓ → ℝ) (R : ℝ),
    (∀ i j, i < j → θ ≤ y j - y i) → 0 ≤ R → (∀ i j, y j - y i ≤ R) →
    x * ℓ - b * R - C₃ ≤ ∑ i : Fin ℓ, ∑ j : Fin ℓ, if i ≠ j then K (y j - y i) ^ 2 else 0

/-- Multiplicities are nonnegative. -/
theorem mulOf_nonneg (a : Fin 2) : 0 ≤ mulOf a := by
  unfold Distinct839.mulOf
  positivity

/-- A term of the labelled pair energy is nonnegative. -/
theorem pairTerm_nonneg (K : ℝ → ℝ) (a c : Fin 2) (t : ℝ) : 0 ≤ mulOf a * mulOf c * K t ^ 2 :=
  mul_nonneg (mul_nonneg (mulOf_nonneg a) (mulOf_nonneg c)) (sq_nonneg _)

variable {K : ℝ → ℝ} {θ : ℝ}

/-- A certificate of range `r` is a certificate of every range `r' ≥ r`. -/
theorem PairCertFor.mono {r r' : ℕ} {x₁ x₂ b : ℝ} (hr : r ≤ r')
    (h : PairCertFor K θ r x₁ x₂ b) : PairCertFor K θ r' x₁ x₂ b := by
  obtain ⟨C₃, hC⟩ := h
  refine ⟨C₃, fun ℓ y lab R h1 h2 h3 => (hC ℓ y lab R h1 h2 h3).trans ?_⟩
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have hr' : (r : ℤ) ≤ (r' : ℤ) := by exact_mod_cast hr
  by_cases hc : i ≠ j ∧ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ (r : ℤ)
  · rw [if_pos hc, if_pos ⟨hc.1, hc.2.trans hr'⟩]
  · rw [if_neg hc]
    split_ifs
    · exact pairTerm_nonneg K _ _ _
    · exact le_rfl

/-- A certificate of range `r` is a certificate for all pairs. -/
theorem PairCertFor.toAll {r : ℕ} {x₁ x₂ b : ℝ} (h : PairCertFor K θ r x₁ x₂ b) :
    PairCertAllFor K θ x₁ x₂ b := by
  obtain ⟨C₃, hC⟩ := h
  refine ⟨C₃, fun ℓ y lab R h1 h2 h3 => (hC ℓ y lab R h1 h2 h3).trans ?_⟩
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hc : i ≠ j ∧ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ (r : ℤ)
  · rw [if_pos hc, if_pos hc.1]
  · rw [if_neg hc]
    split_ifs
    · exact pairTerm_nonneg K _ _ _
    · exact le_rfl

/-- For simple points: a certificate of range `r` is a certificate of every range `r' ≥ r`. -/
theorem PairCert1For.mono {r r' : ℕ} {x b : ℝ} (hr : r ≤ r')
    (h : PairCert1For K θ r x b) : PairCert1For K θ r' x b := by
  obtain ⟨C₃, hC⟩ := h
  refine ⟨C₃, fun ℓ y R h1 h2 h3 => (hC ℓ y R h1 h2 h3).trans ?_⟩
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have hr' : (r : ℤ) ≤ (r' : ℤ) := by exact_mod_cast hr
  by_cases hc : i ≠ j ∧ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ (r : ℤ)
  · rw [if_pos hc, if_pos ⟨hc.1, hc.2.trans hr'⟩]
  · rw [if_neg hc]
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl

/-- For simple points: a certificate of range `r` is a certificate for all pairs. -/
theorem PairCert1For.toAll {r : ℕ} {x b : ℝ} (h : PairCert1For K θ r x b) :
    PairCert1AllFor K θ x b := by
  obtain ⟨C₃, hC⟩ := h
  refine ⟨C₃, fun ℓ y R h1 h2 h3 => (hC ℓ y R h1 h2 h3).trans ?_⟩
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hc : i ≠ j ∧ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ (r : ℤ)
  · rw [if_pos hc, if_pos hc.1]
  · rw [if_neg hc]
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl

end Ceilings
