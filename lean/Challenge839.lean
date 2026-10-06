/-
Challenge839.lean — WHAT IS CLAIMED, from Mathlib alone.

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: this file and the development it belongs to were drafted with Claude (Anthropic),
an AI system, under the direction of the author, who is responsible for their content.

Two theorems about the zeros of Mathlib's `riemannZeta`:

    liminf_{T → ∞} N_d(T) / N(T) ≥ 1645064/1960733 = 0.8390045967…,
    liminf_{T → ∞} N_s(T) / N(T) ≥ 1329395/1960733 = 0.6780091935…,

each written as "for every ε > 0 there is T₀ such that (q − ε)·N(T) ≤ N_d(T) for all T ≥ T₀"
(resp. N_s(T)). Here N(T) counts the zeros in the open critical strip with ordinate in (0, T], with
multiplicity, N_d(T) counts the distinct ones and N_s(T) the simple ones (multiplicity exactly 1).
The second constant is 2q − 1 for the first constant q, and the second theorem follows from the
first, because a zero that is not simple has multiplicity at least 2.

The first five definitions are copied character-for-character from `ChallengeDeps.lean` of the
library `zeta23` (anthropics/formal-math), on which the proof builds, so the first statement has
exactly the form of the theorems `five_sixths_distinct_cumulative` and
`montgomery_taylor_distinct_mult_cumulative` there, with a larger constant. `ChallengeDeps.lean`
counts simple zeros on the critical line only (`N0simple`); the sixth definition, `Nsimple`, which
counts the simple zeros of the whole strip, is copied character-for-character from
`Zeta23/Statement.lean` of the same library. This module imports only Mathlib. The `sorry`s are
deliberate: this is the statement side. `Solution839.lean` proves the same statements (with the
definitions of `ChallengeDeps.lean`, and the same `Nsimple`) from the development in
`Distinct839/`.
-/
import Mathlib

section
open scoped BigOperators ComplexConjugate
open Complex Set

noncomputable section

/-- ρ is a nontrivial zero of the Riemann zeta function: ζ(ρ) = 0 with 0 < Re ρ < 1. -/
def IsNontrivialZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- The multiplicity of ρ: the order of vanishing of ζ at ρ. -/
def zeroMult (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat

/-- The nontrivial zeros with ordinate in the window (T₁, T₂]. -/
def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsNontrivialZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- N(T₁,T₂): the number of nontrivial zeros with T₁ < Im ρ ≤ T₂, counted with multiplicity. -/
def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ

/-- N_d(T₁,T₂): the number of distinct nontrivial zeros with T₁ < Im ρ ≤ T₂. -/
def Ndist (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂).ncard

/-- N_s(T₁,T₂): the number of SIMPLE nontrivial zeros (multiplicity exactly 1, anywhere in the
critical strip) with T₁ < Im ρ ≤ T₂. -/
def Nsimple (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | zeroMult ρ = 1}).ncard

end
end

/-- More than 83.9% of the zeros of the Riemann zeta function are distinct. -/
theorem distinct_zeros_839 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1645064 / 1960733 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T := by
  sorry

/-- More than 67.8% of the zeros of the Riemann zeta function are simple. -/
theorem simple_zeros_678 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1329395 / 1960733 - ε) * (Ncount 0 T : ℝ) ≤ Nsimple 0 T := by
  sorry
