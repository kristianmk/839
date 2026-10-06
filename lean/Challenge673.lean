/-
Challenge673.lean — WHAT IS CLAIMED, from Mathlib alone.

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: this file and the development it belongs to were drafted with Claude (Anthropic),
an AI system, under the direction of the author, who is responsible for their content.

A theorem about the zeros of Mathlib's `riemannZeta`:

    liminf_{T → ∞} N₀ˢ(T) / N(T) ≥ 1669159/2478195 = 0.6735382001…,

written as "for every ε > 0 there is T₀ such that (s − ε)·N(T) ≤ N₀ˢ(T) for all T ≥ T₀". Here
N(T) counts the zeros in the open critical strip with ordinate in (0, T], with multiplicity, and
N₀ˢ(T) counts those that lie on the critical line Re ρ = 1/2 and are simple (multiplicity
exactly 1).

The five definitions are copied character-for-character from `ChallengeDeps.lean` of the library
`zeta23` (anthropics/formal-math), on which the proof builds, so the statement has exactly the
form of the theorem `montgomery_taylor_simple_on_critical_line_mult_cumulative` there, with a
larger constant.
This module imports only Mathlib. The `sorry` is deliberate: this is the statement side.
`Solution673.lean` proves the same statement (with the definitions of `ChallengeDeps.lean`)
from the development in `Simple673/`.
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

/-- N₀ˢ(T₁,T₂): the number of SIMPLE zeros ON THE CRITICAL LINE with T₁ < Im ρ ≤ T₂. -/
def N0simple (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1}).ncard

end
end

/-- More than 67.35% of the zeros of the Riemann zeta function are simple and on the critical
line. -/
theorem simple_critical_zeros_673 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1669159 / 2478195 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  sorry
