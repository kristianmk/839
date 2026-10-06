/-
Challenge889.lean — WHAT IS CLAIMED, from Mathlib alone.

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: this file and the development it belongs to were drafted with Claude (Anthropic),
an AI system, under the direction of the author, who is responsible for their content.

One theorem about the zeros of Mathlib's `riemannZeta`:

    liminf_{T → ∞} N_{s∨0}(T) / N(T) ≥ 50652159/56956375 = 0.8893150064…,

written as "for every ε > 0 there is T₀ such that (q − ε)·N(T) ≤ N_{s∨0}(T) for all T ≥ T₀". Here
N(T) counts the zeros in the open critical strip with ordinate in (0, T], with multiplicity, and
N_{s∨0}(T) counts, with multiplicity, those that are simple or on the critical line Re ρ = 1/2
(or both). So more than 88.93% of the zeros are simple or on the critical line.

`ChallengeFurther.lean` states the same count with the smaller constant
3376433/3797325 = 0.8891609224… (`simple_or_critical_8891`), which follows from the certificate
of the first window. The present theorem uses a third window and a certificate made for this
count.

The five definitions are copied character-for-character from `ChallengeFurther.lean`: the first
four are those of `ChallengeDeps.lean` of the library `zeta23` (anthropics/formal-math), on which
the proofs build, and `NsimpleOrLine` is the count defined there. This module imports only
Mathlib. The `sorry` is deliberate: this is the statement side. `Solution889.lean` proves the same
statement (with the definitions of `ChallengeDeps.lean`, and the same definition of
`NsimpleOrLine`) from the development in `Line889/`, which builds on `Further/`, `Simple673/` and
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

/-- N_{s∨0}(T₁,T₂): the number of nontrivial zeros with T₁ < Im ρ ≤ T₂ that are SIMPLE OR ON THE
CRITICAL LINE (or both), counted with multiplicity. -/
def NsimpleOrLine (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ ({ρ | zeroMult ρ = 1} ∪ {ρ | ρ.re = 1 / 2}), zeroMult ρ

end
end

/-- More than 88.93% of the zeros of the Riemann zeta function are simple or on the critical
line (counted with multiplicity). -/
theorem simple_or_critical_8893 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (50652159 / 56956375 - ε) * (Ncount 0 T : ℝ) ≤ NsimpleOrLine 0 T := by
  sorry
