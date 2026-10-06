/-
ChallengeFurther.lean — WHAT IS CLAIMED, from Mathlib alone.

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: this file and the development it belongs to were drafted with Claude (Anthropic),
an AI system, under the direction of the author, who is responsible for their content.

Two theorems about the zeros of Mathlib's `riemannZeta`:

    liminf_{T → ∞} (N_s(T) + N₀(T)) / (2 N(T)) ≥ 2073677/2478195 = 0.8367691000…,
    liminf_{T → ∞} N_{s∨0}(T) / N(T)           ≥ 3376433/3797325 = 0.8891609224…,

each written as "for every ε > 0 there is T₀ such that (q − ε)·N(T) ≤ … for all T ≥ T₀". Here
N(T) counts the zeros in the open critical strip with ordinate in (0, T], with multiplicity;
N_s(T) counts the simple ones (multiplicity exactly 1, anywhere in the strip); N₀(T) counts those
on the critical line Re ρ = 1/2, with multiplicity; and N_{s∨0}(T) counts, with multiplicity,
those that are simple or on the critical line (or both).

The first statement says that the average of the proportion of simple zeros and the proportion of
zeros on the critical line is more than 83.67%; the constant is (1 + s)/2 for the constant
s = 1669159/2478195 of `Challenge673.lean`. The second says that more than 88.91% of the zeros
are simple or on the critical line.

The first four definitions are copied character-for-character from `ChallengeDeps.lean` of the
library `zeta23` (anthropics/formal-math), on which the proofs build, and `Nsimple` from
`Challenge839.lean` (it is `Zeta23.Nsimple` of the same library). `N0mult` is character for
character the library's `Zeta23.N0` (`Zeta23/Statement.lean`); `NsimpleOrLine` is new. This module
imports only Mathlib. The `sorry`s are deliberate: this is the statement side.
`SolutionFurther.lean` proves the same statements (with the definitions of `ChallengeDeps.lean`,
and the same three further definitions) from the development in `Further/`, which builds on
`Simple673/` and `Distinct839/`.
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

/-- N₀(T₁,T₂): the number of zeros ON THE CRITICAL LINE with T₁ < Im ρ ≤ T₂, counted with
multiplicity. -/
def N0mult (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}, zeroMult ρ

/-- N_s(T₁,T₂): the number of SIMPLE nontrivial zeros (multiplicity exactly 1, anywhere in the
critical strip) with T₁ < Im ρ ≤ T₂. -/
def Nsimple (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | zeroMult ρ = 1}).ncard

/-- N_{s∨0}(T₁,T₂): the number of nontrivial zeros with T₁ < Im ρ ≤ T₂ that are SIMPLE OR ON THE
CRITICAL LINE (or both), counted with multiplicity. -/
def NsimpleOrLine (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ ({ρ | zeroMult ρ = 1} ∪ {ρ | ρ.re = 1 / 2}), zeroMult ρ

end
end

/-- The average of the proportion of simple zeros and the proportion of zeros on the critical
line (counted with multiplicity) is more than 83.67%. -/
theorem average_simple_and_critical_8367 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2073677 / 2478195 - ε) * (Ncount 0 T : ℝ) ≤ ((Nsimple 0 T : ℝ) + (N0mult 0 T : ℝ)) / 2 := by
  sorry

/-- More than 88.91% of the zeros of the Riemann zeta function are simple or on the critical
line (counted with multiplicity). -/
theorem simple_or_critical_8891 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3376433 / 3797325 - ε) * (Ncount 0 T : ℝ) ≤ NsimpleOrLine 0 T := by
  sorry
