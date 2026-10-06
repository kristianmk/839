/-
SolutionFurther.lean — the statements of `ChallengeFurther.lean`, proved.

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: this file and the development it belongs to were drafted with Claude (Anthropic),
an AI system, under the direction of the author, who is responsible for their content.

The counting function `Ncount` used here is that of `ChallengeDeps.lean` (Mathlib only, root
namespace); it is character-for-character the definition inlined in `ChallengeFurther.lean` and
the one of the library (`Zeta23.Ncount`), so the delegation typechecks by unfolding.

`ChallengeDeps.lean` has no count of the zeros on the critical line with multiplicity, of the
simple zeros of the whole strip, or of the zeros that are simple or on the line. The three
definitions `N0mult`, `Nsimple`, `NsimpleOrLine` are therefore given here, from the `zerosIn` and
`zeroMult` of `ChallengeDeps.lean`. The lines are character-for-character the ones inlined in
`ChallengeFurther.lean` and the ones of the development (`Further.N0mult`, which is the library's
`Zeta23.N0`; `Zeta23.Nsimple`; `Further.NsimpleOrLine`); the three `…_eq_library` theorems record
that they agree.
-/
import ChallengeDeps
import Further.Main

noncomputable section

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

/-- The count of zeros on the critical line defined here is the one of the development (and of
the library, `Zeta23.N0`). -/
theorem N0mult_eq_library (T₁ T₂ : ℝ) : N0mult T₁ T₂ = Further.N0mult T₁ T₂ := rfl

/-- The count of simple zeros defined here is the one of the library. -/
theorem Nsimple_eq_library (T₁ T₂ : ℝ) : Nsimple T₁ T₂ = Zeta23.Nsimple T₁ T₂ := rfl

/-- The count of zeros that are simple or on the critical line defined here is the one of the
development. -/
theorem NsimpleOrLine_eq_library (T₁ T₂ : ℝ) :
    NsimpleOrLine T₁ T₂ = Further.NsimpleOrLine T₁ T₂ := rfl

/-- The average of the proportion of simple zeros and the proportion of zeros on the critical
line (counted with multiplicity) is more than 83.67%. -/
theorem average_simple_and_critical_8367 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2073677 / 2478195 - ε) * (Ncount 0 T : ℝ) ≤ ((Nsimple 0 T : ℝ) + (N0mult 0 T : ℝ)) / 2 :=
  Further.average_simple_and_critical_8367

/-- More than 88.91% of the zeros of the Riemann zeta function are simple or on the critical
line (counted with multiplicity). -/
theorem simple_or_critical_8891 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3376433 / 3797325 - ε) * (Ncount 0 T : ℝ) ≤ NsimpleOrLine 0 T :=
  Further.simple_or_critical_8891
