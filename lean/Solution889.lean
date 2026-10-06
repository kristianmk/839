/-
Solution889.lean — the statement of `Challenge889.lean`, proved.

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: this file and the development it belongs to were drafted with Claude (Anthropic),
an AI system, under the direction of the author, who is responsible for their content.

The counting function `Ncount` used here is that of `ChallengeDeps.lean` (Mathlib only, root
namespace); it is character-for-character the definition inlined in `Challenge889.lean` and
the one of the library (`Zeta23.Ncount`), so the delegation typechecks by unfolding.

`ChallengeDeps.lean` has no count of the zeros that are simple or on the critical line. The
definition `NsimpleOrLine` is therefore given here, from the `zerosIn` and `zeroMult` of
`ChallengeDeps.lean`. The line is character-for-character the one inlined in `Challenge889.lean`
and in `ChallengeFurther.lean`, and the one of the development (`Further.NsimpleOrLine`);
`NsimpleOrLine_eq_library` records that they agree.
-/
import ChallengeDeps
import Line889.Main

noncomputable section

/-- N_{s∨0}(T₁,T₂): the number of nontrivial zeros with T₁ < Im ρ ≤ T₂ that are SIMPLE OR ON THE
CRITICAL LINE (or both), counted with multiplicity. -/
def NsimpleOrLine (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ ({ρ | zeroMult ρ = 1} ∪ {ρ | ρ.re = 1 / 2}), zeroMult ρ

end

/-- The count of zeros that are simple or on the critical line defined here is the one of the
development. -/
theorem NsimpleOrLine_eq_library (T₁ T₂ : ℝ) :
    NsimpleOrLine T₁ T₂ = Further.NsimpleOrLine T₁ T₂ := rfl

/-- More than 88.93% of the zeros of the Riemann zeta function are simple or on the critical
line (counted with multiplicity). -/
theorem simple_or_critical_8893 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (50652159 / 56956375 - ε) * (Ncount 0 T : ℝ) ≤ NsimpleOrLine 0 T :=
  Line889.simple_or_critical_8893
