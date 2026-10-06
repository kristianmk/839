/-
Solution839.lean — the statements of `Challenge839.lean`, proved.

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: this file and the development it belongs to were drafted with Claude (Anthropic),
an AI system, under the direction of the author, who is responsible for their content.

The counting functions `Ncount`, `Ndist` used here are those of `ChallengeDeps.lean` (Mathlib
only, root namespace); they are character-for-character the definitions inlined in
`Challenge839.lean` and the ones of the library (`Zeta23.Ncount`, `Zeta23.Ndist`), so the
delegation typechecks by unfolding.

`ChallengeDeps.lean` counts simple zeros on the critical line only (`N0simple`), so `Nsimple`,
which counts the simple zeros of the whole strip, is defined here, from the `zerosIn` and
`zeroMult` of `ChallengeDeps.lean`. The line is character-for-character the one inlined in
`Challenge839.lean` and the one of the library (`Zeta23.Nsimple`); `Nsimple_eq_library` records
that they agree.
-/
import ChallengeDeps
import Distinct839.Simple

/-- More than 83.9% of the zeros of the Riemann zeta function are distinct. -/
theorem distinct_zeros_839 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1645064 / 1960733 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T :=
  Distinct839.distinct_zeros_839

noncomputable section

/-- N_s(T₁,T₂): the number of SIMPLE nontrivial zeros (multiplicity exactly 1, anywhere in the
critical strip) with T₁ < Im ρ ≤ T₂. -/
def Nsimple (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | zeroMult ρ = 1}).ncard

end

/-- The count of simple zeros defined here is the one of the library. -/
theorem Nsimple_eq_library (T₁ T₂ : ℝ) : Nsimple T₁ T₂ = Zeta23.Nsimple T₁ T₂ := rfl

/-- More than 67.8% of the zeros of the Riemann zeta function are simple. -/
theorem simple_zeros_678 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1329395 / 1960733 - ε) * (Ncount 0 T : ℝ) ≤ Nsimple 0 T :=
  Distinct839.simple_zeros_678
