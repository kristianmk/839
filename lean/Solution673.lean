/-
Solution673.lean — the statement of `Challenge673.lean`, proved.

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: this file and the development it belongs to were drafted with Claude (Anthropic),
an AI system, under the direction of the author, who is responsible for their content.

The counting functions `Ncount`, `N0simple` used here are those of `ChallengeDeps.lean` (Mathlib
only, root namespace); they are character-for-character the definitions inlined in
`Challenge673.lean` and the ones of the library (`Zeta23.Ncount`, `Zeta23.N0simple`), so the
delegation typechecks by unfolding.
-/
import ChallengeDeps
import Simple673.Main

/-- More than 67.35% of the zeros of the Riemann zeta function are simple and on the critical
line. -/
theorem simple_critical_zeros_673 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1669159 / 2478195 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  Simple673.simple_critical_zeros_673
