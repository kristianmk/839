/-
Further/Defs.lean — the counting functions of the two further theorems.

Two consequences of the developments `Distinct839` (83.90% distinct zeros) and `Simple673`
(67.35% simple zeros on the critical line) are proved in `Further/`:

    liminf_{T → ∞} (N_s(T) + N₀(T)) / (2 N(T)) ≥ 2073677/2478195 = 0.8367691000…,
    liminf_{T → ∞} N_{s∨0}(T) / N(T)           ≥ 3376433/3797325 = 0.8891609224….

Here `N(T)` counts the zeros of the Riemann zeta function in the open critical strip with ordinate
in `(0, T]`, with multiplicity; `N_s` counts the simple ones (`Zeta23.Nsimple`, the definition of
`Challenge839.lean`); `N₀` counts those on the critical line, with multiplicity (`N0mult`); and
`N_{s∨0}` counts, with multiplicity, those that are simple or on the critical line
(`NsimpleOrLine`).

The definitions of the library that the statements use (`IsNontrivialZero`, `zeroMult`,
`zerosIn`, `Ncount`, `Nsimple`; file `Zeta23/Statement.lean`) are exported into this namespace;
they are character for character the Mathlib-only definitions of `ChallengeDeps.lean` and
`Challenge839.lean`. This file contains definitions only (and one `rfl`).
-/
import Zeta23.Statement

open scoped BigOperators
open Set

noncomputable section

namespace Further

export Zeta23 (IsNontrivialZero zeroMult zerosIn Ncount Nsimple)

/-- `N₀(T₁,T₂)`: the zeros on the critical line with `T₁ < Im ρ ≤ T₂`, counted with
multiplicity. -/
def N0mult (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}, zeroMult ρ

/-- `N_{s∨0}(T₁,T₂)`: the zeros with `T₁ < Im ρ ≤ T₂` that are simple or on the critical line (or
both), counted with multiplicity. -/
def NsimpleOrLine (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ ({ρ | zeroMult ρ = 1} ∪ {ρ | ρ.re = 1 / 2}), zeroMult ρ

/-- `N0mult` is the count `N₀` of the library. -/
theorem N0mult_eq_library (T₁ T₂ : ℝ) : N0mult T₁ T₂ = Zeta23.N0 T₁ T₂ := rfl

end Further
