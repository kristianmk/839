/-
Simple673/Spec.lean — the interface statements between the layers of the proof (part 1: the
statements that need only Mathlib; the zero side is in `Simple673/Spec2.lean`).

Every statement here is a `Prop`-valued definition. Each layer proves one or more of them,
possibly from others; `Simple673/Compose.lean` composes them. This file contains definitions
only.

Differences from `Distinct839/Spec.lean`: there are no labels (all points are simple zeros),
the clipping level is `clipC = 2`, the bound on separated sets is `normS = 19/10 < 2` instead
of `c/2`, and the frames have eight points instead of seven, so that the pairs at index distance
at most seven enter (`7 x₁`, `7 α` and `14 ε` below, where `Distinct839` has `6`, `6` and `12`).
-/
import Simple673.Defs

open scoped BigOperators ComplexOrder
open Real

noncomputable section

namespace Simple673

/-! ## Layer E1: the kernel and its table (`LocalInequality` is in `Defs`) -/

/-- The kernel is the cosine transform of the window. -/
def KIntegral : Prop :=
  ∀ t : ℝ, K t = ∫ u in (-(1 : ℝ) / 2)..(1 / 2), fCos u * Real.cos (2 * π * t * u)

/-- A table `tab` of integers is a sound lower enclosure of `K²` on the grid cells:
`tab k / V ≤ K(t)²` for `t ∈ [k/H, (k+1)/H]`. -/
def TableSound (tab : ℕ → ℕ) : Prop :=
  ∀ (k : ℕ) (t : ℝ), (k : ℝ) / gridH ≤ t → t ≤ ((k : ℝ) + 1) / gridH →
    (tab k : ℝ) / scaleV ≤ K t ^ 2

/-- `K(t)² ≥ β` for `|t| ≤ 17/20`. -/
def BetaBound : Prop := ∀ t : ℝ, |t| ≤ sep → betaC ≤ K t ^ 2

/-! ## Layer D: the telescoping transfer -/

/-- Transfer lemma, in a form that tolerates an error `ε` in the pair energies.
`y` is an increasing `sep`-separated chain of `ℓ` points contained in an interval of length `R`,
and `e i j` is a nonnegative pair energy with `e i j ≥ K(y_j - y_i)² - ε`. Then

`x₁ ℓ - 7α R - (7 x₁ + Ω) - 14 ε ℓ ≤ ∑_{i ≠ j} e i j`.

(`7 x₁`: the seven points at the two ends that are not the rewarded point of a frame; `14 ε ℓ`:
each of the at most `7ℓ` pairs at index distance at most seven has total weight at most `2`.) -/
def TransferStatement : Prop :=
  ∀ (ℓ : ℕ) (y : Fin ℓ → ℝ) (e : Fin ℓ → Fin ℓ → ℝ) (ε R : ℝ),
    (∀ i j, i < j → sep ≤ y j - y i) →
    0 ≤ R → (∀ i j, y j - y i ≤ R) →
    0 ≤ ε →
    (∀ i j, i ≠ j → 0 ≤ e i j) →
    (∀ i j, i ≠ j → K (y j - y i) ^ 2 - ε ≤ e i j) →
    rewX * ℓ - spanB * R - (7 * rewX + omegaB) - 14 * ε * ℓ
      ≤ ∑ i, ∑ j, if i ≠ j then e i j else 0

/-! ## Layer C: the majorant -/

/-- `f ≤ g` on the support of the window. -/
def MajorantPointwise : Prop := ∀ u : ℝ, |u| ≤ 1 / 2 → fCos u ≤ gMaj u

/-- `L = ∫ g = 1.78942…` is below `1.79`. -/
def LMajBound : Prop := LMaj ≤ 179 / 100

/-- For a `sep`-separated finite set of points, any measurable weight `0 ≤ w ≤ g` gives a
quadratic form bounded by `L`. The double sum equals `|∑ x_i e^{2π i y_i u}|²`. -/
def SeparatedBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (y : ι → ℝ) (x : ι → ℝ) (w : ℝ → ℝ),
    (∀ i j, i ≠ j → sep ≤ |y i - y j|) →
    Measurable w → (∀ u, 0 ≤ w u) → (∀ u, w u ≤ gMaj u) →
    ∫ u, w u * (∑ i, ∑ j, x i * x j * Real.cos (2 * π * (y i - y j) * u)) ≤ LMaj * ∑ i, x i ^ 2

/-! ## Layer B: the finite Gram theorem at clipping level `2` -/

/-- Lower bound for the clipped trace of a Gram matrix of simple points whose entries are within
`η` of the kernel values and which is bounded by `normS` on separated subsets.

`y` are the positions, `κ` the Gram matrix of the (nearly unit) vectors, `G` the same matrix
with complex entries. The conclusion is

`(1 + x₁)·n − 7α·R − (7 x₁ + Ω) − C η n ≤ tr φ₂(G)`,   `n` the number of points. -/
def GramEnergyStatement : Prop :=
  ∃ C η₀ : ℝ, 0 ≤ C ∧ 0 < η₀ ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (y : ι → ℝ) (κ : ι → ι → ℝ)
      (η R : ℝ) (G : Matrix ι ι ℂ) (hG : G.PosSemidef),
      Function.Injective y →
      0 ≤ η → η ≤ η₀ →
      (∀ i j, κ i j = κ j i) →
      (∀ i j, |κ i j - K (y i - y j)| ≤ η) →
      (∀ S : Finset ι, (∀ i ∈ S, ∀ j ∈ S, i ≠ j → sep ≤ |y i - y j|) →
        ∀ x : ι → ℝ, ∑ i ∈ S, ∑ j ∈ S, x i * κ i j * x j ≤ normS * ∑ i ∈ S, x i ^ 2) →
      0 ≤ R → (∀ i j, y i - y j ≤ R) →
      (∀ i j, G i j = ((κ i j : ℝ) : ℂ)) →
      (1 + rewX) * Fintype.card ι - spanB * R - (7 * rewX + omegaB) - C * η * Fintype.card ι
        ≤ ∑ k, phiC clipC (hG.1.eigenvalues k)

end Simple673
