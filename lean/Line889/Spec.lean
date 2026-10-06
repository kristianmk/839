/-
Line889/Spec.lean — the interface statements between the layers of the proof (part 1: the
statements that need only Mathlib; the zero side is in `Line889/Spec2.lean`).

Every statement here is a `Prop`-valued definition. Each layer proves one or more of them,
possibly from others; `Line889/Compose.lean` composes them. This file contains definitions only.

The statements have the form of those of `Simple673/Spec.lean` (no labels: all points are simple
zeros on the line; clipping level `clipC = 2`; the bound on separated sets is `normS = 17/10 < 2`),
for the window, the kernel and the certificate data of `Line889/Defs.lean`. The second level
`tLev` of the threshold inequality does not occur here: it enters only in the final count.
-/
import Line889.Defs

open scoped BigOperators ComplexOrder
open Real

noncomputable section

namespace Line889

/-! ## The kernel and its table (`LocalInequality` is in `Defs`) -/

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

/-! ## The telescoping transfer -/

/-- Transfer lemma, in a form that tolerates an error `ε` in the pair energies.
`y` is an increasing `sep`-separated chain of `ℓ` points contained in an interval of length `R`,
and `e i j` is a nonnegative pair energy with `e i j ≥ K(y_j - y_i)² - ε`. Then

`x ℓ - 6α R - (6 x + Ω) - 12 ε ℓ ≤ ∑_{i ≠ j} e i j`.

(`6 x`: the six points at the two ends that are not the middle point of a frame; `12 ε ℓ`:
each of the at most `6ℓ` pairs at index distance at most six has total weight at most `2`.) -/
def TransferStatement : Prop :=
  ∀ (ℓ : ℕ) (y : Fin ℓ → ℝ) (e : Fin ℓ → Fin ℓ → ℝ) (ε R : ℝ),
    (∀ i j, i < j → sep ≤ y j - y i) →
    0 ≤ R → (∀ i j, y j - y i ≤ R) →
    0 ≤ ε →
    (∀ i j, i ≠ j → 0 ≤ e i j) →
    (∀ i j, i ≠ j → K (y j - y i) ^ 2 - ε ≤ e i j) →
    rewX * ℓ - spanB * R - (6 * rewX + omegaB) - 12 * ε * ℓ
      ≤ ∑ i, ∑ j, if i ≠ j then e i j else 0

/-! ## The majorant -/

/-- `f ≤ g` on the support of the window. -/
def MajorantPointwise : Prop := ∀ u : ℝ, |u| ≤ 1 / 2 → fCos u ≤ gMaj u

/-- `L = ∫ g = 1.67931…` is below `1.68`. -/
def LMajBound : Prop := LMaj ≤ 168 / 100

/-- For a `sep`-separated finite set of points, any measurable weight `0 ≤ w ≤ g` gives a
quadratic form bounded by `L`. The double sum equals `|∑ x_i e^{2π i y_i u}|²`. -/
def SeparatedBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (y : ι → ℝ) (x : ι → ℝ) (w : ℝ → ℝ),
    (∀ i j, i ≠ j → sep ≤ |y i - y j|) →
    Measurable w → (∀ u, 0 ≤ w u) → (∀ u, w u ≤ gMaj u) →
    ∫ u, w u * (∑ i, ∑ j, x i * x j * Real.cos (2 * π * (y i - y j) * u)) ≤ LMaj * ∑ i, x i ^ 2

/-! ## The finite Gram theorem at clipping level `2` -/

/-- Lower bound for the clipped trace of a Gram matrix of simple points whose entries are within
`η` of the kernel values and which is bounded by `normS` on separated subsets.

`y` are the positions, `κ` the Gram matrix of the (nearly unit) vectors, `G` the same matrix
with complex entries. The conclusion is

`(1 + x)·n − 6α·R − (6 x + Ω) − C η n ≤ tr φ₂(G)`,   `n` the number of points. -/
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
      (1 + rewX) * Fintype.card ι - spanB * R - (6 * rewX + omegaB) - C * η * Fintype.card ι
        ≤ ∑ k, phiC clipC (hG.1.eigenvalues k)

end Line889
