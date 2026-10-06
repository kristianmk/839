/-
Distinct839/Spec.lean — the interface statements between the layers of the proof.

Every statement here is a `Prop`-valued definition. Each layer proves one of them, possibly from
others; the assembly file composes them. This file contains definitions only.
-/
import Distinct839.Defs

open scoped BigOperators ComplexOrder
open Real

noncomputable section

namespace Distinct839

/-! ## Layer E: kernel table and local inequality (`LocalInequality` is in `Defs`) -/

/-- A table `tab` of integers is a sound lower enclosure of `K²` on the grid cells:
`tab k / V ≤ K(t)²` for `t ∈ [k/H, (k+1)/H]`. -/
def TableSound (tab : ℕ → ℕ) : Prop :=
  ∀ (k : ℕ) (t : ℝ), (k : ℝ) / gridH ≤ t → t ≤ ((k : ℝ) + 1) / gridH →
    (tab k : ℝ) / scaleV ≤ K t ^ 2

/-- `K(t)² ≥ β` for `|t| ≤ 17/20`. -/
def BetaBound : Prop := ∀ t : ℝ, |t| ≤ sep → betaC ≤ K t ^ 2

/-! ## Layer D: the labelled telescoping transfer -/

/-- Transfer lemma, in a form that tolerates an error `ε` in the pair energies.
`y` is an increasing `sep`-separated chain of `ℓ` points with labels `lab`, contained in an
interval of length `R`, and `e i j` is a nonnegative pair energy with `e i j ≥ K(y_j - y_i)² - ε`. -/
def TransferStatement : Prop :=
  ∀ (ℓ : ℕ) (y : Fin ℓ → ℝ) (lab : Fin ℓ → Fin 2) (e : Fin ℓ → Fin ℓ → ℝ) (ε R : ℝ),
    (∀ i j, i < j → sep ≤ y j - y i) →
    0 ≤ R → (∀ i j, y j - y i ≤ R) →
    0 ≤ ε →
    (∀ i j, i ≠ j → 0 ≤ e i j) →
    (∀ i j, i ≠ j → K (y j - y i) ^ 2 - ε ≤ e i j) →
    ∑ i, rew (lab i) - spanB * R - (6 * rewY + omegaB) - 48 * ε * ℓ
      ≤ ∑ i, ∑ j, if i ≠ j then mulOf (lab i) * mulOf (lab j) * e i j else 0

/-! ## Layer C: the majorant -/

/-- `f ≤ g` on the support of the window. -/
def MajorantPointwise : Prop := ∀ u : ℝ, |u| ≤ 1 / 2 → fCos u ≤ gMaj u

/-- `L = ∫ g` is below `c/2`, with room. -/
def LMajBound : Prop := LMaj ≤ 16711 / 10000

/-- For a `sep`-separated finite set of points, any measurable weight `0 ≤ w ≤ g` gives a
quadratic form bounded by `L`. The double sum equals `|∑ x_i e^{2π i y_i u}|²`. -/
def SeparatedBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (y : ι → ℝ) (x : ι → ℝ) (w : ℝ → ℝ),
    (∀ i j, i ≠ j → sep ≤ |y i - y j|) →
    Measurable w → (∀ u, 0 ≤ w u) → (∀ u, w u ≤ gMaj u) →
    ∫ u, w u * (∑ i, ∑ j, x i * x j * Real.cos (2 * π * (y i - y j) * u)) ≤ LMaj * ∑ i, x i ^ 2

/-! ## Layer B: the finite Gram theorem -/

/-- Lower bound for the clipped trace of a labelled Gram matrix whose entries are within `η` of
the kernel values and which is bounded by `c/2` on separated subsets.

`y` are the positions, `lab` the labels (multiplicity `mulOf (lab i) ∈ {1, 2}`), `κ` the Gram
matrix of the (nearly unit) vectors, `G = D^{1/2} κ D^{1/2}` the weighted Gram matrix. -/
def GramEnergyStatement : Prop :=
  ∃ C η₀ : ℝ, 0 ≤ C ∧ 0 < η₀ ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (y : ι → ℝ) (lab : ι → Fin 2) (κ : ι → ι → ℝ)
      (η R : ℝ) (G : Matrix ι ι ℂ) (hG : G.PosSemidef),
      Function.Injective y →
      0 ≤ η → η ≤ η₀ →
      (∀ i j, κ i j = κ j i) →
      (∀ i j, |κ i j - K (y i - y j)| ≤ η) →
      (∀ S : Finset ι, (∀ i ∈ S, ∀ j ∈ S, i ≠ j → sep ≤ |y i - y j|) →
        ∀ x : ι → ℝ, ∑ i ∈ S, ∑ j ∈ S, x i * κ i j * x j ≤ clipC / 2 * ∑ i ∈ S, x i ^ 2) →
      0 ≤ R → (∀ i j, y i - y j ≤ R) →
      (∀ i j, G i j = ((Real.sqrt (mulOf (lab i) * mulOf (lab j)) * κ i j : ℝ) : ℂ)) →
      ∑ i, (mulOf (lab i) ^ 2 + rew (lab i)) - spanB * R - (6 * rewY + omegaB)
          - C * η * Fintype.card ι
        ≤ ∑ k, phiC clipC (hG.1.eigenvalues k)

end Distinct839
