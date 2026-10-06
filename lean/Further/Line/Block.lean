/-
Further/Line/Block.lean — the counting step for the average, at the block level.

Setting of `Simple673/Assembly/Block.lean`: the abstract zero-side data `ZeroBlockData ι d`, a set
`good` of on-line indices of multiplicity one, clipping level `c = 2`. The threshold inequality
(`Distinct839.Assembly.seam_block`) reads

    4·tr Â − ‖Â‖_F² ≤ 4·#good − ∑_j φ₂(λ_j(Wᴴ W)) + 4·(p + #(onLine \ good)).

`Simple673` bounds the last term by `2·(N − s₁)`, which is exact only if every zero outside the
Gram part is a double zero on the line or a pair of simple zeros off the line. Here the zeros
outside the Gram part are counted by kind. Each of them costs `c² = 4`, and

* a zero on the line of multiplicity `m ≥ 2` carries `m` in `N` and `m` in `N₀`:   `2m ≥ 4`;
* a pair off the line of multiplicity one carries `2` in `N` and `2` in `N_s`:      `4 ≥ 4`;
* a pair off the line of multiplicity `m ≥ 2` carries `2m` in `N`:                 `2m ≥ 4`;
* a good zero carries `1` in each of `N`, `N_s`, `N₀`, and costs `4 − 1 = 3` (before the reward).

Hence (`count_avg`), with `e` the number of simple on-line indices outside `good`,

    3·#good + 4·(p + #(onLine \ good)) ≤ N + N_s + N₀ + 4·e,

where `N_s = simpleCard D` counts all indices of multiplicity one and `N₀ = D.Non` is the sum of
the multiplicities of the on-line indices. With the certificate `(1 + x₁)·#good − E ≤ ∑ φ₂(λ_j)`
this gives `seam_block_avg`:

    4·tr Â − ‖Â‖_F² ≤ N + N_s + N₀ − x₁·s₁ + (4 + x₁)·e + E.
-/
import Simple673.Assembly.Block
import Further.Counting

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Further.Line

open Zeta23 Zeta23.ZeroSide Zeta23.ZeroSide.RankTraceMult
open Simple673 (rewX clipC phiC)
open Simple673.Assembly (clipC_pos two_clipC clipC_sq s₁_eq_card_good_add)
open Distinct839.Assembly (goodW seam_block)

section Block

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d) {good : Finset ι}

/-- **Counting.** `3·#good + 4·(p + #(onLine \ good)) ≤ N + N_s + N₀ + 4·e`, where `N_s` counts
the indices of multiplicity one, `N₀` is the sum of the multiplicities of the on-line indices and
`e` counts the simple on-line indices outside `good`. -/
theorem count_avg (Pr : D.PairReps) (hgood : good ⊆ D.onLine) (hm1 : ∀ z ∈ good, D.m z = 1) :
    3 * #good + 4 * (Pr.p + #(D.onLine \ good))
      ≤ D.Ncount + simpleCard D + D.Non + 4 * #{z ∈ D.onLine \ good | D.m z = 1} := by
  -- the contribution of an index to `N + N_s`
  set g : ι → ℕ := fun z => D.m z + (if D.m z = 1 then 1 else 0) with hg
  have htot : D.Ncount + simpleCard D = ∑ z, g z := by
    simp only [hg, Finset.sum_add_distrib, ZeroBlockData.Ncount, simpleCard, Finset.card_filter]
  have hsplit := D.sum_split Pr g
  -- off-line pairs: `m = 1` gives `2 + 2`, `m ≥ 2` gives `2m`
  have hpair : 4 * Pr.p ≤ ∑ z ∈ Pr.R, (g z + g (D.σ z)) := by
    have h : ∀ z ∈ Pr.R, 4 ≤ g z + g (D.σ z) := fun z _ => by
      have h1 := D.one_le_m z
      simp only [hg, D.m_σ z]
      split_ifs <;> omega
    calc 4 * Pr.p = ∑ _z ∈ Pr.R, 4 := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]; rfl
      _ ≤ ∑ z ∈ Pr.R, (g z + g (D.σ z)) := Finset.sum_le_sum h
  -- on-line indices: together with `N₀` each contributes `2m + [m = 1]`
  have hon : ∑ z ∈ D.onLine, g z + D.Non
      = ∑ z ∈ D.onLine \ good, (g z + D.m z) + ∑ z ∈ good, (g z + D.m z) := by
    rw [Finset.sum_sdiff hgood]
    exact (Finset.sum_add_distrib (s := D.onLine) (f := g) (g := fun z => D.m z)).symm
  have hgoodsum : ∑ z ∈ good, (g z + D.m z) = 3 * #good := by
    have h : ∀ z ∈ good, g z + D.m z = 3 := fun z hz => by simp [hg, hm1 z hz]
    rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, mul_comm]
  have hrest : 4 * #(D.onLine \ good)
      ≤ ∑ z ∈ D.onLine \ good, (g z + D.m z) + 4 * #{z ∈ D.onLine \ good | D.m z = 1} := by
    have h : ∀ z ∈ D.onLine \ good,
        4 ≤ (g z + D.m z) + 4 * (if D.m z = 1 then 1 else 0) := fun z _ => by
      have h1 := D.one_le_m z
      simp only [hg]
      split_ifs <;> omega
    have hs := Finset.sum_le_sum h
    rw [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.card_filter] at hs
    omega
  omega

/-- **Block seam for the average, `c = 2`.** `good` is a set of simple on-line indices. If the
clipped trace of their Gram matrix `G = Wᴴ W` satisfies `(1 + x₁)·#good − E ≤ ∑_j φ₂(λ_j(G))`,
then `4·tr Â − ‖Â‖_F² ≤ N + N_s + N₀ − x₁·s₁ + (4 + x₁)·e + E`, with `e` the number of simple
on-line indices outside `good`. -/
theorem seam_block_avg (Pr : D.PairReps) (hgood : good ⊆ D.onLine)
    (hm1 : ∀ z ∈ good, D.m z = 1) {nrm : ℝ} (hnrm : 0 < nrm)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ nrm) {E : ℝ}
    (hE : (1 + rewX) * (#good : ℝ) - E
      ≤ ∑ j, phiC clipC
          ((Matrix.posSemidef_conjTranspose_mul_self (goodW D good nrm)).1.eigenvalues j)) :
    4 * rtrace (D.blockP nrm + D.blockQ nrm) - frobSq (D.blockP nrm + D.blockQ nrm)
      ≤ (D.Ncount : ℝ) + (simpleCard D : ℝ) + (D.Non : ℝ) - rewX * (D.s₁ : ℝ)
        + (4 + rewX) * (#{z ∈ D.onLine \ good | D.m z = 1} : ℝ) + E := by
  have h1 := seam_block D Pr hgood hnrm hPois clipC_pos
  have hsum : ∑ z ∈ good, (D.m z : ℝ) = (#good : ℝ) := by
    rw [Finset.sum_congr rfl fun z hz => by rw [hm1 z hz, Nat.cast_one]]
    simp
  have h2 : (3 : ℝ) * (#good : ℝ) + 4 * ((Pr.p + #(D.onLine \ good) : ℕ) : ℝ)
      ≤ (D.Ncount : ℝ) + (simpleCard D : ℝ) + (D.Non : ℝ)
        + 4 * (#{z ∈ D.onLine \ good | D.m z = 1} : ℝ) := by
    exact_mod_cast count_avg D Pr hgood hm1
  have hs : (D.s₁ : ℝ) = #good + (#{z ∈ D.onLine \ good | D.m z = 1} : ℝ) := by
    exact_mod_cast s₁_eq_card_good_add D hgood hm1
  rw [hsum, two_clipC, clipC_sq] at h1
  rw [hs]
  linarith

end Block

end Further.Line
