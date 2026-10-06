/-
Simple673/Assembly/Block.lean — the block-level seam at clipping level `2`.

Setting: the abstract zero-side data `ZeroBlockData ι d` of `Zeta23/ZeroSide.lean` (distinct
points `z : ι` with multiplicities `m z ≥ 1`, vectors `v z`, the reflection `σ`), a normalisation
`nrm = a L² > 0`, and a set `good` of on-line indices of multiplicity one. The decomposition

    Â = P_good + Q',   P_good = W Wᴴ,   Q' = (on-line part outside `good`) + blockQ,

the bound `posIndex Q' ≤ p + #(onLine \ good)` and the threshold inequality in terms of the Gram
matrix `Wᴴ W` are those of `Distinct839/Assembly/Block.lean` (`goodW`, `posIndex_restQ_le`,
`seam_block`), which are generic in the clipping level and in the good set. With `c = 2` and
`m = 1` on `good`, `seam_block` reads

    4·tr Â − ‖Â‖_F² ≤ 4·#good − ∑_j φ₂(λ_j(Wᴴ W)) + 4·(p + #(onLine \ good)).

This file adds the counting step (`seam_count`). The on-line indices outside `good` are the `s₂`
multiple ones and `e` simple ones, and `s₁ = #good + e`. A multiple on-line zero and an off-line
pair each cost `c² = 4` and each carry multiplicity at least `2`, so
`4·(p + s₂) ≤ 2·(N − s₁)`; a simple zero outside `good` costs `4` and carries only `1`. Hence

    (3 − x₁)·#good + 4·(p + #(onLine \ good)) ≤ 2·N + (1 − x₁)·s₁ + 4·e.

The combination is `seam_block_count`. For `x₁ = 0`, `e = 0` it is the upstream
`ZeroBlockData.mult_two` (`4·tr Â − ‖Â‖² − 2N ≤ s₁`), which keeps all on-line zeros in the
positive part and therefore cannot carry an interaction term.
-/
import Distinct839.Assembly.Block
import Simple673.Assembly.Constants

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Simple673.Assembly

open Zeta23 Zeta23.ZeroSide Zeta23.ZeroSide.RankTraceMult
open Distinct839.Assembly (goodW seam_block)

section Block

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d) {good : Finset ι}

/-! ### The on-line indices outside the good set -/

/-- The on-line indices outside `good` that are not simple are exactly the multiple on-line
indices, because every good index is simple. -/
lemma card_rest_multiple (hm1 : ∀ z ∈ good, D.m z = 1) :
    #{z ∈ D.onLine \ good | ¬ D.m z = 1} = D.s₂ := by
  unfold ZeroBlockData.s₂ ZeroBlockData.S₂
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_sdiff, ZeroBlockData.mem_onLine, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨⟨h1, -⟩, h3⟩
    exact ⟨h1, by have := D.one_le_m z; omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun hz => by have := hm1 z hz; omega⟩, by omega⟩

/-- `#(onLine \ good) = e + s₂`, `e` the number of simple on-line indices outside `good`. -/
lemma card_rest_eq (hm1 : ∀ z ∈ good, D.m z = 1) :
    #(D.onLine \ good) = #{z ∈ D.onLine \ good | D.m z = 1} + D.s₂ := by
  rw [← card_rest_multiple D hm1]
  exact (Finset.card_filter_add_card_filter_not (s := D.onLine \ good) (fun z => D.m z = 1)).symm

/-- `s₁ = #good + e`: a simple on-line index is good or is one of the `e` excluded ones. -/
lemma s₁_eq_card_good_add (hgood : good ⊆ D.onLine) (hm1 : ∀ z ∈ good, D.m z = 1) :
    D.s₁ = #good + #{z ∈ D.onLine \ good | D.m z = 1} := by
  unfold ZeroBlockData.s₁ ZeroBlockData.S₁
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff, ZeroBlockData.mem_onLine,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hz : z ∈ good
      · exact Or.inl hz
      · exact Or.inr ⟨⟨h1, hz⟩, h2⟩
    · rintro (hz | ⟨⟨h1, -⟩, h2⟩)
      · exact ⟨(D.mem_onLine).mp (hgood hz), hm1 z hz⟩
      · exact ⟨h1, h2⟩
  · rw [Finset.disjoint_left]
    intro z hz hz'
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz').1).2 hz

/-! ### The counting step -/

/-- **Counting.** `(3 − x₁)·#good + 4·(p + #(onLine \ good)) ≤ 2·N + (1 − x₁)·s₁ + 4·e`, where
`e` counts the simple on-line indices outside `good`. -/
theorem seam_count (Pr : D.PairReps) (hgood : good ⊆ D.onLine) (hm1 : ∀ z ∈ good, D.m z = 1) :
    (3 - rewX) * (#good : ℝ) + 4 * ((Pr.p + #(D.onLine \ good) : ℕ) : ℝ)
      ≤ 2 * (D.Ncount : ℝ) + (1 - rewX) * (D.s₁ : ℝ)
        + 4 * (#{z ∈ D.onLine \ good | D.m z = 1} : ℝ) := by
  have hN : (D.s₁ : ℝ) + 2 * D.s₂ + 2 * Pr.p ≤ D.Ncount := by
    exact_mod_cast D.s₁_add_two_s₂_add_two_p_le_Ncount Pr
  have hs : (D.s₁ : ℝ) = #good + (#{z ∈ D.onLine \ good | D.m z = 1} : ℝ) := by
    exact_mod_cast s₁_eq_card_good_add D hgood hm1
  have hr : ((Pr.p + #(D.onLine \ good) : ℕ) : ℝ)
      = Pr.p + ((#{z ∈ D.onLine \ good | D.m z = 1} : ℝ) + D.s₂) := by
    rw [card_rest_eq D hm1]; push_cast; ring
  have hx := rewX_nonneg
  have hx1 := one_sub_rewX_pos
  have he : (0 : ℝ) ≤ (#{z ∈ D.onLine \ good | D.m z = 1} : ℝ) := Nat.cast_nonneg _
  have h3 : 0 ≤ (3 - rewX) * (#{z ∈ D.onLine \ good | D.m z = 1} : ℝ) :=
    mul_nonneg (by linarith) he
  rw [hr, hs]
  linarith

/-- **Block seam with counting, `c = 2`.** `good` is a set of simple on-line indices. If the
clipped trace of their Gram matrix `G = Wᴴ W` satisfies `(1 + x₁)·#good − E ≤ ∑_j φ₂(λ_j(G))`,
then `4·tr Â − ‖Â‖_F² ≤ 2·N + (1 − x₁)·s₁ + 4·e + E`, with `e` the number of simple on-line
indices outside `good`. -/
theorem seam_block_count (Pr : D.PairReps) (hgood : good ⊆ D.onLine)
    (hm1 : ∀ z ∈ good, D.m z = 1) {nrm : ℝ} (hnrm : 0 < nrm)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ nrm) {E : ℝ}
    (hE : (1 + rewX) * (#good : ℝ) - E
      ≤ ∑ j, phiC clipC
          ((Matrix.posSemidef_conjTranspose_mul_self (goodW D good nrm)).1.eigenvalues j)) :
    4 * rtrace (D.blockP nrm + D.blockQ nrm) - frobSq (D.blockP nrm + D.blockQ nrm)
      ≤ 2 * (D.Ncount : ℝ) + (1 - rewX) * (D.s₁ : ℝ)
        + 4 * (#{z ∈ D.onLine \ good | D.m z = 1} : ℝ) + E := by
  have h1 := seam_block D Pr hgood hnrm hPois clipC_pos
  have hsum : ∑ z ∈ good, (D.m z : ℝ) = (#good : ℝ) := by
    rw [Finset.sum_congr rfl fun z hz => by rw [hm1 z hz, Nat.cast_one]]
    simp
  have h2 := seam_count D Pr hgood hm1
  rw [hsum, two_clipC, clipC_sq] at h1
  linarith

end Block

end Simple673.Assembly
