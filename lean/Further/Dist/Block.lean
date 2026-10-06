/-
Further/Dist/Block.lean — the counting step for "simple or on the line", at the block level.

Setting of `Distinct839/Assembly/Block.lean`: the abstract zero-side data `ZeroBlockData ι d`, a
set `good` of on-line indices of multiplicity at most two, clipping level `c = 67/20`. The
threshold inequality with the two levels `c ≤ t = 27/8` (`Further.seam_block2`) reads

    2t·tr Â − ‖Â‖_F² ≤ 2t·∑_{good} m_z − ∑_j φ_c(λ_j(Wᴴ W)) + t²·(p + #(onLine \ good)).

The counting step (`seam_count_sl`) bounds the cost of every index by a multiple of its
multiplicity: `(2t − e₁)·m` if the index is simple or on the line, `(2t − e₀)·m` otherwise
(`e₁ = 1 + x`, `e₀ = 2t − t²/4`; see `Further/Dist/Constants.lean`):

* good, `m = 1`:                      `2t − 1 − x = 2t − e₁`;
* good, `m = 2`:                      `4t − 4 − y ≤ 2(2t − e₁)`;
* on the line, not good, `m ≥ 3`:      `t² ≤ 3(2t − e₁) ≤ m(2t − e₁)`;
* on the line, not good, `m ≤ 2`:      counted separately (`e` of them, they lie at the edges);
* pair off the line, `m = 1`:          `t² ≤ 2(2t − e₁)`;
* pair off the line, `m ≥ 2`:          `t² = 4(2t − e₀) ≤ 2m(2t − e₀)`.

Hence, with `N_{s∨0} = simpleOrLineSum D` the sum of the multiplicities of the indices that are
simple or on the line,

    ∑_{good} (2t m − m² − rew) + t²(p + #(onLine \ good))
        ≤ (2t − e₀)·N + (e₀ − e₁)·N_{s∨0} + t²·e.

The combination with the certificate is `seam_block_sl`.
-/
import Distinct839.Assembly.Block
import Further.Threshold
import Further.Counting
import Further.Dist.Constants

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Further.Dist

open Zeta23 Zeta23.ZeroSide Zeta23.ZeroSide.RankTraceMult
open Distinct839 (clipC rewX rewY rew phiC)
open Distinct839.Assembly (goodW labOf labOf_one labOf_two rew_zero rew_one clipC_pos)

section Block

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d) {good : Finset ι}

/-- **Counting.**
`∑_{good} (2t m − m² − rew) + t²(p + #(onLine \ good)) ≤ (2t − e₀)·N + (e₀ − e₁)·N_{s∨0} + t²·e`,
where `e` counts the on-line indices outside `good` of multiplicity at most two. -/
theorem seam_count_sl (Pr : D.PairReps) (hgood : good ⊆ D.onLine)
    (hm2 : ∀ z ∈ good, D.m z ≤ 2) :
    ∑ z ∈ good, (2 * tLev * (D.m z : ℝ) - ((D.m z : ℝ) ^ 2 + rew (labOf (D.m z))))
        + tLev ^ 2 * ((Pr.p + #(D.onLine \ good) : ℕ) : ℝ)
      ≤ (2 * tLev - e0C) * (D.Ncount : ℝ) + (e0C - e1C) * (simpleOrLineSum D : ℝ)
        + tLev ^ 2 * (#{z ∈ D.onLine \ good | D.m z ≤ 2} : ℝ) := by
  have h1 := two_tLev_sub_e1C_pos
  have h0 := two_tLev_sub_e0C_pos
  -- the bound for the cost of an index
  set f : ι → ℝ := fun z =>
    if D.m z = 1 ∨ D.σ z = z then (2 * tLev - e1C) * (D.m z : ℝ)
    else (2 * tLev - e0C) * (D.m z : ℝ) with hf
  have hm1 : ∀ z, (1 : ℝ) ≤ D.m z := fun z => by exact_mod_cast D.one_le_m z
  have hf0 : ∀ z, 0 ≤ f z := fun z => by
    have := hm1 z
    simp only [hf]
    split_ifs <;> positivity
  -- the right side as a sum over all indices
  have htot : (2 * tLev - e0C) * (D.Ncount : ℝ) + (e0C - e1C) * (simpleOrLineSum D : ℝ)
      = ∑ z, f z := by
    simp only [hf, ZeroBlockData.Ncount, simpleOrLineSum, Nat.cast_sum, Finset.sum_filter,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    split_ifs <;> ring
  -- off-line pairs
  have hpair : tLev ^ 2 * (Pr.p : ℝ) ≤ ∑ z ∈ Pr.R, (f z + f (D.σ z)) := by
    have : ∀ z ∈ Pr.R, tLev ^ 2 ≤ f z + f (D.σ z) := fun z hz => by
      have hoff : D.σ z ≠ z := Pr.off z hz
      have hoff' : ¬ D.σ (D.σ z) = D.σ z := by rw [D.σ_invol z]; exact fun h => hoff h.symm
      simp only [hf, D.m_σ z, hoff, hoff', or_false]
      by_cases hm : D.m z = 1
      · rw [if_pos hm, hm]
        have := coeff_pair_simple
        push_cast
        linarith
      · rw [if_neg hm]
        have h2 : (2 : ℝ) ≤ D.m z := by
          exact_mod_cast (by have := D.one_le_m z; omega : 2 ≤ D.m z)
        have := coeff_pair_multiple
        nlinarith
    calc tLev ^ 2 * (Pr.p : ℝ) = ∑ _z ∈ Pr.R, tLev ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]; rfl
      _ ≤ ∑ z ∈ Pr.R, (f z + f (D.σ z)) := Finset.sum_le_sum this
  -- good indices
  have hgoodsum : ∑ z ∈ good, (2 * tLev * (D.m z : ℝ)
        - ((D.m z : ℝ) ^ 2 + rew (labOf (D.m z))))
      ≤ ∑ z ∈ good, f z := by
    refine Finset.sum_le_sum fun z hz => ?_
    have hon : D.σ z = z := (D.mem_onLine).mp (hgood hz)
    have hm := D.one_le_m z
    have hm' := hm2 z hz
    have h : D.m z = 1 ∨ D.m z = 2 := by omega
    simp only [hf, hon, or_true, if_true]
    rcases h with h | h
    · rw [h, labOf_one, rew_zero]
      have := coeff_simple
      push_cast
      linarith
    · rw [h, labOf_two, rew_one]
      have := coeff_double
      push_cast
      linarith
  -- on-line indices outside `good`
  have hrest : tLev ^ 2 * (#(D.onLine \ good) : ℝ)
      - tLev ^ 2 * (#{z ∈ D.onLine \ good | D.m z ≤ 2} : ℝ) ≤ ∑ z ∈ D.onLine \ good, f z := by
    have hterm : ∀ z ∈ D.onLine \ good,
        tLev ^ 2 - tLev ^ 2 * (if D.m z ≤ 2 then (1 : ℝ) else 0) ≤ f z := fun z hz => by
      have hon : D.σ z = z := (D.mem_onLine).mp (Finset.mem_sdiff.mp hz).1
      by_cases h : D.m z ≤ 2
      · rw [if_pos h]
        have := hf0 z
        linarith
      · rw [if_neg h]
        have h3 : (3 : ℝ) ≤ D.m z := by exact_mod_cast (by omega : 3 ≤ D.m z)
        have h4 := mul_le_mul_of_nonneg_left h3 h1.le
        have := coeff_triple
        simp only [hf, hon, or_true, if_true]
        linarith
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
      Finset.sum_boole] at hsum
    linarith
  have hsplit : ∑ z, f z = (∑ z ∈ good, f z + ∑ z ∈ D.onLine \ good, f z)
      + ∑ z ∈ Pr.R, (f z + f (D.σ z)) := by
    rw [D.sum_split Pr f, add_comm (∑ z ∈ good, f z), Finset.sum_sdiff hgood]
  rw [htot, hsplit]
  push_cast
  linarith

/-- **Block seam for "simple or on the line".** If the clipped trace of the Gram matrix
`G = Wᴴ W` of the good indices satisfies `∑_{good} (m² + rew) − E ≤ ∑_j φ_c(λ_j(G))`, then
`2t·tr Â − ‖Â‖_F² ≤ (2t − e₀)·N + (e₀ − e₁)·N_{s∨0} + t²·e + E`. -/
theorem seam_block_sl (Pr : D.PairReps) (hgood : good ⊆ D.onLine)
    (hm2 : ∀ z ∈ good, D.m z ≤ 2) {nrm : ℝ} (hnrm : 0 < nrm)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ nrm) {E : ℝ}
    (hE : ∑ z ∈ good, ((D.m z : ℝ) ^ 2 + rew (labOf (D.m z))) - E
      ≤ ∑ j, phiC clipC
          ((Matrix.posSemidef_conjTranspose_mul_self (goodW D good nrm)).1.eigenvalues j)) :
    2 * tLev * rtrace (D.blockP nrm + D.blockQ nrm) - frobSq (D.blockP nrm + D.blockQ nrm)
      ≤ (2 * tLev - e0C) * (D.Ncount : ℝ) + (e0C - e1C) * (simpleOrLineSum D : ℝ)
        + tLev ^ 2 * (#{z ∈ D.onLine \ good | D.m z ≤ 2} : ℝ) + E := by
  have h1 := seam_block2 D Pr hgood hnrm hPois clipC_pos clipC_le_tLev
  have h2 := seam_count_sl D Pr hgood hm2
  have h3 : ∑ z ∈ good, (2 * tLev * (D.m z : ℝ) - ((D.m z : ℝ) ^ 2 + rew (labOf (D.m z))))
      = 2 * tLev * ∑ z ∈ good, (D.m z : ℝ)
        - ∑ z ∈ good, ((D.m z : ℝ) ^ 2 + rew (labOf (D.m z))) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  linarith

end Block

end Further.Dist
