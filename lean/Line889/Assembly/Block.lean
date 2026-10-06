/-
Line889/Assembly/Block.lean — the counting step for "simple or on the line", at the block level.

Setting of `Distinct839/Assembly/Block.lean`: the abstract zero-side data `ZeroBlockData ι d`
(an index stands for a zero, `m` is its multiplicity, `σ` the reflection in the critical line,
`onLine` the indices fixed by `σ`, and `p` the number of pairs `{z, σ z}` off the line). The Gram
part is a set `good` of on-line indices of multiplicity one, and the clipping level is
`c = clipC = 2`. The threshold inequality with the two levels `c ≤ t = tLev = 27/8`
(`Further.seam_block2`) reads, since `∑_{good} m = #good`,

    2t·tr Â − ‖Â‖_F² ≤ 2t·#good − ∑_j φ_c(λ_j(Wᴴ W)) + t²·(p + #(onLine \ good)).

So a good index costs `2t` and earns its share of the clipped trace, and every other on-line
index and every pair off the line costs `t²`. The counting step (`seam_count_sl`) bounds each
cost by a multiple of the multiplicity: `(2t − e₁)·m` if the index is simple or on the line,
`(2t − e₀)·m` otherwise (`e₁ = 1 + x`, `e₀ = 2t − t²/4`; see `Line889/Assembly/Constants.lean`):

* good, `m = 1`:                    `2t − e₁ = (2t − e₁)·m`;
* on the line, not good, `m ≥ 2`:    `t² ≤ 2(2t − e₁) ≤ m(2t − e₁)`;
* on the line, not good, `m = 1`:    counted separately (`e` of them; in the application they
                                    are the simple zeros near the ends of the window);
* pair off the line, `m = 1`:        `t² ≤ 2(2t − e₁)`;
* pair off the line, `m ≥ 2`:        `t² = 4(2t − e₀) ≤ 2m(2t − e₀)`.

The second and the fourth line are the same inequality `4t − t² ≥ 2 + 2x` (`coeff_two`). Hence,
with `N` the sum of all multiplicities and `N_{s∨0} = simpleOrLineSum D` the sum of the
multiplicities of the indices that are simple or on the line,

    (2t − e₁)·#good + t²(p + #(onLine \ good)) ≤ (2t − e₀)·N + (e₀ − e₁)·N_{s∨0} + t²·e.

The combination with a lower bound `(1 + x)·#good − E ≤ ∑_j φ_c(λ_j(Wᴴ W))` for the clipped
trace of the Gram part is `seam_block_sl`:

    2t·tr Â − ‖Â‖_F² ≤ (2t − e₀)·N + (e₀ − e₁)·N_{s∨0} + t²·e + E.

Compared with `Further/Dist/Block.lean` (the same count on the Gram part of `Distinct839`): the
good indices all have multiplicity one, so there are no labels and no reward for double zeros,
and the class "on the line, not good" starts at multiplicity two instead of three.
-/
import Distinct839.Assembly.Block
import Further.Threshold
import Further.Counting
import Line889.Assembly.Constants

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Line889.Assembly

open Zeta23 Zeta23.ZeroSide Zeta23.ZeroSide.RankTraceMult
open Distinct839.Assembly (goodW)
open Further (simpleOrLineSum seam_block2)

section Block

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d) {good : Finset ι}

/-- **Counting.** For a set `good` of on-line indices of multiplicity one,
`(2t − e₁)·#good + t²(p + #(onLine \ good)) ≤ (2t − e₀)·N + (e₀ − e₁)·N_{s∨0} + t²·e`,
where `e` counts the on-line indices of multiplicity one outside `good`. -/
theorem seam_count_sl (Pr : D.PairReps) (hgood : good ⊆ D.onLine)
    (hm1 : ∀ z ∈ good, D.m z = 1) :
    (2 * tLev - e1C) * (#good : ℝ) + tLev ^ 2 * ((Pr.p + #(D.onLine \ good) : ℕ) : ℝ)
      ≤ (2 * tLev - e0C) * (D.Ncount : ℝ) + (e0C - e1C) * (simpleOrLineSum D : ℝ)
        + tLev ^ 2 * (#{z ∈ D.onLine \ good | D.m z = 1} : ℝ) := by
  have h1 := two_tLev_sub_e1C_pos
  have h0 := two_tLev_sub_e0C_pos
  -- the bound for the cost of an index
  set f : ι → ℝ := fun z =>
    if D.m z = 1 ∨ D.σ z = z then (2 * tLev - e1C) * (D.m z : ℝ)
    else (2 * tLev - e0C) * (D.m z : ℝ) with hf
  have hm1' : ∀ z, (1 : ℝ) ≤ D.m z := fun z => by exact_mod_cast D.one_le_m z
  have hf0 : ∀ z, 0 ≤ f z := fun z => by
    have := hm1' z
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
        have := coeff_two
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
  have hgoodsum : (2 * tLev - e1C) * (#good : ℝ) = ∑ z ∈ good, f z := by
    have : ∀ z ∈ good, f z = 2 * tLev - e1C := fun z hz => by
      simp only [hf, hm1 z hz, true_or, if_true, Nat.cast_one, mul_one]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- on-line indices outside `good`
  have hrest : tLev ^ 2 * (#(D.onLine \ good) : ℝ)
      - tLev ^ 2 * (#{z ∈ D.onLine \ good | D.m z = 1} : ℝ) ≤ ∑ z ∈ D.onLine \ good, f z := by
    have hterm : ∀ z ∈ D.onLine \ good,
        tLev ^ 2 - tLev ^ 2 * (if D.m z = 1 then (1 : ℝ) else 0) ≤ f z := fun z hz => by
      have hon : D.σ z = z := (D.mem_onLine).mp (Finset.mem_sdiff.mp hz).1
      by_cases h : D.m z = 1
      · rw [if_pos h]
        have := hf0 z
        linarith
      · rw [if_neg h]
        have h2 : (2 : ℝ) ≤ D.m z := by
          exact_mod_cast (by have := D.one_le_m z; omega : 2 ≤ D.m z)
        have h4 := mul_le_mul_of_nonneg_left h2 h1.le
        have := coeff_two
        simp only [hf, hon, or_true, if_true]
        linarith
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
      Finset.sum_boole] at hsum
    linarith
  have hsplit : ∑ z, f z = (∑ z ∈ good, f z + ∑ z ∈ D.onLine \ good, f z)
      + ∑ z ∈ Pr.R, (f z + f (D.σ z)) := by
    rw [D.sum_split Pr f, add_comm (∑ z ∈ good, f z), Finset.sum_sdiff hgood]
  rw [htot, hsplit, hgoodsum]
  push_cast
  linarith

/-- **Block seam for "simple or on the line", at the levels `c = 2 ≤ t = 27/8`.** `good` is a
set of on-line indices of multiplicity one. If the clipped trace of their Gram matrix
`G = Wᴴ W` satisfies `(1 + x)·#good − E ≤ ∑_j φ_c(λ_j(G))`, then
`2t·tr Â − ‖Â‖_F² ≤ (2t − e₀)·N + (e₀ − e₁)·N_{s∨0} + t²·e + E`,
where `e` counts the on-line indices of multiplicity one outside `good`. -/
theorem seam_block_sl (Pr : D.PairReps) (hgood : good ⊆ D.onLine)
    (hm1 : ∀ z ∈ good, D.m z = 1) {nrm : ℝ} (hnrm : 0 < nrm)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ nrm) {E : ℝ}
    (hE : (1 + rewX) * (#good : ℝ) - E
      ≤ ∑ j, phiC clipC
          ((Matrix.posSemidef_conjTranspose_mul_self (goodW D good nrm)).1.eigenvalues j)) :
    2 * tLev * rtrace (D.blockP nrm + D.blockQ nrm) - frobSq (D.blockP nrm + D.blockQ nrm)
      ≤ (2 * tLev - e0C) * (D.Ncount : ℝ) + (e0C - e1C) * (simpleOrLineSum D : ℝ)
        + tLev ^ 2 * (#{z ∈ D.onLine \ good | D.m z = 1} : ℝ) + E := by
  -- the threshold inequality with the two levels `c ≤ t`
  have h1 := seam_block2 D Pr hgood hnrm hPois clipC_pos clipC_le_tLev
  have h2 := seam_count_sl D Pr hgood hm1
  -- the good indices have multiplicity one
  have hsum : ∑ z ∈ good, (D.m z : ℝ) = (#good : ℝ) := by
    rw [Finset.sum_congr rfl fun z hz => by rw [hm1 z hz, Nat.cast_one]]
    simp
  rw [hsum] at h1
  have h3 : (2 * tLev - e1C) * (#good : ℝ)
      = 2 * tLev * (#good : ℝ) - (1 + rewX) * (#good : ℝ) := by
    unfold e1C; ring
  linarith

end Block

end Line889.Assembly
