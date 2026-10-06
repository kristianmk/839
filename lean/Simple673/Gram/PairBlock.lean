/-
Simple673/Gram/PairBlock.lean — the two-by-two blocks of the Gram theorem at clipping level 2.

A removed pair `{i, j}` at distance less than `sep = 17/20` has the block

    [[κ_ii, κ_ij], [κ_ij, κ_jj]],     |κ_ii - 1| ≤ η,  |κ_jj - 1| ≤ η.

`BetaBound` gives `κ_ij² ≥ β - 3η` with `β = betaC = 1/20`. With the tolerance `η` the larger
eigenvalue of the block may exceed `c = 2` (diagonal `1 + η`, off-diagonal close to `1`), so the
block may be clipped. The comparison matrix with off-diagonal square `w = β - 3η` has both
eigenvalues below `2` (they are at most `1 + η + √β`), so by the two-point estimate
`Distinct839.Gram.phiC_pair_ge`, in the form `Distinct839.Gram.pairBlock_ge`, the clipped trace
of the block is at least `κ_ii² + κ_jj² + 2w`, which is at least `2(1 + x₁) - 10η` because
`x₁ ≤ β` (`x₁ = rewX = 8722 · 10⁻⁶`). This is the only place where `β` is used.
-/
import Simple673.Gram.Basic
import Distinct839.Gram.Pinching
import Distinct839.Gram.PairBlock

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Simple673.Gram

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β] [DecidableEq β]
  {y : ι → ℝ} {κ : ι → ι → ℝ} {η : ℝ} {G : Matrix ι ι ℂ}

/-- The site reward is below the lower bound for `K²` near the origin: `x₁ ≤ β`, that is,
`8722 · 10⁻⁶ ≤ 1/20`. -/
lemma rewX_le_betaC : rewX ≤ betaC := by unfold rewX betaC; norm_num

/-- **Pair block.** If the block `k` of the partition `f` consists of two points `i ≠ j` at
distance less than `sep`, the clipped trace of the block of `G` is at least
`2(1 + x₁) - 10η`. -/
theorem pair_block_ge (hβ : BetaBound) (D : GramData y κ η G) (hG : G.PosSemidef)
    (f : ι → β) (k : β) {i j : ι} (hij : i ≠ j) (hclose : |y i - y j| < sep)
    (hfi : f i = k) (hfj : f j = k) (hfib : ∀ l, f l = k → l = i ∨ l = j) :
    ∑ _a : {l // f l = k}, (1 + rewX - 5 * η)
      ≤ ∑ t, phiC clipC ((Distinct839.Gram.blockOf_posSemidef f hG k).1.eigenvalues t) := by
  set a₁ : {l // f l = k} := ⟨i, hfi⟩ with ha₁
  set a₂ : {l // f l = k} := ⟨j, hfj⟩ with ha₂
  have hne : a₁ ≠ a₂ := fun h => hij (congrArg Subtype.val h)
  have huniv : (Finset.univ : Finset {l // f l = k}) = {a₁, a₂} := by
    ext a
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases hfib a.1 a.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hη0 := D.eta_nonneg
  have hη1 := D.eta_le
  -- the entries of the block
  have hAB : ∀ a b : {l // f l = k},
      Distinct839.Gram.blockOf f G k a b = ((κ a b : ℝ) : ℂ) := fun a b => D.entry a b
  have hsymm : ∀ a b : {l // f l = k}, κ a b = κ b a := fun a b => D.symm a b
  -- the off-diagonal entry
  have hβij : betaC - 3 * η ≤ κ i j ^ 2 := by
    have h1 := hβ (y i - y j) hclose.le
    have h2 := D.offdiag_sq_ge i j
    linarith
  have hβnum : betaC = 1 / 20 := rfl
  have hβη : 0 ≤ betaC - 3 * η := by rw [hβnum]; linarith
  -- the diagonal entries
  obtain ⟨hi1, hi2⟩ := D.diag_bounds i
  obtain ⟨hj1, hj2⟩ := D.diag_bounds j
  have hc : clipC = 2 := rfl
  -- the comparison matrix has its eigenvalues below `2`
  have hdet : betaC - 3 * η ≤ (clipC - κ i i) * (clipC - κ j j) := by
    rw [hc, hβnum]
    have h1 : (99 : ℝ) / 100 ≤ 2 - κ i i := by linarith
    have h2 : (99 : ℝ) / 100 ≤ 2 - κ j j := by linarith
    have h3 := mul_le_mul h1 h2 (by norm_num) (by linarith)
    linarith
  have hmain : κ i i ^ 2 + κ j j ^ 2 + 2 * (betaC - 3 * η)
      ≤ ∑ t, phiC clipC ((Distinct839.Gram.blockOf_posSemidef f hG k).1.eigenvalues t) :=
    Distinct839.Gram.pairBlock_ge (Distinct839.Gram.blockOf_posSemidef f hG k).1
      (B := fun a b : {l // f l = k} => κ a b) hAB hsymm hne huniv hβη hβij
      (by rw [hc]; linarith) (by rw [hc]; linarith) hdet
  refine le_trans ?_ hmain
  -- the arithmetic
  rw [huniv, Finset.sum_pair hne]
  have hd1 := D.diag_sq_ge i
  have hd2 := D.diag_sq_ge j
  have hx := rewX_le_betaC
  linarith

end Simple673.Gram
