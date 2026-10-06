/-
Distinct839/Gram/PairBlock.lean — the two-by-two blocks of the Gram theorem.

A removed pair `{i, j}` at distance less than `sep = 17/20` has the block

    [[a κ_ii, √(ab) κ_ij], [√(ab) κ_ij, b κ_jj]],     a = m_i, b = m_j ∈ {1, 2}.

`BetaBound` gives `κ_ij² ≥ β - 3η`. The comparison matrix with off-diagonal square
`w = ab(β - 3η)` has both eigenvalues below `c = 67/20`, so by the two-point estimate
`phiC_pair_ge` the clipped trace of the block is at least `a²κ_ii² + b²κ_jj² + 2w`, which is at
least `a² + b² + rew_i + rew_j - 40η` because `rew_i + rew_j ≤ 2abβ`.
-/
import Distinct839.Gram.Basic
import Distinct839.Gram.Pinching

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Distinct839.Gram

/-- **Two-by-two block estimate, abstract form.** A Hermitian matrix on a two-element index
type `{a₁, a₂}` with real entries `B`. If `w ≤ B a₁ a₂ ²` and the comparison matrix with
off-diagonal square `w` has its eigenvalues below `c`, then the clipped trace is at least
`B a₁ a₁ ² + B a₂ a₂ ² + 2w`. -/
theorem pairBlock_ge {τ : Type*} [Fintype τ] [DecidableEq τ] {A : Matrix τ τ ℂ}
    (hA : A.IsHermitian) {B : τ → τ → ℝ} (hAB : ∀ a b, A a b = (B a b : ℂ))
    (hsymm : ∀ a b, B a b = B b a) {a₁ a₂ : τ} (hne : a₁ ≠ a₂)
    (huniv : (Finset.univ : Finset τ) = {a₁, a₂}) {c w : ℝ} (hw : 0 ≤ w)
    (hwq : w ≤ B a₁ a₂ ^ 2) (hp : B a₁ a₁ ≤ c) (hr : B a₂ a₂ ≤ c)
    (hdet : w ≤ (c - B a₁ a₁) * (c - B a₂ a₂)) :
    B a₁ a₁ ^ 2 + B a₂ a₂ ^ 2 + 2 * w ≤ ∑ j, phiC c (hA.eigenvalues j) := by
  have hs2 : ∀ F : τ → ℝ, ∑ j, F j = F a₁ + F a₂ := fun F => by
    rw [huniv, Finset.sum_pair hne]
  have hsum : hA.eigenvalues a₁ + hA.eigenvalues a₂ = B a₁ a₁ + B a₂ a₂ := by
    rw [← hs2 fun j => hA.eigenvalues j, ← rtrace_eq_sum_eigenvalues hA, rtrace_of_real hAB,
      hs2]
  have hsq : hA.eigenvalues a₁ ^ 2 + hA.eigenvalues a₂ ^ 2
      = B a₁ a₁ ^ 2 + B a₂ a₂ ^ 2 + 2 * B a₁ a₂ ^ 2 := by
    rw [← hs2 fun j => hA.eigenvalues j ^ 2, ← frobSq_hermitian_eq_sum_sq_eigenvalues hA,
      frobSq_of_real hAB, hs2, hs2, hs2, hsymm a₂ a₁]
    ring
  rw [hs2]
  exact phiC_pair_ge hsum ⟨B a₁ a₂, hwq, hsq⟩ hw hp hr hdet

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β] [DecidableEq β]
  {y : ι → ℝ} {lab : ι → Fin 2} {κ : ι → ι → ℝ} {η : ℝ} {G : Matrix ι ι ℂ}

/-- **Pair block.** If the block `k` of the partition `f` consists of two points `i ≠ j` at
distance less than `sep`, the clipped trace of the block of `G` is at least
`m_i² + m_j² + rew_i + rew_j - 40η`. -/
theorem pair_block_ge (hβ : BetaBound) (D : GramData y lab κ η G) (hG : G.PosSemidef)
    (f : ι → β) (k : β) {i j : ι} (hij : i ≠ j) (hclose : |y i - y j| < sep)
    (hfi : f i = k) (hfj : f j = k) (hfib : ∀ l, f l = k → l = i ∨ l = j) :
    ∑ a : {l // f l = k}, (mulOf (lab a) ^ 2 + rew (lab a) - 20 * η)
      ≤ ∑ t, phiC clipC ((blockOf_posSemidef f hG k).1.eigenvalues t) := by
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
      blockOf f G k a b = ((GramData.B lab κ a b : ℝ) : ℂ) := fun a b => D.entry a b
  have hsymm : ∀ a b : {l // f l = k}, GramData.B lab κ a b = GramData.B lab κ b a :=
    fun a b => D.B_symm a b
  -- multiplicities
  have hmi1 := one_le_mulOf (lab i)
  have hmi2 := mulOf_le_two (lab i)
  have hmj1 := one_le_mulOf (lab j)
  have hmj2 := mulOf_le_two (lab j)
  have hmm0 : 0 ≤ mulOf (lab i) * mulOf (lab j) := by positivity
  have hmm4 : mulOf (lab i) * mulOf (lab j) ≤ 4 := by nlinarith
  -- the off-diagonal entry
  have hβij : betaC - 3 * η ≤ κ i j ^ 2 := by
    have h1 := hβ (y i - y j) hclose.le
    have h2 := D.offdiag_sq_ge i j
    linarith
  have hβnum : betaC = 8824337 / 134217728 := rfl
  have hβη : 0 ≤ betaC - 3 * η := by rw [hβnum]; linarith
  -- the diagonal entries
  obtain ⟨hi1, hi2⟩ := D.diag_bounds i
  obtain ⟨hj1, hj2⟩ := D.diag_bounds j
  have hB11 : GramData.B lab κ a₁ a₁ = mulOf (lab i) * κ i i := GramData.B_diag lab κ i
  have hB22 : GramData.B lab κ a₂ a₂ = mulOf (lab j) * κ j j := GramData.B_diag lab κ j
  have hB12 : GramData.B lab κ a₁ a₂ ^ 2 = mulOf (lab i) * mulOf (lab j) * κ i j ^ 2 :=
    GramData.B_sq lab κ i j
  have hp : GramData.B lab κ a₁ a₁ ≤ 101 / 50 := by
    rw [hB11]
    have := mul_le_mul_of_nonneg_right hmi2 (by linarith : 0 ≤ κ i i)
    linarith
  have hr : GramData.B lab κ a₂ a₂ ≤ 101 / 50 := by
    rw [hB22]
    have := mul_le_mul_of_nonneg_right hmj2 (by linarith : 0 ≤ κ j j)
    linarith
  have hc : clipC = 67 / 20 := rfl
  set w : ℝ := mulOf (lab i) * mulOf (lab j) * (betaC - 3 * η) with hw
  have hw0 : 0 ≤ w := mul_nonneg hmm0 hβη
  have hw4 : w ≤ 3 / 10 := by
    have h1 : w ≤ 4 * (betaC - 3 * η) := mul_le_mul_of_nonneg_right hmm4 hβη
    rw [hβnum] at h1; linarith
  have hwq : w ≤ GramData.B lab κ a₁ a₂ ^ 2 := by
    rw [hB12]
    exact mul_le_mul_of_nonneg_left hβij hmm0
  have hdet : w ≤ (clipC - GramData.B lab κ a₁ a₁) * (clipC - GramData.B lab κ a₂ a₂) := by
    rw [hc]
    have h1 : (133 : ℝ) / 100 ≤ 67 / 20 - GramData.B lab κ a₁ a₁ := by linarith
    have h2 : (133 : ℝ) / 100 ≤ 67 / 20 - GramData.B lab κ a₂ a₂ := by linarith
    have h3 := mul_le_mul h1 h2 (by norm_num) (by linarith)
    linarith
  have hmain := pairBlock_ge (blockOf_posSemidef f hG k).1 hAB hsymm hne huniv hw0 hwq
    (by rw [hc]; linarith) (by rw [hc]; linarith) hdet
  refine le_trans ?_ hmain
  -- the arithmetic
  rw [huniv, Finset.sum_pair hne]
  have hd1 := D.diag_sq_ge i
  have hd2 := D.diag_sq_ge j
  have e1 : GramData.B lab κ a₁ a₁ ^ 2 = mulOf (lab i) ^ 2 * κ i i ^ 2 := by
    rw [hB11]; ring
  have e2 : GramData.B lab κ a₂ a₂ ^ 2 = mulOf (lab j) ^ 2 * κ j j ^ 2 := by
    rw [hB22]; ring
  have hrew := rew_add_rew_le (lab i) (lab j)
  have h6 : mulOf (lab i) * mulOf (lab j) * (3 * η) ≤ 4 * (3 * η) :=
    mul_le_mul_of_nonneg_right hmm4 (by linarith)
  have hwexp : w = mulOf (lab i) * mulOf (lab j) * betaC
      - mulOf (lab i) * mulOf (lab j) * (3 * η) := by rw [hw]; ring
  rw [e1, e2]
  show mulOf (lab i) ^ 2 + rew (lab i) - 20 * η + (mulOf (lab j) ^ 2 + rew (lab j) - 20 * η)
    ≤ mulOf (lab i) ^ 2 * κ i i ^ 2 + mulOf (lab j) ^ 2 * κ j j ^ 2 + 2 * w
  linarith

end Distinct839.Gram
