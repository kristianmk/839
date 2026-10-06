/-
Distinct839/Gram/Pinching.lean — trace pinching for the convex functions `g_c` and `φ_c`.

Let `G` be a positive semidefinite matrix on the index set `ι` and let `f : ι → β` split `ι`
into the blocks `{i | f i = k}`. Write `G_k` for the principal submatrix of `G` on block `k`.
Then

    ∑_k ∑ φ_c(eigenvalues of G_k) ≤ ∑ φ_c(eigenvalues of G),

and the same for `g_c`. Proof: let `V` have as columns the eigenvectors of the blocks, extended
by zero. Then `V Vᴴ = 1`, the matrix `Vᴴ G V` has the same characteristic polynomial as `G`, and
its diagonal consists of the eigenvalues of the blocks. The upstream Schur–Jensen inequality
`sum_gc_diag_le_sum_gc_eigenvalues` (diagonal against spectrum, for `g_c`) applied to `Vᴴ G V`
gives the claim for `g_c`; the traces agree, which gives it for `φ_c(t) = g_c(t) + c t`.
-/
import Distinct839.Gram.PhiC

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Polynomial
open scoped ComplexOrder BigOperators
open Zeta23.ZeroSide.RankTraceMult

namespace Distinct839.Gram

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ### Eigenvalue sums depend only on the characteristic polynomial -/

/-- A sum over the eigenvalues of a Hermitian matrix, written through the roots of the
characteristic polynomial. -/
lemma sum_eigenvalues_eq_roots {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) (g : ℝ → ℝ) :
    ∑ i, g (hA.eigenvalues i)
      = ((A.charpoly.roots).map fun z : 𝕜 => g (RCLike.re z)).sum := by
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  show (Finset.univ.val.map fun i => g (hA.eigenvalues i)).sum = _
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun i _ => ?_)
  simp only [Function.comp_apply, RCLike.ofReal_re]

/-- Hermitian matrices (possibly on different index types) with the same characteristic
polynomial have the same eigenvalue sums. -/
theorem sum_eigenvalues_eq_of_charpoly_eq {A : Matrix ι ι 𝕜} {B : Matrix σ σ 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A.charpoly = B.charpoly) (g : ℝ → ℝ) :
    ∑ i, g (hA.eigenvalues i) = ∑ j, g (hB.eigenvalues j) := by
  rw [sum_eigenvalues_eq_roots hA, sum_eigenvalues_eq_roots hB, h]

/-- Conjugation by a matrix `V` with `V Vᴴ = 1` between index types of the same cardinality
does not change the characteristic polynomial. -/
lemma charpoly_conj_eq (G : Matrix ι ι 𝕜) (V : Matrix ι σ 𝕜) (hV : V * Vᴴ = 1)
    (hcard : Fintype.card σ = Fintype.card ι) :
    (Vᴴ * G * V).charpoly = G.charpoly := by
  have h := Matrix.charpoly_mul_comm' (G * V) Vᴴ
  rw [Matrix.mul_assoc G V Vᴴ, hV, Matrix.mul_one, hcard, ← Matrix.mul_assoc] at h
  exact (mul_left_cancel₀ (pow_ne_zero _ Polynomial.X_ne_zero) h).symm

/-- **Schur–Jensen for `g_c` in a rotated basis.** If `V Vᴴ = 1`, the diagonal of `Vᴴ G V` is
dominated by the spectrum of `G` along `g_c`. -/
theorem sum_gc_diag_conj_le {G : Matrix ι ι 𝕜} (hG : G.PosSemidef) (V : Matrix ι σ 𝕜)
    (hV : V * Vᴴ = 1) (hcard : Fintype.card σ = Fintype.card ι) {c : ℝ} (hc : 0 ≤ c) :
    ∑ j, gc c (RCLike.re ((Vᴴ * G * V) j j)) ≤ ∑ i, gc c (hG.1.eigenvalues i) := by
  have hM : (Vᴴ * G * V).PosSemidef := hG.conjTranspose_mul_mul_same V
  calc ∑ j, gc c (RCLike.re ((Vᴴ * G * V) j j))
      ≤ ∑ j, gc c (hM.1.eigenvalues j) := sum_gc_diag_le_sum_gc_eigenvalues hM hc
    _ = ∑ i, gc c (hG.1.eigenvalues i) :=
        sum_eigenvalues_eq_of_charpoly_eq hM.1 hG.1 (charpoly_conj_eq G V hV hcard) _

/-! ### The block structure given by a map `f : ι → β` -/

section Blocks

variable {β : Type*} [Fintype β] [DecidableEq β] (f : ι → β)

/-- The principal submatrix of `G` on the block `{i | f i = k}`. -/
def blockOf (G : Matrix ι ι 𝕜) (k : β) : Matrix {i // f i = k} {i // f i = k} 𝕜 :=
  G.submatrix Subtype.val Subtype.val

@[simp] lemma blockOf_apply (G : Matrix ι ι 𝕜) (k : β) (a b : {i // f i = k}) :
    blockOf f G k a b = G a b := rfl

lemma blockOf_posSemidef {G : Matrix ι ι 𝕜} (hG : G.PosSemidef) (k : β) :
    (blockOf f G k).PosSemidef := hG.submatrix _

/-- A sum over `ι` of a function supported on the block `k` is the sum over the block. -/
lemma sum_eq_sum_block {M : Type*} [AddCommMonoid M] (k : β) (F : ι → M)
    (hF : ∀ i, f i ≠ k → F i = 0) : ∑ i, F i = ∑ a : {i // f i = k}, F a := by
  have h : ∑ i ∈ Finset.univ.filter (fun i => f i = k), F i = ∑ a : {i // f i = k}, F a :=
    Finset.sum_subtype _ (by simp) F
  rw [← h]
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun i _ hi => ?_).symm
  exact hF i (by simpa using hi)

/-- The unitary matrix of eigenvectors of the block `k` of `G`. -/
def blockU {G : Matrix ι ι 𝕜} (hG : G.PosSemidef) (k : β) :
    Matrix {i // f i = k} {i // f i = k} 𝕜 :=
  ((blockOf_posSemidef f hG k).1.eigenvectorUnitary : Matrix {i // f i = k} {i // f i = k} 𝕜)

lemma blockU_mul_conjTranspose {G : Matrix ι ι 𝕜} (hG : G.PosSemidef) (k : β) :
    blockU f hG k * (blockU f hG k)ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.1 (blockOf_posSemidef f hG k).1.eigenvectorUnitary.2

/-- The spectral theorem for the block `k`: `Uᴴ G_k U` is diagonal. -/
lemma blockU_conj {G : Matrix ι ι 𝕜} (hG : G.PosSemidef) (k : β) :
    (blockU f hG k)ᴴ * blockOf f G k * blockU f hG k
      = diagonal (RCLike.ofReal ∘ (blockOf_posSemidef f hG k).1.eigenvalues) := by
  have := (blockOf_posSemidef f hG k).1.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at this
  exact this

/-- The matrix whose columns are the eigenvectors of the blocks of `G`, extended by zero.
Columns are indexed by pairs (block `k`, index in block `k`). -/
def blockEigenMatrix {G : Matrix ι ι 𝕜} (hG : G.PosSemidef) :
    Matrix ι (Σ k : β, {i // f i = k}) 𝕜 :=
  fun i x => if h : f i = x.1 then blockU f hG x.1 ⟨i, h⟩ x.2 else 0

lemma blockEigenMatrix_apply_same {G : Matrix ι ι 𝕜} (hG : G.PosSemidef) (k : β)
    (a j : {i // f i = k}) :
    blockEigenMatrix f hG a.1 ⟨k, j⟩ = blockU f hG k a j := by
  show (if h : f a.1 = k then blockU f hG k ⟨a.1, h⟩ j else 0) = _
  rw [dif_pos a.2]

lemma blockEigenMatrix_apply_ne {G : Matrix ι ι 𝕜} (hG : G.PosSemidef) (i : ι) (k : β)
    (j : {i // f i = k}) (h : f i ≠ k) : blockEigenMatrix f hG i ⟨k, j⟩ = 0 := by
  show (if h : f i = k then blockU f hG k ⟨i, h⟩ j else 0) = 0
  rw [dif_neg h]

/-- The columns of `blockEigenMatrix` are orthonormal and complete: `V Vᴴ = 1`. -/
lemma blockEigenMatrix_mul_conjTranspose {G : Matrix ι ι 𝕜} (hG : G.PosSemidef) :
    blockEigenMatrix f hG * (blockEigenMatrix f hG)ᴴ = 1 := by
  ext i i'
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  simp only [conjTranspose_apply]
  -- only the block of `i` contributes
  rw [Finset.sum_eq_single (f i)]
  · have hUU := blockU_mul_conjTranspose f hG (f i)
    by_cases h : f i' = f i
    · have h1 : ∀ j : {l // f l = f i},
          blockEigenMatrix f hG i ⟨f i, j⟩ * star (blockEigenMatrix f hG i' ⟨f i, j⟩)
            = blockU f hG (f i) ⟨i, rfl⟩ j * star (blockU f hG (f i) ⟨i', h⟩ j) := fun j => by
        rw [blockEigenMatrix_apply_same f hG (f i) ⟨i, rfl⟩ j,
          blockEigenMatrix_apply_same f hG (f i) ⟨i', h⟩ j]
      rw [Finset.sum_congr rfl fun j _ => h1 j]
      have h2 := congrFun (congrFun hUU ⟨i, rfl⟩) ⟨i', h⟩
      rw [Matrix.mul_apply] at h2
      simp only [conjTranspose_apply] at h2
      rw [h2, Matrix.one_apply, Matrix.one_apply]
      simp only [Subtype.mk.injEq]
    · have hne : i ≠ i' := fun hii => h (by rw [hii])
      rw [Matrix.one_apply_ne hne]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [blockEigenMatrix_apply_ne f hG i' (f i) j h, star_zero, mul_zero]
  · intro k _ hk
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [blockEigenMatrix_apply_ne f hG i k j (Ne.symm hk), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The diagonal of `Vᴴ G V` consists of the eigenvalues of the blocks. -/
lemma blockEigenMatrix_conj_diag {G : Matrix ι ι 𝕜} (hG : G.PosSemidef) (k : β)
    (j : {i // f i = k}) :
    ((blockEigenMatrix f hG)ᴴ * G * blockEigenMatrix f hG) ⟨k, j⟩ ⟨k, j⟩
      = ((blockOf_posSemidef f hG k).1.eigenvalues j : 𝕜) := by
  have hjj := congrFun (congrFun (blockU_conj f hG k) j) j
  rw [Matrix.diagonal_apply_eq, Function.comp_apply] at hjj
  rw [← hjj]
  -- compare the two double sums
  simp only [Matrix.mul_apply, conjTranspose_apply]
  rw [sum_eq_sum_block f k]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [blockEigenMatrix_apply_same f hG k b j]
    congr 1
    rw [sum_eq_sum_block f k]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [blockEigenMatrix_apply_same f hG k a j, blockOf_apply]
    · intro i hi
      rw [blockEigenMatrix_apply_ne f hG i k j hi, star_zero, zero_mul]
  · intro i hi
    rw [blockEigenMatrix_apply_ne f hG i k j hi, mul_zero]

/-- **Trace pinching for `g_c`.** The sum of `g_c` over the eigenvalues of all diagonal blocks
is at most the sum over the eigenvalues of the full positive semidefinite matrix. -/
theorem pinching_gc {G : Matrix ι ι 𝕜} (hG : G.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    ∑ k, ∑ j, gc c ((blockOf_posSemidef f hG k).1.eigenvalues j)
      ≤ ∑ i, gc c (hG.1.eigenvalues i) := by
  have hcard : Fintype.card (Σ k : β, {i // f i = k}) = Fintype.card ι :=
    Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  have h := sum_gc_diag_conj_le hG (blockEigenMatrix f hG)
    (blockEigenMatrix_mul_conjTranspose f hG) hcard hc
  rw [Fintype.sum_sigma] at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [blockEigenMatrix_conj_diag f hG k j, RCLike.ofReal_re]

/-- The traces of the diagonal blocks add up to the trace. -/
lemma sum_rtrace_blockOf (G : Matrix ι ι 𝕜) :
    ∑ k, rtrace (blockOf f G k) = rtrace G := by
  unfold rtrace Matrix.trace
  simp only [map_sum, Matrix.diag_apply, blockOf_apply]
  exact Fintype.sum_fiberwise f fun i => RCLike.re (G i i)

/-- **Trace pinching for `φ_c`.** The sum of `φ_c` over the eigenvalues of all diagonal blocks
is at most the sum over the eigenvalues of the full positive semidefinite matrix. -/
theorem pinching_phiC {G : Matrix ι ι 𝕜} (hG : G.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    ∑ k, ∑ j, phiC c ((blockOf_posSemidef f hG k).1.eigenvalues j)
      ≤ ∑ i, phiC c (hG.1.eigenvalues i) := by
  have h := pinching_gc f hG hc
  have htr : ∑ k, ∑ j, (blockOf_posSemidef f hG k).1.eigenvalues j
      = ∑ i, hG.1.eigenvalues i := by
    rw [← rtrace_eq_sum_eigenvalues hG.1, ← sum_rtrace_blockOf f G]
    exact Finset.sum_congr rfl fun k _ =>
      (rtrace_eq_sum_eigenvalues (blockOf_posSemidef f hG k).1).symm
  have hL : ∑ k, ∑ j, phiC c ((blockOf_posSemidef f hG k).1.eigenvalues j)
      = ∑ k, ∑ j, gc c ((blockOf_posSemidef f hG k).1.eigenvalues j)
        + c * ∑ k, ∑ j, (blockOf_posSemidef f hG k).1.eigenvalues j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => sum_phiC_eq Finset.univ c _
  rw [hL, sum_phiC_eq Finset.univ c, htr]
  linarith

end Blocks

end Distinct839.Gram
