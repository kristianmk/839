/-
Further/Threshold.lean — the threshold inequality with two parameters.

For `P ⪰ 0`, `Q` Hermitian with at most `b` positive eigenvalues, and two levels `0 < c ≤ t`,

    2t·tr(P + Q) − 2t·tr P + ∑_k φ_c(λ_k(P)) − t²·b ≤ ‖P + Q‖_F²,     φ_c(s) = s² − (s − c)₊².

The clipping level `c` acts on the positive semidefinite part `P`, the level `t` on the positive
eigenvalues of `Q`. For `t = c` this is `Distinct839.Assembly.threshold_eig_phiC`. The proof is
the same, with one change: the positive part of `Q` is bounded with `t` in place of `c`,

    ‖Q₊‖_F² ≥ 2t·tr Q₊ − t²·b,

and the term `(2t − 2c)·tr Q₋ ≥ 0` that then appears is dropped.

The second part restates the inequality for `P = W Wᴴ` in terms of the Gram matrix `Wᴴ W`, and
the third part applies it to the block data of the zeros (`seam_block2`, the two-parameter form
of `Distinct839.Assembly.seam_block`).
-/
import Distinct839.Assembly.Block

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Further

open Zeta23 Zeta23.ZeroSide Zeta23.ZeroSide.RankTraceMult
open Distinct839 (phiC)
open Distinct839.Assembly (phiC_eq_gc_add sum_phiC_eigenvalues_comm goodW restQ
  restQ_isHermitian posIndex_restQ_le blockP_add_blockQ_eq rtrace_goodW_le)

section Threshold

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Threshold inequality with two parameters, `g_c` form.** For `P ⪰ 0`, `Q` Hermitian with
`n₊(Q) ≤ b` and `0 < c ≤ t`:
`c·tr P + ∑_k g_c(λ_k(P)) + 2t·tr Q − t²·b ≤ ‖P + Q‖_F²`. -/
theorem threshold2_eig_gc {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) {c t : ℝ} (hc : 0 < c) (hct : c ≤ t) :
    c * rtrace P + (∑ k, gc c (hP.1.eigenvalues k)) + 2 * t * rtrace Q - t ^ 2 * b
      ≤ frobSq (P + Q) := by
  classical
  -- Positive and negative parts of `Q`.
  set Qp := hermPosPart hQ with hQp_def
  set Qm := hermNegPart hQ with hQm_def
  have hQdec : Q = Qp - Qm := (hermPosPart_sub_hermNegPart hQ).symm
  have hQp_psd : Qp.PosSemidef := hermPosPart_posSemidef hQ
  have hQm_psd : Qm.PosSemidef := hermNegPart_posSemidef hQ
  have hQpQm : Qp * Qm = 0 := hermPosPart_mul_hermNegPart hQ
  set d := Fintype.card n
  set p : Fin d → ℝ := hP.isHermitian.eigenvalues₀
  set mm : Fin d → ℝ := hQm_psd.isHermitian.eigenvalues₀
  have hp_nn : ∀ k, 0 ≤ p k := fun k => by
    rw [show p k = hP.isHermitian.eigenvalues (eigEquiv k) from
      (eigenvalues_eigEquiv hP.isHermitian k).symm]
    exact hP.eigenvalues_nonneg _
  have hm_nn : ∀ k, 0 ≤ mm k := fun k => by
    rw [show mm k = hQm_psd.isHermitian.eigenvalues (eigEquiv k) from
      (eigenvalues_eigEquiv hQm_psd.isHermitian k).symm]
    exact hQm_psd.eigenvalues_nonneg _
  have htraceP : rtrace P = ∑ k, p k := by
    rw [rtrace_eq_sum_eigenvalues hP.isHermitian]; exact sum_eigenvalues_reindex hP.isHermitian id
  have htraceQm : rtrace Qm = ∑ k, mm k := by
    rw [rtrace_eq_sum_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian id
  have hfrobP : frobSq P = ∑ k, (p k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hP.isHermitian]
    exact sum_eigenvalues_reindex hP.isHermitian (· ^ 2)
  have hfrobQm : frobSq Qm = ∑ k, (mm k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian (· ^ 2)
  -- Step 1: Frobenius expansion.
  have hexpand : frobSq (P + Q)
      = frobSq P + 2 * RCLike.re (P * Qp).trace - 2 * RCLike.re (P * Qm).trace
        + frobSq Qp + frobSq Qm := by
    have h1 : frobSq (-Qm) = frobSq Qm := by unfold frobSq; rw [conjTranspose_neg, neg_mul_neg]
    have h2 : RCLike.re (Qp * -Qm).trace = 0 := by rw [mul_neg, hQpQm]; simp
    rw [hQdec, frobSq_add_hermitian hP.isHermitian (hQp_psd.isHermitian.sub hQm_psd.isHermitian),
      sub_eq_add_neg Qp Qm, frobSq_add_hermitian hQp_psd.isHermitian hQm_psd.isHermitian.neg,
      h1, h2, mul_add, mul_neg, trace_add, trace_neg, map_add, map_neg]
    ring
  -- Step 2: drop `tr(P Q₊) ≥ 0`.
  have hPQp : 0 ≤ RCLike.re (P * Qp).trace := trace_mul_nonneg_of_posSemidef hP hQp_psd
  -- Step 3: von Neumann.
  have hvN : RCLike.re (P * Qm).trace ≤ ∑ k, p k * mm k :=
    vonNeumann_trace_ineq hP.isHermitian hQm_psd.isHermitian
  have hstep4 : ∑ k, (p k - mm k) ^ 2
      ≤ frobSq P - 2 * RCLike.re (P * Qm).trace + frobSq Qm := by
    have hsplit : ∑ k, (p k - mm k) ^ 2
        = ∑ k, (p k) ^ 2 - 2 * ∑ k, p k * mm k + ∑ k, (mm k) ^ 2 := by
      simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
    rw [hsplit, hfrobP, hfrobQm]; linarith
  -- Step 5: the termwise scalar estimate at level `c`, kept in eigenvalue form.
  have hgc_eig : ∑ k, gc c (hP.1.eigenvalues k) = ∑ k, gc c (p k) :=
    sum_eigenvalues_reindex hP.isHermitian (gc c)
  have hstep5 : c * rtrace P + (∑ k, gc c (hP.1.eigenvalues k)) - 2 * c * rtrace Qm
      ≤ ∑ k, (p k - mm k) ^ 2 := by
    rw [htraceP, htraceQm, hgc_eig]
    exact sum_sq_sub_ge_gc hp_nn hm_nn hc.le
  -- Step 6: the estimate on `Q₊`, at level `t`.
  have hstep6 : 2 * t * rtrace Qp - t ^ 2 * b ≤ frobSq Qp := by
    rw [hQp_def, rtrace_hermPosPart, frobSq_hermPosPart]
    refine sum_sq_lower_of_card_pos_le ?_ t
    calc #{i | (hQ.eigenvalues i)⁺ ≠ 0} = #{i | 0 < hQ.eigenvalues i} := by
          congr 1; ext i; simp [posPart_eq_zero, not_le]
      _ ≤ b := hb
  have htraceQ : 2 * t * rtrace Q = 2 * t * rtrace Qp - 2 * t * rtrace Qm := by
    rw [hQdec, rtrace_sub]; ring
  -- Step 7: the term `(2t − 2c)·tr Q₋` is nonnegative and is dropped.
  have hQm0 : 0 ≤ rtrace Qm := by
    rw [htraceQm]; exact Finset.sum_nonneg fun k _ => hm_nn k
  have hdrop : 0 ≤ (t - c) * rtrace Qm := mul_nonneg (sub_nonneg.mpr hct) hQm0
  linarith [hstep4, hstep5, hstep6, hPQp, hexpand, htraceQ, hdrop]

/-- **Threshold inequality with two parameters, `φ_c` form**:
`2t·tr(P + Q) − 2t·tr P + ∑_k φ_c(λ_k(P)) − t²·b ≤ ‖P + Q‖_F²` for `0 < c ≤ t`. -/
theorem threshold2_eig_phiC {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) {c t : ℝ} (hc : 0 < c) (hct : c ≤ t) :
    2 * t * rtrace (P + Q) - 2 * t * rtrace P + (∑ k, phiC c (hP.1.eigenvalues k)) - t ^ 2 * b
      ≤ frobSq (P + Q) := by
  have h := threshold2_eig_gc hP hQ hb hc hct
  have hsum : ∑ k, phiC c (hP.1.eigenvalues k)
      = (∑ k, gc c (hP.1.eigenvalues k)) + c * rtrace P := by
    rw [rtrace_eq_sum_eigenvalues hP.isHermitian, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => phiC_eq_gc_add c _
  rw [rtrace_add, hsum]
  linarith

end Threshold

section Gram

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Threshold inequality with two parameters for `P = W Wᴴ`, in terms of the Gram matrix
`Wᴴ W`.** -/
theorem threshold2_gram (W : Matrix n ι 𝕜) {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) {c t : ℝ} (hc : 0 < c) (hct : c ≤ t) :
    2 * t * rtrace (W * Wᴴ + Q) - frobSq (W * Wᴴ + Q)
      ≤ 2 * t * rtrace (W * Wᴴ)
        - (∑ j, phiC c ((Matrix.posSemidef_conjTranspose_mul_self W).1.eigenvalues j))
        + t ^ 2 * b := by
  have h := threshold2_eig_phiC (Matrix.posSemidef_self_mul_conjTranspose W) hQ hb hc hct
  rw [sum_phiC_eigenvalues_comm W hc.le] at h
  linarith

end Gram

section Block

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d) {good : Finset ι}

/-- **Block seam with two parameters.** With `G = Wᴴ W` the weighted Gram matrix of the good
indices and `0 < c ≤ t`,
`2t·tr Â − ‖Â‖_F² ≤ 2t·∑_{good} m_z − ∑_j φ_c(λ_j(G)) + t²·(p + #(onLine \ good))`. -/
theorem seam_block2 (Pr : D.PairReps) (hgood : good ⊆ D.onLine) {nrm : ℝ} (hnrm : 0 < nrm)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ nrm) {c t : ℝ} (hc : 0 < c) (hct : c ≤ t) :
    2 * t * rtrace (D.blockP nrm + D.blockQ nrm) - frobSq (D.blockP nrm + D.blockQ nrm)
      ≤ 2 * t * ∑ z ∈ good, (D.m z : ℝ)
        - (∑ j, phiC c
            ((Matrix.posSemidef_conjTranspose_mul_self (goodW D good nrm)).1.eigenvalues j))
        + t ^ 2 * ((Pr.p + #(D.onLine \ good) : ℕ) : ℝ) := by
  rw [blockP_add_blockQ_eq D hgood hnrm]
  have h := threshold2_gram (goodW D good nrm) (restQ_isHermitian D good hnrm)
    (posIndex_restQ_le D good Pr hnrm) hc hct
  have htr := rtrace_goodW_le D hgood hnrm hPois
  have : 2 * t * rtrace (goodW D good nrm * (goodW D good nrm)ᴴ)
      ≤ 2 * t * ∑ z ∈ good, (D.m z : ℝ) := mul_le_mul_of_nonneg_left htr (by linarith)
  linarith

end Block

end Further
