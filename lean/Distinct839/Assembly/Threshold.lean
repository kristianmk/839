/-
Distinct839/Assembly/Threshold.lean — the threshold inequality in eigenvalue form.

For `P ⪰ 0`, `Q` Hermitian with at most `b` positive eigenvalues, and a threshold `c > 0`,

    2c·tr(P + Q) − 2c·tr P + ∑_k φ_c(λ_k(P)) − c²·b ≤ ‖P + Q‖_F²,     φ_c(t) = t² − (t − c)₊².

This is the upstream proof of "Lemma R" (`Zeta23.ZeroSide.RankTraceMult.rank_trace_mult`) stopped
before its last step (the Schur–Jensen passage from the eigenvalues of `P` to its diagonal), and
written for an arbitrary positive semidefinite `P`. The second part of the file transfers the
eigenvalue sum from `W Wᴴ` to the Gram matrix `Wᴴ W`.
-/
import Zeta23.ZeroSide.RankTraceMult
import Distinct839.Defs

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Distinct839.Assembly

open Zeta23.ZeroSide.RankTraceMult

/-! ### The clipped square -/

/-- `φ_c(t) = g_c(t) + c·t`, where `g_c` is the upstream function `gc`. -/
lemma phiC_eq_gc_add (c t : ℝ) : phiC c t = gc c t + c * t := by
  unfold phiC gc; ring

/-- `φ_c(0) = 0` for `c ≥ 0`. -/
lemma phiC_zero {c : ℝ} (hc : 0 ≤ c) : phiC c 0 = 0 := by
  unfold phiC
  rw [max_eq_right (by linarith)]; ring

section Threshold

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Threshold inequality, `g_c` form.** For `P ⪰ 0`, `Q` Hermitian with `n₊(Q) ≤ b` and `c > 0`:
`c·tr P + ∑_k g_c(λ_k(P)) + 2c·tr Q − c²·b ≤ ‖P + Q‖_F²`. -/
theorem threshold_eig_gc {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) {c : ℝ} (hc : 0 < c) :
    c * rtrace P + (∑ k, gc c (hP.1.eigenvalues k)) + 2 * c * rtrace Q - c ^ 2 * b
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
  -- Step 5: the termwise scalar estimate, kept in eigenvalue form.
  have hgc_eig : ∑ k, gc c (hP.1.eigenvalues k) = ∑ k, gc c (p k) :=
    sum_eigenvalues_reindex hP.isHermitian (gc c)
  have hstep5 : c * rtrace P + (∑ k, gc c (hP.1.eigenvalues k)) - 2 * c * rtrace Qm
      ≤ ∑ k, (p k - mm k) ^ 2 := by
    rw [htraceP, htraceQm, hgc_eig]
    exact sum_sq_sub_ge_gc hp_nn hm_nn hc.le
  -- Step 6: the estimate on `Q₊`.
  have hstep6 : 2 * c * rtrace Qp - c ^ 2 * b ≤ frobSq Qp := by
    rw [hQp_def, rtrace_hermPosPart, frobSq_hermPosPart]
    refine sum_sq_lower_of_card_pos_le ?_ c
    calc #{i | (hQ.eigenvalues i)⁺ ≠ 0} = #{i | 0 < hQ.eigenvalues i} := by
          congr 1; ext i; simp [posPart_eq_zero, not_le]
      _ ≤ b := hb
  have htraceQ : 2 * c * rtrace Q = 2 * c * rtrace Qp - 2 * c * rtrace Qm := by
    rw [hQdec, rtrace_sub]; ring
  linarith [hstep4, hstep5, hstep6, hPQp, hexpand, htraceQ]

/-- **Threshold inequality, `φ_c` form** (the threshold lemma of the paper):
`2c·tr(P + Q) − 2c·tr P + ∑_k φ_c(λ_k(P)) − c²·b ≤ ‖P + Q‖_F²`. -/
theorem threshold_eig_phiC {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) {c : ℝ} (hc : 0 < c) :
    2 * c * rtrace (P + Q) - 2 * c * rtrace P + (∑ k, phiC c (hP.1.eigenvalues k)) - c ^ 2 * b
      ≤ frobSq (P + Q) := by
  have h := threshold_eig_gc hP hQ hb hc
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

/-- The eigenvalue sum of `φ_c` is the same for `W Wᴴ` and for the Gram matrix `Wᴴ W`. -/
theorem sum_phiC_eigenvalues_comm (W : Matrix n ι 𝕜) {c : ℝ} (hc : 0 ≤ c) :
    ∑ i, phiC c ((Matrix.posSemidef_self_mul_conjTranspose W).1.eigenvalues i)
      = ∑ j, phiC c ((Matrix.posSemidef_conjTranspose_mul_self W).1.eigenvalues j) :=
  sum_eigenvalues_comm W (phiC c) (phiC_zero hc)

/-- **Threshold inequality for `P = W Wᴴ`, in terms of the Gram matrix `Wᴴ W`.** -/
theorem threshold_gram (W : Matrix n ι 𝕜) {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) {c : ℝ} (hc : 0 < c) :
    2 * c * rtrace (W * Wᴴ + Q) - frobSq (W * Wᴴ + Q)
      ≤ 2 * c * rtrace (W * Wᴴ)
        - (∑ j, phiC c ((Matrix.posSemidef_conjTranspose_mul_self W).1.eigenvalues j))
        + c ^ 2 * b := by
  have h := threshold_eig_phiC (Matrix.posSemidef_self_mul_conjTranspose W) hQ hb hc
  rw [sum_phiC_eigenvalues_comm W hc.le] at h
  linarith

end Gram

end Distinct839.Assembly
