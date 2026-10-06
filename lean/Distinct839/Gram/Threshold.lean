/-
Distinct839/Gram/Threshold.lean — the threshold inequality in eigenvalue form.

For `P ⪰ 0`, `Q` Hermitian with at most `b` positive eigenvalues, and `c > 0`:

    ‖P + Q‖_F² ≥ 2c tr(P + Q) - 2c tr P + tr φ_c(P) - c² b,     φ_c(t) = t² - (t - c)₊².

This is the upstream proof of `Zeta23.ZeroSide.RankTraceMult.rank_trace_mult` ("Lemma R")
without its last step (the Schur–Jensen estimate that replaces the eigenvalues of `P` by its
diagonal in a rank-one decomposition). The skeleton is the same: `Q = Q₊ - Q₋`, drop
`tr(P Q₊) ≥ 0`, von Neumann's trace inequality for `tr(P Q₋)`, the termwise estimate
`(p - n)² ≥ c p + g_c(p) - 2 c n`, and `‖Q₊‖_F² ≥ 2c tr Q₊ - c² b`.

Also: the nonzero spectra of `W Wᴴ` and `Wᴴ W` agree, in the form of sums of `φ_c`.
-/
import Distinct839.Gram.PhiC

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23.ZeroSide.RankTraceMult

namespace Distinct839.Gram

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The trace of `φ_c(P)` is the trace of `g_c(P)` plus `c tr P`. -/
lemma sum_phiC_eigenvalues_eq {P : Matrix n n 𝕜} (hP : P.IsHermitian) (c : ℝ) :
    ∑ k, phiC c (hP.eigenvalues k) = ∑ k, gc c (hP.eigenvalues k) + c * rtrace P := by
  rw [rtrace_eq_sum_eigenvalues hP]
  exact sum_phiC_eq Finset.univ c _

/-- The upstream rank–trace inequality with the spectrum of `P` kept:
`c tr P + tr g_c(P) + 2c tr Q - c² b ≤ ‖P + Q‖_F²` for `P ⪰ 0`, `Q` Hermitian with at most `b`
positive eigenvalues, `c > 0`. (The proof of `rank_trace_mult` up to its Schur–Jensen step.) -/
theorem rank_trace_gc_eig {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
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
    rw [rtrace_eq_sum_eigenvalues hP.isHermitian]
    exact sum_eigenvalues_reindex hP.isHermitian id
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
  -- Step 5: the termwise estimate, with the eigenvalues of `P` kept.
  have hgc_eig : ∑ k, gc c (hP.1.eigenvalues k) = ∑ k, gc c (p k) :=
    sum_eigenvalues_reindex hP.isHermitian (gc c)
  have hstep5 : c * rtrace P + (∑ k, gc c (hP.1.eigenvalues k)) - 2 * c * rtrace Qm
      ≤ ∑ k, (p k - mm k) ^ 2 := by
    rw [htraceP, htraceQm, hgc_eig]
    exact sum_sq_sub_ge_gc hp_nn hm_nn hc.le
  -- Step 6: estimate on `Q₊`.
  have hstep6 : 2 * c * rtrace Qp - c ^ 2 * b ≤ frobSq Qp := by
    rw [hQp_def, rtrace_hermPosPart, frobSq_hermPosPart]
    refine sum_sq_lower_of_card_pos_le ?_ c
    calc #{i | (hQ.eigenvalues i)⁺ ≠ 0} = #{i | 0 < hQ.eigenvalues i} := by
          congr 1; ext i; simp [posPart_eq_zero, not_le]
      _ ≤ b := hb
  have htraceQ : 2 * c * rtrace Q = 2 * c * rtrace Qp - 2 * c * rtrace Qm := by
    rw [hQdec, rtrace_sub]; ring
  linarith [hstep4, hstep5, hstep6, hPQp, hexpand, htraceQ]

/-- **Threshold inequality, eigenvalue form**, for a general positive semidefinite `P`:
`2c tr(P + Q) - 2c tr P + tr φ_c(P) - c² b ≤ ‖P + Q‖_F²`. -/
theorem threshold_eig_posSemidef {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) {c : ℝ} (hc : 0 < c) :
    2 * c * rtrace (P + Q) - 2 * c * rtrace P + (∑ k, phiC c (hP.1.eigenvalues k)) - c ^ 2 * b
      ≤ frobSq (P + Q) := by
  have h := rank_trace_gc_eig hP hQ hb hc
  rw [sum_phiC_eigenvalues_eq hP.1 c, rtrace_add]
  linarith

end Distinct839.Gram

/-! ### The exported statements (namespace `Distinct839`) -/

namespace Distinct839

open Gram

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Threshold inequality, eigenvalue form**, for `P = ∑_j m_j v_j v_jᴴ` (upstream `Pmat`).
The hypothesis `0 ≤ m j` of the upstream `rank_trace_mult` is kept for the interface but is
not needed: `Pmat m v` is positive semidefinite for every `m`. -/
theorem threshold_eig {m : ι → ℝ} (_hm : ∀ j, 0 ≤ m j) (v : ι → n → 𝕜)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) {c : ℝ} (hc : 0 < c) :
    2 * c * rtrace (Pmat m v + Q) - 2 * c * rtrace (Pmat m v)
        + (∑ k, phiC c ((Pmat_posSemidef m v).1.eigenvalues k)) - c ^ 2 * b
      ≤ frobSq (Pmat m v + Q) :=
  threshold_eig_posSemidef (Pmat_posSemidef m v) hQ hb hc

/-- The nonzero spectra of `W Wᴴ` and `Wᴴ W` agree: sums of `φ_c` over the two spectra are equal
(`c ≥ 0`, so that `φ_c(0) = 0`; for `c < 0` and `card n ≠ card ι` the identity fails). -/
theorem sum_phiC_eigenvalues_comm (W : Matrix n ι 𝕜) (c : ℝ) (hc : 0 ≤ c) :
    ∑ i, phiC c ((Matrix.posSemidef_self_mul_conjTranspose W).1.eigenvalues i)
      = ∑ j, phiC c ((Matrix.posSemidef_conjTranspose_mul_self W).1.eigenvalues j) :=
  sum_eigenvalues_comm W (phiC c) (phiC_zero hc)

end Distinct839
