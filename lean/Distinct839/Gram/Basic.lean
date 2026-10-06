/-
Distinct839/Gram/Basic.lean — elementary facts used by the finite Gram theorem.

* The kernel: `K 0 = 1` and the crude bound `|K| ≤ 4/3`, both directly from the definition
  (`K(t) = sinc(t) + ∑ a_j (sinc(t - j) + sinc(t + j))/2`, `|sinc| ≤ 1`, `∑ |a_j| < 1/3`).
* Multiplicities and rewards: `1 ≤ mulOf l ≤ 2` and `rew a + rew b ≤ 2 ab β`.
* Trace and Frobenius norm of a complex matrix with real entries.
* The structure `GramData`, which collects the hypotheses on the labelled Gram matrix.
-/
import Distinct839.Spec
import Distinct839.Gram.PhiC

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Distinct839.Gram

/-! ### The kernel -/

lemma abs_sincN_le_one (t : ℝ) : |sincN t| ≤ 1 := Real.abs_sinc_le_one _

@[simp] lemma sincN_zero : sincN 0 = 1 := by simp [sincN]

/-- The normalised sinc vanishes at the nonzero integers. -/
lemma sincN_int {n : ℤ} (hn : n ≠ 0) : sincN n = 0 := by
  unfold sincN
  rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero (Int.cast_ne_zero.2 hn)), mul_comm,
    Real.sin_int_mul_pi, zero_div]

/-- `K(0) = 1`. -/
theorem K_zero : K 0 = 1 := by
  unfold K
  have h1 : ∀ j : Fin 6, sincN (0 - (((j : ℕ) : ℝ) + 1)) = 0 := fun j => by
    have h := sincN_int (n := -((j : ℕ) : ℤ) - 1) (by omega)
    convert h using 2
    push_cast; ring
  have h2 : ∀ j : Fin 6, sincN (0 + (((j : ℕ) : ℝ) + 1)) = 0 := fun j => by
    have h := sincN_int (n := ((j : ℕ) : ℤ) + 1) (by omega)
    convert h using 2
    push_cast; ring
  simp only [h1, h2, add_zero, mul_zero, Finset.sum_const_zero, sincN_zero]

/-- `∑ |a_j| = 0.321589`. -/
lemma sum_abs_aC : ∑ j, |aC j| = 321589 / 1000000 := by
  have h : ∀ j, |aC j| = ((|aInt j| : ℤ) : ℝ) / 1000000 := fun j => by
    unfold aC
    rw [abs_div, Int.cast_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1000000)]
  simp_rw [h]
  rw [← Finset.sum_div, ← Int.cast_sum]
  have h2 : ∑ j, |aInt j| = 321589 := by decide
  rw [h2]; norm_num

/-- Crude bound `|K| ≤ 4/3`, from `|sinc| ≤ 1` and `∑ |a_j| < 1/3`. (The sharp bound is
`|K| ≤ K(0) = 1`; it is not needed here.) -/
theorem abs_K_le (t : ℝ) : |K t| ≤ 4 / 3 := by
  unfold K
  have hterm : ∀ j : Fin 6,
      |aC j / 2 * (sincN (t - (((j : ℕ) : ℝ) + 1)) + sincN (t + (((j : ℕ) : ℝ) + 1)))|
        ≤ |aC j| := fun j => by
    have h1 := abs_sincN_le_one (t - (((j : ℕ) : ℝ) + 1))
    have h2 := abs_sincN_le_one (t + (((j : ℕ) : ℝ) + 1))
    have h3 := abs_add_le (sincN (t - (((j : ℕ) : ℝ) + 1))) (sincN (t + (((j : ℕ) : ℝ) + 1)))
    rw [abs_mul, abs_div, abs_two]
    have h4 : (0 : ℝ) ≤ |aC j| := abs_nonneg _
    have h5 : |sincN (t - (((j : ℕ) : ℝ) + 1)) + sincN (t + (((j : ℕ) : ℝ) + 1))| ≤ 2 := by
      linarith
    nlinarith [mul_nonneg h4 (sub_nonneg.2 h5)]
  calc |sincN t + ∑ j : Fin 6,
          aC j / 2 * (sincN (t - (((j : ℕ) : ℝ) + 1)) + sincN (t + (((j : ℕ) : ℝ) + 1)))|
      ≤ |sincN t| + |∑ j : Fin 6,
          aC j / 2 * (sincN (t - (((j : ℕ) : ℝ) + 1)) + sincN (t + (((j : ℕ) : ℝ) + 1)))| :=
        abs_add_le _ _
    _ ≤ 1 + ∑ j : Fin 6, |aC j| :=
        add_le_add (abs_sincN_le_one t)
          ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hterm j))
    _ ≤ 4 / 3 := by rw [sum_abs_aC]; norm_num

/-- If `k` is within `η` of a number `K₀` with `|K₀| ≤ 4/3`, then `k² ≥ K₀² - 3η`. -/
lemma sq_ge_of_close {k K₀ η : ℝ} (hK : |K₀| ≤ 4 / 3) (h : |k - K₀| ≤ η) :
    K₀ ^ 2 - 3 * η ≤ k ^ 2 := by
  obtain ⟨h1, h2⟩ := abs_le.1 h
  obtain ⟨h3, h4⟩ := abs_le.1 hK
  have e : k ^ 2 = K₀ ^ 2 + 2 * K₀ * (k - K₀) + (k - K₀) ^ 2 := by ring
  have p1 := mul_nonneg (sub_nonneg.2 h2) (by linarith : 0 ≤ 4 / 3 - K₀)
  have p2 := mul_nonneg (by linarith : 0 ≤ η + (k - K₀)) (by linarith : 0 ≤ 4 / 3 + K₀)
  nlinarith [sq_nonneg (k - K₀)]

/-! ### Multiplicities and rewards -/

lemma one_le_mulOf (l : Fin 2) : 1 ≤ mulOf l := by
  unfold mulOf; have : (0 : ℝ) ≤ ((l : ℕ) : ℝ) := Nat.cast_nonneg _; linarith

lemma mulOf_le_two (l : Fin 2) : mulOf l ≤ 2 := by
  unfold mulOf
  have : ((l : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Nat.le_of_lt_succ l.2
  linarith

lemma mulOf_pos (l : Fin 2) : 0 < mulOf l := lt_of_lt_of_le one_pos (one_le_mulOf l)

/-- The reward margins: `rew a + rew b ≤ 2 ab β` for all labels `a, b`
(`2β ≥ 2x`, `4β ≥ x + y`, `8β ≥ 2y`). -/
lemma rew_add_rew_le (la lb : Fin 2) :
    rew la + rew lb ≤ 2 * (mulOf la * mulOf lb) * betaC := by
  fin_cases la <;> fin_cases lb <;> norm_num [rew, mulOf, rewX, rewY, betaC]

/-! ### Matrices with real entries -/

section RealEntries

variable {τ : Type*} [Fintype τ]

/-- `‖A‖_F² = ∑ |A_ab|²`. -/
lemma frobSq_eq_sum_norm_sq_entries {𝕜 : Type*} [RCLike 𝕜] (A : Matrix τ τ 𝕜) :
    frobSq A = ∑ a, ∑ b, ‖A a b‖ ^ 2 := by
  unfold frobSq
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply, map_sum, RCLike.star_def]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- Frobenius norm of a complex matrix with real entries. -/
lemma frobSq_of_real {A : Matrix τ τ ℂ} {B : τ → τ → ℝ} (h : ∀ a b, A a b = (B a b : ℂ)) :
    frobSq A = ∑ a, ∑ b, B a b ^ 2 := by
  rw [frobSq_eq_sum_norm_sq_entries]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [h, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Trace of a complex matrix with real entries. -/
lemma rtrace_of_real {A : Matrix τ τ ℂ} {B : τ → τ → ℝ} (h : ∀ a b, A a b = (B a b : ℂ)) :
    rtrace A = ∑ a, B a a := by
  unfold rtrace Matrix.trace
  simp only [diag_apply, h, map_sum, RCLike.re_to_complex, Complex.ofReal_re]

end RealEntries

/-! ### The data of the Gram theorem -/

/-- The hypotheses on a labelled Gram matrix: positions `y`, labels `lab`, a symmetric real
matrix `κ` within `η ≤ 1/100` of the kernel values `K(y_i - y_j)`, and the weighted matrix
`G = D^{1/2} κ D^{1/2}` with `D = diag(mulOf (lab i))`. -/
structure GramData {ι : Type*} (y : ι → ℝ) (lab : ι → Fin 2) (κ : ι → ι → ℝ) (η : ℝ)
    (G : Matrix ι ι ℂ) : Prop where
  /-- the error is nonnegative -/
  eta_nonneg : 0 ≤ η
  /-- the error is at most `η₀ = 1/100` -/
  eta_le : η ≤ 1 / 100
  /-- `κ` is symmetric -/
  symm : ∀ i j, κ i j = κ j i
  /-- `κ` is close to the kernel matrix -/
  close : ∀ i j, |κ i j - K (y i - y j)| ≤ η
  /-- the entries of `G` -/
  entry : ∀ i j, G i j = ((Real.sqrt (mulOf (lab i) * mulOf (lab j)) * κ i j : ℝ) : ℂ)

namespace GramData

variable {ι : Type*} {y : ι → ℝ} {lab : ι → Fin 2} {κ : ι → ι → ℝ} {η : ℝ} {G : Matrix ι ι ℂ}

/-- The real matrix of entries of `G`. -/
def B (lab : ι → Fin 2) (κ : ι → ι → ℝ) (i j : ι) : ℝ :=
  Real.sqrt (mulOf (lab i) * mulOf (lab j)) * κ i j

lemma B_diag (lab : ι → Fin 2) (κ : ι → ι → ℝ) (i : ι) : B lab κ i i = mulOf (lab i) * κ i i := by
  unfold B; rw [Real.sqrt_mul_self (mulOf_pos _).le]

lemma B_sq (lab : ι → Fin 2) (κ : ι → ι → ℝ) (i j : ι) :
    B lab κ i j ^ 2 = mulOf (lab i) * mulOf (lab j) * κ i j ^ 2 := by
  unfold B
  rw [mul_pow, Real.sq_sqrt (mul_nonneg (mulOf_pos _).le (mulOf_pos _).le)]

lemma B_symm (D : GramData y lab κ η G) (i j : ι) : B lab κ i j = B lab κ j i := by
  unfold B; rw [D.symm i j, mul_comm (mulOf (lab i))]

/-- Diagonal entries of `κ` are within `η` of `1`. -/
lemma diag_bounds (D : GramData y lab κ η G) (i : ι) : 1 - η ≤ κ i i ∧ κ i i ≤ 1 + η := by
  have h := D.close i i
  rw [sub_self, K_zero] at h
  obtain ⟨h1, h2⟩ := abs_le.1 h
  constructor <;> linarith

/-- `m_i² κ_ii² ≥ m_i² - 8η`. -/
lemma diag_sq_ge (D : GramData y lab κ η G) (i : ι) :
    mulOf (lab i) ^ 2 - 8 * η ≤ mulOf (lab i) ^ 2 * κ i i ^ 2 := by
  obtain ⟨h1, -⟩ := D.diag_bounds i
  have hη0 := D.eta_nonneg
  have hη1 := D.eta_le
  have hκ : 1 - 2 * η ≤ κ i i ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (by linarith : 0 ≤ κ i i + (1 - η)), sq_nonneg η]
  have hm1 := one_le_mulOf (lab i)
  have hm2 := mulOf_le_two (lab i)
  have hm4 : mulOf (lab i) ^ 2 ≤ 4 := by nlinarith
  have hA := mul_le_mul_of_nonneg_left hκ (sq_nonneg (mulOf (lab i)))
  have hB := mul_le_mul_of_nonneg_right hm4 (by linarith : 0 ≤ 2 * η)
  nlinarith

/-- Off-diagonal entries: `κ_ij² ≥ K(y_i - y_j)² - 3η`. -/
lemma offdiag_sq_ge (D : GramData y lab κ η G) (i j : ι) :
    K (y i - y j) ^ 2 - 3 * η ≤ κ i j ^ 2 :=
  sq_ge_of_close (abs_K_le _) (D.close i j)

end GramData

end Distinct839.Gram
