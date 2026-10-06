/-
Simple673/Gram/Basic.lean — elementary facts used by the finite Gram theorem at clipping level 2.

* The kernel: `K 0 = 1` and the crude bound `|K| ≤ 4/3`, both directly from the definition
  (`K(t) = sinc(t) + ∑ a_j (sinc(t - j) + sinc(t + j))/2` with ten coefficients `a_j`,
  `|sinc| ≤ 1`, `∑ |a_j| = 0.210672 < 1/3`).
* The structure `GramData`, which collects the hypotheses on the Gram matrix of simple points,
  and the bounds for its entries: `κ_ii² ≥ 1 - 2η`, `κ_ij² ≥ K(y_i - y_j)² - 3η`.

There are no labels here: every point is a simple zero, every multiplicity is `1`, and the
matrix `G` is the matrix `κ` itself with complex entries. The facts that do not depend on the
window (`sincN` at the integers, `sq_ge_of_close`, trace and Frobenius norm of a complex matrix
with real entries) are those of `Distinct839/Gram/Basic.lean` and are used from there.
-/
import Simple673.Spec
import Distinct839.Gram.Basic

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Simple673.Gram

/-! ### The kernel -/

/-- `K(0) = 1`. -/
theorem K_zero : K 0 = 1 := by
  unfold K
  have h1 : ∀ j : Fin 10, sincN (0 - (((j : ℕ) : ℝ) + 1)) = 0 := fun j => by
    have h := Distinct839.Gram.sincN_int (n := -((j : ℕ) : ℤ) - 1) (by omega)
    convert h using 2
    push_cast; ring
  have h2 : ∀ j : Fin 10, sincN (0 + (((j : ℕ) : ℝ) + 1)) = 0 := fun j => by
    have h := Distinct839.Gram.sincN_int (n := ((j : ℕ) : ℤ) + 1) (by omega)
    convert h using 2
    push_cast; ring
  simp only [h1, h2, add_zero, mul_zero, Finset.sum_const_zero, Distinct839.Gram.sincN_zero]

/-- `∑ |a_j| = 0.210672`, the sum over the ten window coefficients. -/
lemma sum_abs_aC : ∑ j, |aC j| = 210672 / 1000000 := by
  have h : ∀ j, |aC j| = ((|aInt j| : ℤ) : ℝ) / 1000000 := fun j => by
    unfold aC
    rw [abs_div, Int.cast_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1000000)]
  simp_rw [h]
  rw [← Finset.sum_div, ← Int.cast_sum]
  have h2 : ∑ j, |aInt j| = 210672 := by decide
  rw [h2]; norm_num

/-- Crude bound `|K| ≤ 4/3`, from `|sinc| ≤ 1` and `∑ |a_j| < 1/3`. (The window is positive, so
in fact `|K| ≤ K(0) = 1`; this is not needed here.) -/
theorem abs_K_le (t : ℝ) : |K t| ≤ 4 / 3 := by
  unfold K
  have hterm : ∀ j : Fin 10,
      |aC j / 2 * (sincN (t - (((j : ℕ) : ℝ) + 1)) + sincN (t + (((j : ℕ) : ℝ) + 1)))|
        ≤ |aC j| := fun j => by
    have h1 := Distinct839.Gram.abs_sincN_le_one (t - (((j : ℕ) : ℝ) + 1))
    have h2 := Distinct839.Gram.abs_sincN_le_one (t + (((j : ℕ) : ℝ) + 1))
    have h3 := abs_add_le (sincN (t - (((j : ℕ) : ℝ) + 1))) (sincN (t + (((j : ℕ) : ℝ) + 1)))
    rw [abs_mul, abs_div, abs_two]
    have h4 : (0 : ℝ) ≤ |aC j| := abs_nonneg _
    have h5 : |sincN (t - (((j : ℕ) : ℝ) + 1)) + sincN (t + (((j : ℕ) : ℝ) + 1))| ≤ 2 := by
      linarith
    nlinarith [mul_nonneg h4 (sub_nonneg.2 h5)]
  calc |sincN t + ∑ j : Fin 10,
          aC j / 2 * (sincN (t - (((j : ℕ) : ℝ) + 1)) + sincN (t + (((j : ℕ) : ℝ) + 1)))|
      ≤ |sincN t| + |∑ j : Fin 10,
          aC j / 2 * (sincN (t - (((j : ℕ) : ℝ) + 1)) + sincN (t + (((j : ℕ) : ℝ) + 1)))| :=
        abs_add_le _ _
    _ ≤ 1 + ∑ j : Fin 10, |aC j| :=
        add_le_add (Distinct839.Gram.abs_sincN_le_one t)
          ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hterm j))
    _ ≤ 4 / 3 := by rw [sum_abs_aC]; norm_num

/-! ### The data of the Gram theorem -/

/-- The hypotheses on a Gram matrix of simple points: positions `y`, a symmetric real matrix
`κ` within `η ≤ 1/100` of the kernel values `K(y_i - y_j)`, and the same matrix `G` with
complex entries. -/
structure GramData {ι : Type*} (y : ι → ℝ) (κ : ι → ι → ℝ) (η : ℝ) (G : Matrix ι ι ℂ) :
    Prop where
  /-- the error is nonnegative -/
  eta_nonneg : 0 ≤ η
  /-- the error is at most `η₀ = 1/100` -/
  eta_le : η ≤ 1 / 100
  /-- `κ` is symmetric -/
  symm : ∀ i j, κ i j = κ j i
  /-- `κ` is close to the kernel matrix -/
  close : ∀ i j, |κ i j - K (y i - y j)| ≤ η
  /-- the entries of `G` -/
  entry : ∀ i j, G i j = ((κ i j : ℝ) : ℂ)

namespace GramData

variable {ι : Type*} {y : ι → ℝ} {κ : ι → ι → ℝ} {η : ℝ} {G : Matrix ι ι ℂ}

/-- Diagonal entries of `κ` are within `η` of `1`. -/
lemma diag_bounds (D : GramData y κ η G) (i : ι) : 1 - η ≤ κ i i ∧ κ i i ≤ 1 + η := by
  have h := D.close i i
  rw [sub_self, K_zero] at h
  obtain ⟨h1, h2⟩ := abs_le.1 h
  constructor <;> linarith

/-- `κ_ii² ≥ 1 - 2η`. -/
lemma diag_sq_ge (D : GramData y κ η G) (i : ι) : 1 - 2 * η ≤ κ i i ^ 2 := by
  obtain ⟨h1, -⟩ := D.diag_bounds i
  have hη0 := D.eta_nonneg
  have hη1 := D.eta_le
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (by linarith : 0 ≤ κ i i + (1 - η)), sq_nonneg η]

/-- Off-diagonal entries: `κ_ij² ≥ K(y_i - y_j)² - 3η`. -/
lemma offdiag_sq_ge (D : GramData y κ η G) (i j : ι) :
    K (y i - y j) ^ 2 - 3 * η ≤ κ i j ^ 2 :=
  Distinct839.Gram.sq_ge_of_close (abs_K_le _) (D.close i j)

end GramData

end Simple673.Gram
