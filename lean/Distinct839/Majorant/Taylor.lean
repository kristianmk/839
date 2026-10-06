/-
Distinct839/Majorant/Taylor.lean — Taylor enclosures for `cos`, `sin` and `sinc`.

The partial sums of the cosine, sine and sinc series are defined over an arbitrary field, so that
the same definition can be evaluated on rational numbers by the kernel and compared with the real
functions. The alternating partial sums enclose the functions:

* `cosPoly x (2n+2) ≤ cos x ≤ cosPoly x (2n+1)` for every real `x`,
* `sinPoly x (2n+2) ≤ sin x ≤ sinPoly x (2n+1)` for `x ≥ 0`,
* `sincPoly x (2n+2) ≤ sinc x` for every real `x`.

The proof is the classical one: each difference vanishes at `0` and its derivative is the
previous difference. The file also contains the Lipschitz bound `|sinc a - sinc b| ≤ |a - b|/2`.

All auxiliary declarations of the majorant layer live in the namespace `Distinct839.Majorant`.
-/
import Distinct839.Defs

open Real MeasureTheory

namespace Distinct839.Majorant

/-! ## Partial sums -/

/-- Partial sum `∑_{k<n} (-1)^k x^{2k}/(2k)!` of the cosine series. -/
def cosPoly {F : Type*} [Field F] (x : F) : ℕ → F
  | 0 => 0
  | n + 1 => cosPoly x n + (-1) ^ n * x ^ (2 * n) / ((2 * n).factorial : F)

/-- Partial sum `∑_{k<n} (-1)^k x^{2k+1}/(2k+1)!` of the sine series. -/
def sinPoly {F : Type*} [Field F] (x : F) : ℕ → F
  | 0 => 0
  | n + 1 => sinPoly x n + (-1) ^ n * x ^ (2 * n + 1) / ((2 * n + 1).factorial : F)

/-- Partial sum `∑_{k<n} (-1)^k x^{2k}/(2k+1)!` of the series of `sin x / x`. -/
def sincPoly {F : Type*} [Field F] (x : F) : ℕ → F
  | 0 => 0
  | n + 1 => sincPoly x n + (-1) ^ n * x ^ (2 * n) / ((2 * n + 1).factorial : F)

section Field

variable {F : Type*} [Field F]

lemma cosPoly_succ (x : F) (n : ℕ) :
    cosPoly x (n + 1) = cosPoly x n + (-1) ^ n * x ^ (2 * n) / ((2 * n).factorial : F) := rfl

lemma sinPoly_succ (x : F) (n : ℕ) :
    sinPoly x (n + 1) = sinPoly x n + (-1) ^ n * x ^ (2 * n + 1) / ((2 * n + 1).factorial : F) :=
  rfl

lemma sincPoly_succ (x : F) (n : ℕ) :
    sincPoly x (n + 1) = sincPoly x n + (-1) ^ n * x ^ (2 * n) / ((2 * n + 1).factorial : F) :=
  rfl

@[simp] lemma cosPoly_zero (x : F) : cosPoly x 0 = 0 := rfl
@[simp] lemma sinPoly_zero (x : F) : sinPoly x 0 = 0 := rfl
@[simp] lemma sincPoly_zero (x : F) : sincPoly x 0 = 0 := rfl

/-- `sinPoly x n = x * sincPoly x n`. -/
lemma sinPoly_eq_mul_sincPoly (x : F) (n : ℕ) : sinPoly x n = x * sincPoly x n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sinPoly_succ, sincPoly_succ, ih, pow_succ]; ring

end Field

/-- The rational partial sums cast to the real partial sums. -/
lemma cast_cosPoly (q : ℚ) (n : ℕ) : ((cosPoly q n : ℚ) : ℝ) = cosPoly (q : ℝ) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [cosPoly_succ, cosPoly_succ, ← ih]; push_cast; rfl

/-- The rational partial sums cast to the real partial sums. -/
lemma cast_sincPoly (q : ℚ) (n : ℕ) : ((sincPoly q n : ℚ) : ℝ) = sincPoly (q : ℝ) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sincPoly_succ, sincPoly_succ, ← ih]; push_cast; rfl

/-! ## Values at zero and parity -/

lemma sinPoly_at_zero (n : ℕ) : sinPoly (0 : ℝ) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sinPoly_succ, ih]; simp

lemma cosPoly_at_zero (n : ℕ) : cosPoly (0 : ℝ) (n + 1) = 1 := by
  induction n with
  | zero => simp [cosPoly_succ]
  | succ n ih => rw [cosPoly_succ, ih]; simp

lemma sincPoly_at_zero (n : ℕ) : sincPoly (0 : ℝ) (n + 1) = 1 := by
  induction n with
  | zero => simp [sincPoly_succ]
  | succ n ih => rw [sincPoly_succ, ih]; simp

lemma cosPoly_abs (x : ℝ) (n : ℕ) : cosPoly |x| n = cosPoly x n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cosPoly_succ, cosPoly_succ, ih, pow_mul, sq_abs, ← pow_mul]

lemma sincPoly_abs (x : ℝ) (n : ℕ) : sincPoly |x| n = sincPoly x n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sincPoly_succ, sincPoly_succ, ih, pow_mul, sq_abs, ← pow_mul]

/-! ## Derivatives -/

lemma hasDerivAt_sinPoly (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => sinPoly y n) (cosPoly x n) x := by
  induction n with
  | zero => exact hasDerivAt_const x (0 : ℝ)
  | succ n ih =>
    have h : HasDerivAt (fun y : ℝ => (-1) ^ n * y ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ))
        ((-1) ^ n * (((2 * n + 1 : ℕ) : ℝ) * x ^ (2 * n + 1 - 1)) / ((2 * n + 1).factorial : ℝ)) x :=
      ((hasDerivAt_pow (2 * n + 1) x).const_mul ((-1 : ℝ) ^ n)).div_const _
    have h1 : HasDerivAt (fun y : ℝ => (-1) ^ n * y ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ))
        ((-1) ^ n * x ^ (2 * n) / ((2 * n).factorial : ℝ)) x := by
      refine h.congr_deriv ?_
      have hc : ((2 * n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
      rw [Nat.factorial_succ, Nat.add_sub_cancel, Nat.cast_mul, mul_left_comm,
        mul_div_mul_left _ _ hc]
    exact ih.add h1

lemma hasDerivAt_cosPoly (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => cosPoly y (n + 1)) (-sinPoly x n) x := by
  induction n with
  | zero =>
    have h : (fun y : ℝ => cosPoly y (0 + 1)) = fun _ => (1 : ℝ) := by
      funext y; simp [cosPoly_succ]
    rw [h]
    simpa using hasDerivAt_const x (1 : ℝ)
  | succ n ih =>
    have h : HasDerivAt
        (fun y : ℝ => (-1) ^ (n + 1) * y ^ (2 * n + 1 + 1) / ((2 * n + 1 + 1).factorial : ℝ))
        ((-1) ^ (n + 1) * (((2 * n + 1 + 1 : ℕ) : ℝ) * x ^ (2 * n + 1 + 1 - 1))
          / ((2 * n + 1 + 1).factorial : ℝ)) x :=
      ((hasDerivAt_pow (2 * n + 1 + 1) x).const_mul ((-1 : ℝ) ^ (n + 1))).div_const _
    have h1 : HasDerivAt
        (fun y : ℝ => (-1) ^ (n + 1) * y ^ (2 * n + 1 + 1) / ((2 * n + 1 + 1).factorial : ℝ))
        (-((-1) ^ n * x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ))) x := by
      refine h.congr_deriv ?_
      have hc : ((2 * n + 1 + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
      rw [Nat.factorial_succ (2 * n + 1), Nat.add_sub_cancel, Nat.cast_mul, mul_left_comm,
        mul_div_mul_left _ _ hc, pow_succ ((-1 : ℝ)) n]
      ring
    have h2 := ih.add h1
    rw [← neg_add] at h2
    exact h2

/-! ## The alternating enclosures -/

/-- A differentiable function vanishing at `0` with nonnegative derivative on `[0, ∞)` is
nonnegative on `[0, ∞)`. -/
private lemma nonneg_of_hasDerivAt {f f' : ℝ → ℝ} (h0 : f 0 = 0)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hpos : ∀ x, 0 ≤ x → 0 ≤ f' x) :
    ∀ x, 0 ≤ x → 0 ≤ f x := by
  intro x hx
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.mpr fun y => (hd y).continuousAt).continuousOn
    · exact fun y _ => (hd y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hd y).deriv]
      exact hpos y (le_of_lt hy)
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  rw [h0] at h
  exact h

/-- The signs of the Taylor remainders of `cos` and `sin` on `[0, ∞)`: with `m + 1` terms the
partial sum minus the function has the sign `(-1)^m`. -/
theorem taylor_sign (m : ℕ) :
    (∀ x : ℝ, 0 ≤ x → 0 ≤ (-1 : ℝ) ^ m * (cosPoly x (m + 1) - cos x)) ∧
    (∀ x : ℝ, 0 ≤ x → 0 ≤ (-1 : ℝ) ^ m * (sinPoly x (m + 1) - sin x)) := by
  -- the sine statement follows from the cosine statement of the same order
  have step : ∀ m : ℕ, (∀ x : ℝ, 0 ≤ x → 0 ≤ (-1 : ℝ) ^ m * (cosPoly x (m + 1) - cos x)) →
      ∀ x : ℝ, 0 ≤ x → 0 ≤ (-1 : ℝ) ^ m * (sinPoly x (m + 1) - sin x) := by
    intro m hc
    refine nonneg_of_hasDerivAt (f := fun y => (-1 : ℝ) ^ m * (sinPoly y (m + 1) - sin y))
      (f' := fun y => (-1 : ℝ) ^ m * (cosPoly y (m + 1) - cos y)) ?_ ?_ hc
    · simp [sinPoly_at_zero]
    · intro y
      have h : HasDerivAt (fun z : ℝ => (-1 : ℝ) ^ m * (sinPoly z (m + 1) - sin z))
          ((-1 : ℝ) ^ m * (cosPoly y (m + 1) - cos y)) y :=
        ((hasDerivAt_sinPoly (m + 1) y).sub (hasDerivAt_sin y)).const_mul _
      exact h
  induction m with
  | zero =>
    have hc : ∀ x : ℝ, 0 ≤ x → 0 ≤ (-1 : ℝ) ^ 0 * (cosPoly x (0 + 1) - cos x) := by
      intro x _
      have h1 : cosPoly x (0 + 1) = 1 := by rw [cosPoly_succ, cosPoly_zero]; simp
      rw [h1, pow_zero, one_mul]
      linarith [cos_le_one x]
    exact ⟨hc, step 0 hc⟩
  | succ m ih =>
    have hc : ∀ x : ℝ, 0 ≤ x → 0 ≤ (-1 : ℝ) ^ (m + 1) * (cosPoly x (m + 1 + 1) - cos x) := by
      refine nonneg_of_hasDerivAt
        (f := fun y => (-1 : ℝ) ^ (m + 1) * (cosPoly y (m + 1 + 1) - cos y))
        (f' := fun y => (-1 : ℝ) ^ m * (sinPoly y (m + 1) - sin y)) ?_ ?_ ih.2
      · simp [cosPoly_at_zero]
      · intro y
        have h : HasDerivAt (fun z : ℝ => (-1 : ℝ) ^ (m + 1) * (cosPoly z (m + 1 + 1) - cos z))
            ((-1 : ℝ) ^ (m + 1) * (-sinPoly y (m + 1) - -sin y)) y :=
          ((hasDerivAt_cosPoly (m + 1) y).sub (hasDerivAt_cos y)).const_mul _
        refine h.congr_deriv ?_
        rw [pow_succ]
        ring
    exact ⟨hc, step (m + 1) hc⟩

/-- Upper Taylor bound for `cos`, valid for every real `x`. -/
theorem cos_le_cosPoly (x : ℝ) (n : ℕ) : cos x ≤ cosPoly x (2 * n + 1) := by
  have h := (taylor_sign (2 * n)).1 |x| (abs_nonneg x)
  rw [Even.neg_one_pow (even_two_mul n), one_mul, cosPoly_abs, cos_abs] at h
  linarith

/-- Lower Taylor bound for `cos`, valid for every real `x`. -/
theorem cosPoly_le_cos (x : ℝ) (n : ℕ) : cosPoly x (2 * n + 2) ≤ cos x := by
  have h : 0 ≤ (-1 : ℝ) ^ (2 * n + 1) * (cosPoly |x| (2 * n + 2) - cos |x|) :=
    (taylor_sign (2 * n + 1)).1 |x| (abs_nonneg x)
  rw [Odd.neg_one_pow (odd_two_mul_add_one n), cosPoly_abs, cos_abs] at h
  linarith

/-- Upper Taylor bound for `sin` on `[0, ∞)`. -/
theorem sin_le_sinPoly {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : sin x ≤ sinPoly x (2 * n + 1) := by
  have h := (taylor_sign (2 * n)).2 x hx
  rw [Even.neg_one_pow (even_two_mul n), one_mul] at h
  linarith

/-- Lower Taylor bound for `sin` on `[0, ∞)`. -/
theorem sinPoly_le_sin {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : sinPoly x (2 * n + 2) ≤ sin x := by
  have h : 0 ≤ (-1 : ℝ) ^ (2 * n + 1) * (sinPoly x (2 * n + 2) - sin x) :=
    (taylor_sign (2 * n + 1)).2 x hx
  rw [Odd.neg_one_pow (odd_two_mul_add_one n)] at h
  linarith

lemma sinc_abs (x : ℝ) : sinc |x| = sinc x := by
  rcases abs_choice x with h | h <;> rw [h]
  exact sinc_neg x

/-- Lower Taylor bound for `sinc`, valid for every real `x`. -/
theorem sincPoly_le_sinc (x : ℝ) (n : ℕ) : sincPoly x (2 * n + 2) ≤ sinc x := by
  rw [← sincPoly_abs, ← sinc_abs]
  rcases eq_or_lt_of_le (abs_nonneg x) with h0 | hpos
  · rw [← h0, sinc_zero]
    exact le_of_eq (sincPoly_at_zero (2 * n + 1))
  · rw [sinc_of_ne_zero (ne_of_gt hpos), le_div_iff₀ hpos,
      mul_comm (sincPoly |x| (2 * n + 2)) |x|, ← sinPoly_eq_mul_sincPoly]
    exact sinPoly_le_sin (le_of_lt hpos) n

/-! ## Lipschitz bound for `sinc` -/

/-- `sinc x = ∫₀¹ cos (t x) dt`. -/
lemma sinc_eq_integral (x : ℝ) : sinc x = ∫ t in (0 : ℝ)..1, cos (t * x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [sinc_of_ne_zero hx, intervalIntegral.integral_comp_mul_right (f := cos) hx, integral_cos]
    simp [div_eq_inv_mul]

/-- `sinc` is Lipschitz with constant `1/2`. -/
theorem abs_sinc_sub_sinc_le (a b : ℝ) : |sinc a - sinc b| ≤ |a - b| / 2 := by
  have hint : ∀ c : ℝ, IntervalIntegrable (fun t : ℝ => cos (t * c)) volume 0 1 :=
    fun c => (by fun_prop : Continuous fun t : ℝ => cos (t * c)).intervalIntegrable _ _
  rw [sinc_eq_integral a, sinc_eq_integral b, ← intervalIntegral.integral_sub (hint a) (hint b)]
  calc |∫ t in (0 : ℝ)..1, (cos (t * a) - cos (t * b))|
      ≤ ∫ t in (0 : ℝ)..1, |cos (t * a) - cos (t * b)| :=
        intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, t * |a - b| := by
        apply intervalIntegral.integral_mono_on zero_le_one
        · exact (by fun_prop : Continuous fun t : ℝ => cos (t * a) - cos (t * b)).abs.intervalIntegrable
            _ _
        · exact (by fun_prop : Continuous fun t : ℝ => t * |a - b|).intervalIntegrable _ _
        · intro t ht
          calc |cos (t * a) - cos (t * b)| ≤ |t * a - t * b| := abs_cos_sub_cos_le _ _
            _ = t * |a - b| := by rw [← mul_sub, abs_mul, abs_of_nonneg ht.1]
    _ = |a - b| / 2 := by
        rw [intervalIntegral.integral_mul_const, integral_id]
        ring

end Distinct839.Majorant
