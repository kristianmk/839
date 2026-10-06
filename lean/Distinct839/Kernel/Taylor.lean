/-
Distinct839/Kernel/Taylor.lean — alternating Taylor enclosures of `sin` and `cos`.

`sinPoly n x = ∑_{k<n} (-1)^k x^(2k+1)/(2k+1)!` and `cosPoly n x = ∑_{k<n} (-1)^k x^(2k)/(2k)!` are
the partial sums of the sine and cosine series, defined over any field so that the same definition
is evaluated in `ℚ` by the kernel table and compared with `Real.sin`, `Real.cos` in `ℝ`.

For `x ≥ 0` and `n ≥ 1` the errors alternate in sign (`taylor_sign`):
   `sinPoly n x ≤ sin x`, `cosPoly n x ≤ cos x`   for even `n ≥ 2`,
   `sin x ≤ sinPoly n x`, `cos x ≤ cosPoly n x`   for odd `n`.
The proof is the usual chain of integrations starting from `cos x ≤ 1`.
-/
import Distinct839.Defs

open scoped BigOperators

namespace Distinct839.Kernel

/-! ## The partial sums -/

section Poly

variable {F : Type*} [Field F]

/-- Partial sum of the sine series with `n` terms: `∑_{k<n} (-1)^k x^(2k+1)/(2k+1)!`. -/
def sinPoly (n : ℕ) (x : F) : F :=
  ∑ k ∈ Finset.range n, (-1) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : F)

/-- Partial sum of the cosine series with `n` terms: `∑_{k<n} (-1)^k x^(2k)/(2k)!`. -/
def cosPoly (n : ℕ) (x : F) : F :=
  ∑ k ∈ Finset.range n, (-1) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : F)

lemma sinPoly_succ (n : ℕ) (x : F) :
    sinPoly (n + 1) x
      = sinPoly n x + (-1) ^ n * x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : F) :=
  Finset.sum_range_succ _ _

lemma cosPoly_succ (n : ℕ) (x : F) :
    cosPoly (n + 1) x = cosPoly n x + (-1) ^ n * x ^ (2 * n) / (Nat.factorial (2 * n) : F) :=
  Finset.sum_range_succ _ _

lemma sinPoly_zero_right (n : ℕ) : sinPoly n (0 : F) = 0 :=
  Finset.sum_eq_zero fun k _ => by rw [zero_pow (Nat.succ_ne_zero _), mul_zero, zero_div]

lemma cosPoly_succ_zero_right (n : ℕ) : cosPoly (n + 1) (0 : F) = 1 := by
  induction n with
  | zero => simp [cosPoly]
  | succ n ih =>
    rw [cosPoly_succ, ih, zero_pow (by omega), mul_zero, zero_div, add_zero]

end Poly

/-- The rational partial sums cast to the real ones. -/
lemma sinPoly_cast (n : ℕ) (x : ℚ) : ((sinPoly n x : ℚ) : ℝ) = sinPoly n (x : ℝ) := by
  simp [sinPoly]

lemma cosPoly_cast (n : ℕ) (x : ℚ) : ((cosPoly n x : ℚ) : ℝ) = cosPoly n (x : ℝ) := by
  simp [cosPoly]

/-! ## Derivatives of the partial sums -/

lemma hasDerivAt_pow_div_factorial (c : ℝ) (m : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => c * y ^ (m + 1) / (Nat.factorial (m + 1) : ℝ))
      (c * x ^ m / (Nat.factorial m : ℝ)) x := by
  have h := ((hasDerivAt_pow (m + 1) x).const_mul c).div_const (Nat.factorial (m + 1) : ℝ)
  have hm : ((m + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
  have e : c * x ^ m / (Nat.factorial m : ℝ)
      = c * (((m + 1 : ℕ) : ℝ) * x ^ (m + 1 - 1)) / (Nat.factorial (m + 1) : ℝ) := by
    rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul,
      show c * (((m + 1 : ℕ) : ℝ) * x ^ m) = ((m + 1 : ℕ) : ℝ) * (c * x ^ m) by ring,
      mul_div_mul_left _ _ hm]
  rw [e]
  exact h

/-- `d/dx sinPoly n x = cosPoly n x`. -/
theorem hasDerivAt_sinPoly (n : ℕ) (x : ℝ) :
    HasDerivAt (sinPoly n : ℝ → ℝ) (cosPoly n x) x := by
  induction n with
  | zero =>
    have e : (sinPoly 0 : ℝ → ℝ) = fun _ => 0 := by
      funext y
      simp [sinPoly]
    have e' : cosPoly 0 x = 0 := by simp [cosPoly]
    rw [e, e']
    exact hasDerivAt_const x 0
  | succ n ih =>
    have e : (sinPoly (n + 1) : ℝ → ℝ) = fun y =>
        sinPoly n y + (-1) ^ n * y ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ) := by
      funext y
      exact sinPoly_succ n y
    rw [e, cosPoly_succ]
    exact ih.fun_add (hasDerivAt_pow_div_factorial ((-1) ^ n) (2 * n) x)

/-- `d/dx cosPoly (n+1) x = -sinPoly n x`. -/
theorem hasDerivAt_cosPoly_succ (n : ℕ) (x : ℝ) :
    HasDerivAt (cosPoly (n + 1) : ℝ → ℝ) (-sinPoly n x) x := by
  induction n with
  | zero =>
    have e : (cosPoly (0 + 1) : ℝ → ℝ) = fun _ => 1 := by
      funext y
      simp [cosPoly]
    have e' : -sinPoly 0 x = 0 := by simp [sinPoly]
    rw [e, e']
    exact hasDerivAt_const x 1
  | succ n ih =>
    have e : (cosPoly (n + 1 + 1) : ℝ → ℝ) = fun y =>
        cosPoly (n + 1) y
          + (-(-1) ^ n) * y ^ (2 * n + 1 + 1) / (Nat.factorial (2 * n + 1 + 1) : ℝ) := by
      funext y
      rw [cosPoly_succ, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, pow_succ (-1 : ℝ) n]
      ring
    have e' : -sinPoly (n + 1) x
        = -sinPoly n x + (-(-1) ^ n) * x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ) := by
      rw [sinPoly_succ]
      ring
    rw [e, e']
    exact ih.fun_add (hasDerivAt_pow_div_factorial (-(-1) ^ n) (2 * n + 1) x)

/-! ## The alternating enclosures -/

/-- A function vanishing at `0` with nonnegative derivative on `[0, ∞)` is nonnegative there. -/
lemma nonneg_of_deriv_nonneg {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (h0 : f 0 = 0)
    (h' : ∀ x, 0 ≤ x → 0 ≤ f' x) : ∀ x, 0 ≤ x → 0 ≤ f x := by
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt).continuousOn
    · exact fun x _ => (hf x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hf x).deriv]
      exact h' x (Set.mem_Ioi.mp hx).le
  intro x hx
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  rwa [h0] at h

/-- From the cosine enclosure of order `n` to the sine enclosure of order `n`. -/
lemma sin_sign_of_cos_sign (n : ℕ)
    (hc : ∀ x : ℝ, 0 ≤ x → 0 ≤ (-1) ^ n * (Real.cos x - cosPoly n x)) :
    ∀ x : ℝ, 0 ≤ x → 0 ≤ (-1) ^ n * (Real.sin x - sinPoly n x) := by
  refine nonneg_of_deriv_nonneg (f := fun x => (-1) ^ n * (Real.sin x - sinPoly n x))
    (f' := fun x => (-1) ^ n * (Real.cos x - cosPoly n x)) ?_ ?_ hc
  · intro x
    exact ((Real.hasDerivAt_sin x).fun_sub (hasDerivAt_sinPoly n x)).const_mul _
  · show (-1 : ℝ) ^ n * (Real.sin 0 - sinPoly n 0) = 0
    rw [Real.sin_zero, sinPoly_zero_right, sub_zero, mul_zero]

/-- From the sine enclosure of order `n` to the cosine enclosure of order `n + 1`. -/
lemma cos_sign_of_sin_sign (n : ℕ)
    (hs : ∀ x : ℝ, 0 ≤ x → 0 ≤ (-1) ^ n * (Real.sin x - sinPoly n x)) :
    ∀ x : ℝ, 0 ≤ x → 0 ≤ (-1) ^ (n + 1) * (Real.cos x - cosPoly (n + 1) x) := by
  refine nonneg_of_deriv_nonneg (f := fun x => (-1) ^ (n + 1) * (Real.cos x - cosPoly (n + 1) x))
    (f' := fun x => (-1) ^ (n + 1) * (-Real.sin x - -sinPoly n x)) ?_ ?_ ?_
  · intro x
    exact ((Real.hasDerivAt_cos x).fun_sub (hasDerivAt_cosPoly_succ n x)).const_mul _
  · show (-1 : ℝ) ^ (n + 1) * (Real.cos 0 - cosPoly (n + 1) 0) = 0
    rw [Real.cos_zero, cosPoly_succ_zero_right, sub_self, mul_zero]
  · intro x hx
    have e : (-1 : ℝ) ^ (n + 1) * (-Real.sin x - -sinPoly n x)
        = (-1) ^ n * (Real.sin x - sinPoly n x) := by
      rw [pow_succ]
      ring
    show 0 ≤ (-1 : ℝ) ^ (n + 1) * (-Real.sin x - -sinPoly n x)
    rw [e]
    exact hs x hx

/-- Alternating Taylor enclosures: for `x ≥ 0` and `n ≥ 1` terms, the errors of the partial sums of
the cosine and sine series have the sign `(-1)^n`. -/
theorem taylor_sign (n : ℕ) : ∀ x : ℝ, 0 ≤ x →
    0 ≤ (-1) ^ (n + 1) * (Real.cos x - cosPoly (n + 1) x) ∧
    0 ≤ (-1) ^ (n + 1) * (Real.sin x - sinPoly (n + 1) x) := by
  have key : (∀ x : ℝ, 0 ≤ x → 0 ≤ (-1) ^ (n + 1) * (Real.cos x - cosPoly (n + 1) x)) := by
    induction n with
    | zero =>
      intro x _
      have e : cosPoly (0 + 1) x = 1 := by simp [cosPoly]
      have h1 := Real.cos_le_one x
      rw [e, zero_add, pow_one]
      linarith
    | succ n ih => exact cos_sign_of_sin_sign (n + 1) (sin_sign_of_cos_sign (n + 1) ih)
  exact fun x hx => ⟨key x hx, sin_sign_of_cos_sign (n + 1) key x hx⟩

/-- `sinPoly n x ≤ sin x` for `x ≥ 0` and an even number `n ≥ 2` of terms. -/
theorem sinPoly_le_sin {n : ℕ} (hn : Even n) (hn0 : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    sinPoly n x ≤ Real.sin x := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hm
  have h := (taylor_sign m x hx).2
  rw [hn.neg_one_pow, one_mul] at h
  linarith

/-- `sin x ≤ sinPoly n x` for `x ≥ 0` and an odd number `n` of terms. -/
theorem sin_le_sinPoly {n : ℕ} (hn : Odd n) {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ sinPoly n x := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hn.pos; omega⟩
  subst hm
  have h := (taylor_sign m x hx).2
  rw [hn.neg_one_pow] at h
  linarith

/-- `cosPoly n x ≤ cos x` for `x ≥ 0` and an even number `n ≥ 2` of terms. -/
theorem cosPoly_le_cos {n : ℕ} (hn : Even n) (hn0 : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    cosPoly n x ≤ Real.cos x := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hm
  have h := (taylor_sign m x hx).1
  rw [hn.neg_one_pow, one_mul] at h
  linarith

/-- `cos x ≤ cosPoly n x` for `x ≥ 0` and an odd number `n` of terms. -/
theorem cos_le_cosPoly {n : ℕ} (hn : Odd n) {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ cosPoly n x := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hn.pos; omega⟩
  subst hm
  have h := (taylor_sign m x hx).1
  rw [hn.neg_one_pow] at h
  linarith

end Distinct839.Kernel
