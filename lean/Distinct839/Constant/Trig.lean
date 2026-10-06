/-
Distinct839/Constant/Trig.lean — elementary integrals of cosine waves of integer frequency.

These are the integrals needed for the second-moment constant of a cosine-polynomial window:

* `integral_wave`: `∫_{-1/2}^{1/2-r} cos(2π m s + 2π k r) ds` in closed form (`waveInt m k r`);
* `integral_mul_sin`, `integral_mul_one_sub_mul_cos`: `∫₀¹ r sin(2πnr) dr` and
  `∫₀¹ r (1 - r) cos(2πnr) dr`;
* `integral_cos_mul_cos_shift`: the autocorrelation integrand `cos(2πjs) cos(2πk(s + r))`;
* `integral_mul_waveInt`: `∫₀¹ r · waveInt m k r dr` in closed form (`outerW m k`).

All frequencies are integers, so the boundary values reduce through `sin(x + nπ) = (-1)ⁿ sin x`.
-/
import Mathlib

open Real intervalIntegral

noncomputable section

namespace Distinct839.Constant

/-- Product to sum: `cos x cos y = (cos (x + y) + cos (x - y)) / 2`. -/
lemma cos_mul_cos_eq (x y : ℝ) : cos x * cos y = (cos (x + y) + cos (x - y)) / 2 := by
  rw [cos_add, cos_sub]; ring

lemma sin_two_pi_int (n : ℤ) : sin (2 * π * n) = 0 := by
  have h := sin_int_mul_pi (2 * n)
  rw [← h]; congr 1; push_cast; ring

lemma cos_two_pi_int (n : ℤ) : cos (2 * π * n) = 1 := by
  have h := cos_int_mul_two_pi n
  rw [← h]; congr 1; ring

/-! ### The inner integral -/

/-- Closed form of `∫_{-1/2}^{1/2-r} cos(2π m s + 2π k r) ds`. -/
def waveInt (m k : ℤ) (r : ℝ) : ℝ :=
  if m = 0 then (1 - r) * cos (2 * π * k * r)
  else (-1) ^ m * (sin (2 * π * ((k - m : ℤ) : ℝ) * r) - sin (2 * π * k * r)) / (2 * π * m)

lemma continuous_waveInt (m k : ℤ) : Continuous (waveInt m k) := by
  unfold waveInt
  split_ifs <;> fun_prop

/-- **Inner integral.** `∫_{-1/2}^{1/2-r} cos(2π m s + 2π k r) ds = waveInt m k r`. -/
lemma integral_wave (m k : ℤ) (r : ℝ) :
    ∫ s in (-(1:ℝ)/2)..(1/2 - r), cos (2 * π * m * s + 2 * π * k * r) = waveInt m k r := by
  unfold waveInt
  split_ifs with hm
  · subst hm
    simp only [Int.cast_zero, mul_zero, zero_mul, zero_add, integral_const, smul_eq_mul]
    ring
  · have hm' : (m : ℝ) ≠ 0 := Int.cast_ne_zero.2 hm
    have hc : (2 * π * m : ℝ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hm'
    have h := intervalIntegral.integral_comp_mul_add (a := -(1:ℝ)/2) (b := 1/2 - r) cos hc
      (2 * π * k * r)
    rw [h, integral_cos, smul_eq_mul]
    have h1 : 2 * π * m * (1 / 2 - r) + 2 * π * k * r
        = 2 * π * ((k - m : ℤ) : ℝ) * r + m * π := by push_cast; ring
    have h2 : 2 * π * m * (-(1:ℝ) / 2) + 2 * π * k * r = 2 * π * k * r - m * π := by ring
    rw [h1, h2, sin_add_int_mul_pi, sin_sub_int_mul_pi]
    field_simp

/-! ### The outer integrals -/

/-- `∫₀¹ r sin(2πnr) dr`. -/
def sigmaW (n : ℤ) : ℝ := if n = 0 then 0 else -1 / (2 * π * n)

/-- `∫₀¹ r (1 - r) cos(2πnr) dr`. -/
def rhoW (n : ℤ) : ℝ := if n = 0 then 1 / 6 else -1 / (2 * π ^ 2 * n ^ 2)

/-- `ω r ↦ ω r` has derivative `ω`. -/
lemma hasDerivAt_mul_left (ω x : ℝ) : HasDerivAt (fun r => ω * r) ω x := by
  simpa using (hasDerivAt_id' x).const_mul ω

lemma integral_mul_sin (n : ℤ) : ∫ r in (0:ℝ)..1, r * sin (2 * π * n * r) = sigmaW n := by
  unfold sigmaW
  split_ifs with hn
  · subst hn; simp
  · have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.2 hn
    set ω : ℝ := 2 * π * n with hω
    have hω0 : ω ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hn'
    have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1,
        HasDerivAt (fun r => -r * cos (ω * r) / ω + sin (ω * r) / ω ^ 2) (x * sin (ω * x)) x := by
      intro x _
      have h1 := hasDerivAt_mul_left ω x
      have h0 : HasDerivAt (fun r : ℝ => -r) (-1) x := (hasDerivAt_id' x).neg
      have h4 : HasDerivAt (fun r => -r * cos (ω * r) / ω)
          ((-1 * cos (ω * x) + -x * (-sin (ω * x) * ω)) / ω) x := (h0.mul h1.cos).div_const ω
      have h5 : HasDerivAt (fun r => sin (ω * r) / ω ^ 2) (cos (ω * x) * ω / ω ^ 2) x :=
        h1.sin.div_const (ω ^ 2)
      refine (h4.add h5).congr_deriv ?_
      field_simp
      ring
    rw [integral_eq_sub_of_hasDerivAt hd
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    have hc : cos ω = 1 := cos_two_pi_int n
    have hs : sin ω = 0 := sin_two_pi_int n
    simp only [mul_one, mul_zero, hc, hs, cos_zero, sin_zero, neg_zero, zero_div, add_zero]
    field_simp
    ring

lemma integral_mul_one_sub_mul_cos (n : ℤ) :
    ∫ r in (0:ℝ)..1, r * ((1 - r) * cos (2 * π * n * r)) = rhoW n := by
  unfold rhoW
  split_ifs with hn
  · subst hn
    have e : ∀ r : ℝ, r * ((1 - r) * cos (2 * π * ((0 : ℤ) : ℝ) * r)) = r - r ^ 2 := fun r => by
      simp only [Int.cast_zero, mul_zero, zero_mul, cos_zero]; ring
    simp_rw [e]
    have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun r : ℝ => r ^ 2 / 2 - r ^ 3 / 3) (x - x ^ 2) x := by
      intro x _
      have h2 : HasDerivAt (fun r : ℝ => r ^ 2 / 2) (2 * x / 2) x := by
        simpa using (hasDerivAt_pow 2 x).div_const 2
      have h3 : HasDerivAt (fun r : ℝ => r ^ 3 / 3) (3 * x ^ 2 / 3) x := by
        simpa using (hasDerivAt_pow 3 x).div_const 3
      refine (h2.sub h3).congr_deriv ?_
      ring
    rw [integral_eq_sub_of_hasDerivAt hd (Continuous.intervalIntegrable (by fun_prop) _ _)]
    norm_num
  · have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.2 hn
    set ω : ℝ := 2 * π * n with hω
    have hω0 : ω ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hn'
    have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1,
        HasDerivAt (fun r => (r - r ^ 2) * sin (ω * r) / ω + (1 - 2 * r) * cos (ω * r) / ω ^ 2
            + 2 * sin (ω * r) / ω ^ 3) (x * ((1 - x) * cos (ω * x))) x := by
      intro x _
      have h1 := hasDerivAt_mul_left ω x
      have hp : HasDerivAt (fun r : ℝ => r - r ^ 2) (1 - 2 * x) x := by
        have h2 : HasDerivAt (fun r : ℝ => r ^ 2) (2 * x) x := by
          simpa using hasDerivAt_pow 2 x
        exact ((hasDerivAt_id' x).sub h2)
      have hq : HasDerivAt (fun r : ℝ => 1 - 2 * r) (-2) x := by
        have := ((hasDerivAt_id' x).const_mul 2).const_sub 1
        simpa using this
      have h4 : HasDerivAt (fun r => (r - r ^ 2) * sin (ω * r) / ω)
          (((1 - 2 * x) * sin (ω * x) + (x - x ^ 2) * (cos (ω * x) * ω)) / ω) x :=
        (hp.mul h1.sin).div_const ω
      have h5 : HasDerivAt (fun r => (1 - 2 * r) * cos (ω * r) / ω ^ 2)
          ((-2 * cos (ω * x) + (1 - 2 * x) * (-sin (ω * x) * ω)) / ω ^ 2) x :=
        (hq.mul h1.cos).div_const (ω ^ 2)
      have h6 : HasDerivAt (fun r => 2 * sin (ω * r) / ω ^ 3) (2 * (cos (ω * x) * ω) / ω ^ 3) x :=
        (h1.sin.const_mul 2).div_const (ω ^ 3)
      refine ((h4.add h5).add h6).congr_deriv ?_
      field_simp
      ring
    rw [integral_eq_sub_of_hasDerivAt hd (Continuous.intervalIntegrable (by fun_prop) _ _)]
    have hc : cos ω = 1 := cos_two_pi_int n
    have hs : sin ω = 0 := sin_two_pi_int n
    simp only [mul_one, mul_zero, hc, hs, cos_zero, sin_zero, zero_div, add_zero]
    rw [hω]
    field_simp
    ring

/-! ### The autocorrelation integrand -/

/-- **Product of two cosine waves on the shifted window.**
`∫_{-1/2}^{1/2-r} cos(2πjs) cos(2πk(s + r)) ds = (waveInt (j + k) k r + waveInt (j - k) (-k) r) / 2`. -/
lemma integral_cos_mul_cos_shift (j k : ℤ) (r : ℝ) :
    ∫ s in (-(1:ℝ)/2)..(1/2 - r), cos (2 * π * j * s) * cos (2 * π * k * (s + r))
      = (waveInt (j + k) k r + waveInt (j - k) (-k) r) / 2 := by
  have e : ∀ s : ℝ, cos (2 * π * j * s) * cos (2 * π * k * (s + r))
      = (cos (2 * π * ((j + k : ℤ) : ℝ) * s + 2 * π * k * r)
          + cos (2 * π * ((j - k : ℤ) : ℝ) * s + 2 * π * ((-k : ℤ) : ℝ) * r)) / 2 := by
    intro s
    rw [cos_mul_cos_eq]
    congr 3 <;> push_cast <;> ring
  simp_rw [e]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    integral_wave, integral_wave]

/-- `∫₀¹ r · waveInt m k r dr`. -/
def outerW (m k : ℤ) : ℝ :=
  if m = 0 then rhoW k else (-1) ^ m * (sigmaW (k - m) - sigmaW k) / (2 * π * m)

/-- **Outer integral.** `∫₀¹ r · waveInt m k r dr = outerW m k`. -/
lemma integral_mul_waveInt (m k : ℤ) : ∫ r in (0:ℝ)..1, r * waveInt m k r = outerW m k := by
  by_cases hm : m = 0
  · have e : ∀ r : ℝ, r * waveInt m k r = r * ((1 - r) * cos (2 * π * k * r)) := fun r => by
      rw [waveInt, if_pos hm]
    simp_rw [e]
    rw [integral_mul_one_sub_mul_cos, outerW, if_pos hm]
  · have e : ∀ r : ℝ, r * waveInt m k r
        = (-1) ^ m / (2 * π * m) * (r * sin (2 * π * ((k - m : ℤ) : ℝ) * r)
            - r * sin (2 * π * k * r)) := fun r => by
      rw [waveInt, if_neg hm]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      integral_mul_sin, integral_mul_sin, outerW, if_neg hm]
    ring

end Distinct839.Constant
