/-
Distinct839/Window/Profile.lean — the cosine polynomial `fCos` and the profile `vProf = (2/5) fCos`.

Facts used by the window class (W1) and the window moments (W2):

* the six coefficients as rationals (`aC_vals`) and the expansion of `fCos` in the frequencies
  `cosN (j+1)` of `Trig.lean` (`fCos_eq`);
* pointwise bounds: `678411/10⁶ ≤ fCos ≤ 1321589/10⁶` everywhere (`|∑ a_j cos| ≤ ∑ |a_j|`), and
  `fCos s ≤ 992/1000` on the edge zone `3/8 ≤ |s| ≤ 1/2`, where `cos(2πs) ≤ -√2/2`;
* the derivatives `fCos' = fCos1`, `fCos1' = fCos2` (explicit trigonometric sums) with
  `|fCos1| ≤ 4.62`, `|fCos2| ≤ 110`;
* the integrals over `[-1/2, 1/2]`: `∫ fCos = 1`, `∫ fCos² = 1 + ∑ a_j²/2`,
  `∫ fCos1² = 2π² ∑ j² a_j² ≤ 2.408` (orthogonality of the sines).

All declarations are helpers, in `Distinct839.Window`.
-/
import Distinct839.Window.Trig

open Real MeasureTheory intervalIntegral
open scoped BigOperators

noncomputable section

namespace Distinct839.Window

/-! ### The coefficients -/

/-- The six coefficients `a_1, …, a_6` as rationals. -/
lemma aC_vals : aC 0 = 193305 / 1000000 ∧ aC 1 = -23105 / 1000000 ∧ aC 2 = 29166 / 1000000 ∧
    aC 3 = 13952 / 1000000 ∧ aC 4 = -21009 / 1000000 ∧ aC 5 = 41052 / 1000000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [aC, show aInt 0 = 193305 from rfl]; norm_num
  · rw [aC, show aInt 1 = -23105 from rfl]; norm_num
  · rw [aC, show aInt 2 = 29166 from rfl]; norm_num
  · rw [aC, show aInt 3 = 13952 from rfl]; norm_num
  · rw [aC, show aInt 4 = -21009 from rfl]; norm_num
  · rw [aC, show aInt 5 = 41052 from rfl]; norm_num

/-- `∑ |a_j| = 0.321589`. -/
lemma sum_abs_aC : ∑ j : Fin 6, |aC j| = 321589 / 1000000 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := aC_vals
  rw [Fin.sum_univ_six, h0, h1, h2, h3, h4, h5]; norm_num [abs_of_nonneg, abs_of_nonpos]

/-- `∑ j |a_j| = 0.734178`. -/
lemma sum_mul_abs_aC : ∑ j : Fin 6, ((j.val : ℝ) + 1) * |aC j| = 367089 / 500000 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := aC_vals
  rw [Fin.sum_univ_six, h0, h1, h2, h3, h4, h5]; norm_num [abs_of_nonneg, abs_of_nonpos]

/-- `∑ j² |a_j| = 2.774548`. -/
lemma sum_sq_mul_abs_aC : ∑ j : Fin 6, ((j.val : ℝ) + 1) ^ 2 * |aC j| = 693637 / 250000 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := aC_vals
  rw [Fin.sum_univ_six, h0, h1, h2, h3, h4, h5]; norm_num [abs_of_nonneg, abs_of_nonpos]

/-- `∑ a_j² = 0.04107262…`. -/
lemma sum_aC_sq : ∑ j : Fin 6, aC j ^ 2 = 8214524539 / 200000000000 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := aC_vals
  rw [Fin.sum_univ_six, h0, h1, h2, h3, h4, h5]; norm_num

/-- `∑ j² a_j² = 0.12197667…`. -/
lemma sum_sq_mul_aC_sq : ∑ j : Fin 6, ((j.val : ℝ) + 1) ^ 2 * aC j ^ 2 = 60988336681 / 500000000000 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := aC_vals
  rw [Fin.sum_univ_six, h0, h1, h2, h3, h4, h5]; norm_num

/-! ### `fCos` in the frequencies `cosN (j+1)` -/

lemma fCos_eq (u : ℝ) : fCos u = 1 + ∑ j : Fin 6, aC j * cosN (j.val + 1) u := by
  simp only [fCos, cosN, Nat.cast_add, Nat.cast_one]

lemma fCos_expand (u : ℝ) : fCos u = 1 + 193305 / 1000000 * cosN 1 u - 23105 / 1000000 * cosN 2 u
    + 29166 / 1000000 * cosN 3 u + 13952 / 1000000 * cosN 4 u - 21009 / 1000000 * cosN 5 u
    + 41052 / 1000000 * cosN 6 u := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := aC_vals
  rw [fCos_eq, Fin.sum_univ_six, h0, h1, h2, h3, h4, h5]
  norm_num
  ring

lemma fCos_even (u : ℝ) : fCos (-u) = fCos u := by
  simp only [fCos_eq, cosN_neg]

lemma vProf_even (s : ℝ) : vProf (-s) = vProf s := by
  simp only [vProf, fCos_even]

lemma contDiff_cosN {n : WithTop ℕ∞} (k : ℕ) : ContDiff ℝ n (cosN k) :=
  Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)

lemma contDiff_fCos {n : WithTop ℕ∞} : ContDiff ℝ n fCos := by
  have h : fCos = fun u => 1 + ∑ j : Fin 6, aC j * cosN (j.val + 1) u := funext fCos_eq
  rw [h]
  exact contDiff_const.add (ContDiff.sum fun j _ => contDiff_const.mul (contDiff_cosN _))

lemma contDiff_vProf {n : WithTop ℕ∞} : ContDiff ℝ n vProf :=
  contDiff_const.mul contDiff_fCos

lemma continuous_fCos : Continuous fCos := (contDiff_fCos (n := 0)).continuous

lemma continuous_vProf : Continuous vProf := (contDiff_vProf (n := 0)).continuous

/-! ### Pointwise bounds -/

/-- `|∑ b_j cos(2π (j+1) s)| ≤ ∑ |b_j|`. -/
lemma abs_sum_cos_le {N : ℕ} (b : Fin N → ℝ) (s : ℝ) :
    |∑ j : Fin N, b j * cosN (j.val + 1) s| ≤ ∑ j : Fin N, |b j| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_cosN_le_one _ _)

/-- `|∑ b_j sin(2π (j+1) s)| ≤ ∑ |b_j|`. -/
lemma abs_sum_sin_le {N : ℕ} (b : Fin N → ℝ) (s : ℝ) :
    |∑ j : Fin N, b j * sinN (j.val + 1) s| ≤ ∑ j : Fin N, |b j| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_sinN_le_one _ _)

/-- `fCos ≥ 1 - ∑ |a_j| = 0.678411` everywhere. -/
lemma fCos_ge (s : ℝ) : 678411 / 1000000 ≤ fCos s := by
  have h := abs_sum_cos_le aC s
  rw [sum_abs_aC] at h
  rw [fCos_eq]
  linarith [(abs_le.mp h).1]

/-- `fCos ≤ 1 + ∑ |a_j| = 1.321589` everywhere. -/
lemma fCos_le (s : ℝ) : fCos s ≤ 1321589 / 1000000 := by
  have h := abs_sum_cos_le aC s
  rw [sum_abs_aC] at h
  rw [fCos_eq]
  linarith [(abs_le.mp h).2]

lemma vProf_ge (s : ℝ) : 271 / 1000 ≤ vProf s := by
  have := fCos_ge s; unfold vProf; linarith

lemma vProf_pos (s : ℝ) : 0 < vProf s := by
  have := vProf_ge s; linarith

lemma vProf_le (s : ℝ) : vProf s ≤ 53 / 100 := by
  have := fCos_le s; unfold vProf; linarith

/-- `√2 / 2 ≥ 0.7071`. -/
lemma sqrt_two_div_two_ge : 7071 / 10000 ≤ √2 / 2 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

/-- On `[3/8, 1/2]`, `cos(2πs) ≤ cos(3π/4) = -√2/2 ≤ -0.7071`. -/
lemma cosN_one_le_of_mem {s : ℝ} (h1 : 3 / 8 ≤ s) (h2 : s ≤ 1 / 2) : cosN 1 s ≤ -(7071 / 10000) := by
  have hpi := Real.pi_pos
  have hc : cosN 1 s ≤ Real.cos (π - π / 4) := by
    unfold cosN
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith) (by push_cast; nlinarith)
    push_cast; nlinarith
  rw [Real.cos_pi_sub, Real.cos_pi_div_four] at hc
  linarith [sqrt_two_div_two_ge]

/-- **Edge bound**: `fCos s ≤ 0.992` for `3/8 ≤ |s| ≤ 1/2`. -/
lemma fCos_le_edge {s : ℝ} (h1 : 3 / 8 ≤ |s|) (h2 : |s| ≤ 1 / 2) : fCos s ≤ 992 / 1000 := by
  have key : ∀ t : ℝ, 3 / 8 ≤ t → t ≤ 1 / 2 → fCos t ≤ 992 / 1000 := by
    intro t ht1 ht2
    have hc1 := cosN_one_le_of_mem ht1 ht2
    have b2 := abs_le.mp (abs_cosN_le_one 2 t)
    have b3 := abs_le.mp (abs_cosN_le_one 3 t)
    have b4 := abs_le.mp (abs_cosN_le_one 4 t)
    have b5 := abs_le.mp (abs_cosN_le_one 5 t)
    have b6 := abs_le.mp (abs_cosN_le_one 6 t)
    rw [fCos_expand]
    linarith [b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2]
  rcases le_or_gt 0 s with hs | hs
  · rw [abs_of_nonneg hs] at h1 h2; exact key s h1 h2
  · rw [abs_of_neg hs] at h1 h2; rw [← fCos_even]; exact key (-s) h1 h2

/-! ### Derivatives -/

/-- Coefficients of `fCos'`: `-2π (j+1) a_j`. -/
def d1 (j : Fin 6) : ℝ := -(2 * π * ((j.val : ℝ) + 1) * aC j)

/-- Coefficients of `fCos''`: `-(2π (j+1))² a_j`. -/
def d2 (j : Fin 6) : ℝ := -((2 * π * ((j.val : ℝ) + 1)) ^ 2 * aC j)

/-- `fCos' = ∑ d1_j sin(2π (j+1) s)`. -/
def fCos1 (s : ℝ) : ℝ := ∑ j : Fin 6, d1 j * sinN (j.val + 1) s

/-- `fCos'' = ∑ d2_j cos(2π (j+1) s)`. -/
def fCos2 (s : ℝ) : ℝ := ∑ j : Fin 6, d2 j * cosN (j.val + 1) s

lemma hasDerivAt_fCos (s : ℝ) : HasDerivAt fCos (fCos1 s) s := by
  have h : fCos = fun u => 1 + ∑ j : Fin 6, aC j * cosN (j.val + 1) u := funext fCos_eq
  rw [h]
  have hs := HasDerivAt.sum (u := Finset.univ) (A := fun (j : Fin 6) u => aC j * cosN (j.val + 1) u)
    (fun j _ => (hasDerivAt_cosN (j.val + 1) s).const_mul (aC j))
  refine (hs.const_add 1).congr_deriv ?_
  unfold fCos1 d1
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

lemma hasDerivAt_fCos1 (s : ℝ) : HasDerivAt fCos1 (fCos2 s) s := by
  have hs := HasDerivAt.sum (u := Finset.univ) (A := fun (j : Fin 6) u => d1 j * sinN (j.val + 1) u)
    (fun j _ => (hasDerivAt_sinN (j.val + 1) s).const_mul (d1 j))
  refine hs.congr_deriv ?_
  unfold fCos2 d1 d2
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

lemma continuous_fCos1 : Continuous fCos1 :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_sinN _)

lemma continuous_fCos2 : Continuous fCos2 :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_cosN _)

lemma sum_abs_d1 : ∑ j : Fin 6, |d1 j| = 2 * π * (367089 / 500000) := by
  rw [← sum_mul_abs_aC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [d1, abs_neg, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π * ((j.val : ℝ) + 1))]
  ring

lemma sum_abs_d2 : ∑ j : Fin 6, |d2 j| = 4 * π ^ 2 * (693637 / 250000) := by
  rw [← sum_sq_mul_abs_aC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [d2, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (2 * π * ((j.val : ℝ) + 1)) ^ 2)]
  ring

/-- `|fCos'| ≤ 2π ∑ j |a_j| ≤ 4.62`. -/
lemma abs_fCos1_le (s : ℝ) : |fCos1 s| ≤ 462 / 100 := by
  have h := abs_sum_sin_le d1 s
  rw [sum_abs_d1] at h
  have hpi := Real.pi_lt_d4
  unfold fCos1
  linarith

/-- `|fCos''| ≤ 4π² ∑ j² |a_j| ≤ 110`. -/
lemma abs_fCos2_le (s : ℝ) : |fCos2 s| ≤ 110 := by
  have h := abs_sum_cos_le d2 s
  rw [sum_abs_d2] at h
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have hpi2 : π ^ 2 < 3.1416 ^ 2 := by nlinarith
  unfold fCos2
  linarith

/-! ### Integrals over `[-1/2, 1/2]` -/

/-- `∫ fCos = 1`. -/
lemma integral_fCos : ∫ s in (-(1:ℝ)/2)..(1/2), fCos s = 1 := by
  simp_rw [fCos_eq]
  rw [intervalIntegral.integral_add (by simp) ((continuous_sum_cos aC).intervalIntegrable _ _),
    integral_sum_cos, integral_one]
  ring

/-- `∫ fCos² = 1 + ∑ a_j² / 2`. -/
lemma integral_fCos_sq :
    ∫ s in (-(1:ℝ)/2)..(1/2), fCos s ^ 2 = 1 + (∑ j : Fin 6, aC j ^ 2) / 2 := by
  have hS := continuous_sum_cos aC
  have h1 : ∀ s, fCos s ^ 2 = (1 + 2 * ∑ j : Fin 6, aC j * cosN (j.val + 1) s)
      + (∑ j : Fin 6, aC j * cosN (j.val + 1) s) ^ 2 := fun s => by rw [fCos_eq]; ring
  have i1 : IntervalIntegrable (fun s => 1 + 2 * ∑ j : Fin 6, aC j * cosN (j.val + 1) s) volume
      (-(1:ℝ)/2) (1/2) := (continuous_const.add (continuous_const.mul hS)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun s => (∑ j : Fin 6, aC j * cosN (j.val + 1) s) ^ 2) volume
      (-(1:ℝ)/2) (1/2) := (hS.pow 2).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume (-(1:ℝ)/2) (1/2) :=
    continuous_const.intervalIntegrable _ _
  have i4 : IntervalIntegrable (fun s => 2 * ∑ j : Fin 6, aC j * cosN (j.val + 1) s) volume
      (-(1:ℝ)/2) (1/2) := (continuous_const.mul hS).intervalIntegrable _ _
  simp_rw [h1]
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_add i3 i4,
    intervalIntegral.integral_const_mul, integral_sum_cos, integral_sq_sum_cos, integral_one]
  ring

/-- `∫ fCos'² = ∑ d1_j² / 2 = 2π² ∑ j² a_j²`. -/
lemma integral_fCos1_sq : ∫ s in (-(1:ℝ)/2)..(1/2), fCos1 s ^ 2
    = 2 * π ^ 2 * (60988336681 / 500000000000) := by
  unfold fCos1
  rw [integral_sq_sum_sin, ← sum_sq_mul_aC_sq, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [d1]
  ring

/-- `∫ fCos'² ≤ 2.408`. -/
lemma integral_fCos1_sq_le : ∫ s in (-(1:ℝ)/2)..(1/2), fCos1 s ^ 2 ≤ 2408 / 1000 := by
  rw [integral_fCos1_sq]
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  nlinarith

end Distinct839.Window
