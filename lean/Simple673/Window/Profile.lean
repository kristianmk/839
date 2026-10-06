/-
Simple673/Window/Profile.lean — the cosine polynomial `fCos` and the profile
`vProf = (2/5) fCos`.

Facts used by the window class (W1):

* the ten coefficients as rationals (`aC_vals`) and the expansion of `fCos` in the frequencies
  `cosN (j+1)` of `Distinct839/Window/Trig.lean` (`fCos_eq`);
* pointwise bounds: `789328/10⁶ ≤ fCos ≤ 1210672/10⁶` everywhere (`|∑ a_j cos| ≤ ∑ |a_j|`), and
  `fCos s ≤ 1002/1000` on the edge zone `3/8 ≤ |s| ≤ 1/2`, where `cos(2πs) ≤ -√2/2`;
* the derivatives `fCos' = fCos1`, `fCos1' = fCos2` (explicit trigonometric sums) with
  `|fCos1| ≤ 3`, `|fCos2| ≤ 83`;
* the integrals over `[-1/2, 1/2]`: `∫ fCos = 1`, `∫ fCos² = 1 + ∑ a_j²/2`,
  `∫ fCos1² = 2π² ∑ j² a_j² ≤ 0.655` (orthogonality of the sines).

The pointwise bounds are the crude ones through the sums `∑ |a_j| = 0.210672`,
`∑ j |a_j| = 0.465488` and `∑ j² |a_j| = 2.084874`. They are not sharp; the window class needs no
more.

The frequencies `cosN n u = cos(2π n u)`, `sinN n u = sin(2π n u)` and their integrals do not
depend on the window; they are those of `Distinct839.Window` and are referred to by their full
names. All declarations here are helpers, in `Simple673.Window`.
-/
import Distinct839.Window.Trig
import Simple673.Defs
import Simple673.Sum10

open Real MeasureTheory intervalIntegral
open scoped BigOperators

noncomputable section

namespace Simple673.Window

/-! ### The coefficients -/

/-- The ten coefficients `a_1, …, a_10` as rationals (`a_2`, `a_7` and `a_9` are negative). -/
lemma aC_vals : aC 0 = 122290 / 1000000 ∧ aC 1 = -45012 / 1000000 ∧ aC 2 = 16241 / 1000000 ∧
    aC 3 = 1887 / 1000000 ∧ aC 4 = 2711 / 1000000 ∧ aC 5 = 3731 / 1000000 ∧
    aC 6 = -5307 / 1000000 ∧ aC 7 = 2982 / 1000000 ∧ aC 8 = -5153 / 1000000 ∧
    aC 9 = 5358 / 1000000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [aC, show aInt 0 = 122290 from rfl]; norm_num
  · rw [aC, show aInt 1 = -45012 from rfl]; norm_num
  · rw [aC, show aInt 2 = 16241 from rfl]; norm_num
  · rw [aC, show aInt 3 = 1887 from rfl]; norm_num
  · rw [aC, show aInt 4 = 2711 from rfl]; norm_num
  · rw [aC, show aInt 5 = 3731 from rfl]; norm_num
  · rw [aC, show aInt 6 = -5307 from rfl]; norm_num
  · rw [aC, show aInt 7 = 2982 from rfl]; norm_num
  · rw [aC, show aInt 8 = -5153 from rfl]; norm_num
  · rw [aC, show aInt 9 = 5358 from rfl]; norm_num

/-- `∑ |a_j| = 0.210672`. -/
lemma sum_abs_aC : ∑ j : Fin 10, |aC j| = 210672 / 1000000 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := aC_vals
  rw [sum_univ_ten, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- `∑ j |a_j| = 0.465488`. -/
lemma sum_mul_abs_aC : ∑ j : Fin 10, ((j.val : ℝ) + 1) * |aC j| = 465488 / 1000000 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := aC_vals
  rw [sum_univ_ten, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- `∑ j² |a_j| = 2.084874`. -/
lemma sum_sq_mul_abs_aC : ∑ j : Fin 10, ((j.val : ℝ) + 1) ^ 2 * |aC j| = 2084874 / 1000000 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := aC_vals
  rw [sum_univ_ten, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- `∑ a_j² = 0.017361843122`. -/
lemma sum_aC_sq : ∑ j : Fin 10, aC j ^ 2 = 8680921561 / 500000000000 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := aC_vals
  rw [sum_univ_ten, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]; norm_num

/-- `∑ j² a_j² = 0.033145738196`. -/
lemma sum_sq_mul_aC_sq :
    ∑ j : Fin 10, ((j.val : ℝ) + 1) ^ 2 * aC j ^ 2 = 8286434549 / 250000000000 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := aC_vals
  rw [sum_univ_ten, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]; norm_num

/-! ### `fCos` in the frequencies `cosN (j+1)` -/

lemma fCos_eq (u : ℝ) :
    fCos u = 1 + ∑ j : Fin 10, aC j * Distinct839.Window.cosN (j.val + 1) u := by
  simp only [fCos, Distinct839.Window.cosN, Nat.cast_add, Nat.cast_one]

lemma fCos_expand (u : ℝ) : fCos u = 1 + 122290 / 1000000 * Distinct839.Window.cosN 1 u
    - 45012 / 1000000 * Distinct839.Window.cosN 2 u
    + 16241 / 1000000 * Distinct839.Window.cosN 3 u
    + 1887 / 1000000 * Distinct839.Window.cosN 4 u
    + 2711 / 1000000 * Distinct839.Window.cosN 5 u
    + 3731 / 1000000 * Distinct839.Window.cosN 6 u
    - 5307 / 1000000 * Distinct839.Window.cosN 7 u
    + 2982 / 1000000 * Distinct839.Window.cosN 8 u
    - 5153 / 1000000 * Distinct839.Window.cosN 9 u
    + 5358 / 1000000 * Distinct839.Window.cosN 10 u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := aC_vals
  rw [fCos_eq, sum_univ_ten, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  norm_num
  ring

lemma fCos_even (u : ℝ) : fCos (-u) = fCos u := by
  simp only [fCos_eq, Distinct839.Window.cosN_neg]

lemma vProf_even (s : ℝ) : vProf (-s) = vProf s := by
  simp only [vProf, fCos_even]

lemma contDiff_cosN {n : WithTop ℕ∞} (k : ℕ) : ContDiff ℝ n (Distinct839.Window.cosN k) :=
  Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)

lemma contDiff_fCos {n : WithTop ℕ∞} : ContDiff ℝ n fCos := by
  have h : fCos = fun u => 1 + ∑ j : Fin 10, aC j * Distinct839.Window.cosN (j.val + 1) u :=
    funext fCos_eq
  rw [h]
  exact contDiff_const.add (ContDiff.sum fun j _ => contDiff_const.mul (contDiff_cosN _))

lemma contDiff_vProf {n : WithTop ℕ∞} : ContDiff ℝ n vProf :=
  contDiff_const.mul contDiff_fCos

lemma continuous_fCos : Continuous fCos := (contDiff_fCos (n := 0)).continuous

lemma continuous_vProf : Continuous vProf := (contDiff_vProf (n := 0)).continuous

/-! ### Pointwise bounds -/

/-- `|∑ b_j cos(2π (j+1) s)| ≤ ∑ |b_j|`. -/
lemma abs_sum_cos_le {N : ℕ} (b : Fin N → ℝ) (s : ℝ) :
    |∑ j : Fin N, b j * Distinct839.Window.cosN (j.val + 1) s| ≤ ∑ j : Fin N, |b j| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Distinct839.Window.abs_cosN_le_one _ _)

/-- `|∑ b_j sin(2π (j+1) s)| ≤ ∑ |b_j|`. -/
lemma abs_sum_sin_le {N : ℕ} (b : Fin N → ℝ) (s : ℝ) :
    |∑ j : Fin N, b j * Distinct839.Window.sinN (j.val + 1) s| ≤ ∑ j : Fin N, |b j| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Distinct839.Window.abs_sinN_le_one _ _)

/-- `fCos ≥ 1 - ∑ |a_j| = 0.789328` everywhere. -/
lemma fCos_ge (s : ℝ) : 789328 / 1000000 ≤ fCos s := by
  have h := abs_sum_cos_le aC s
  rw [sum_abs_aC] at h
  rw [fCos_eq]
  linarith [(abs_le.mp h).1]

/-- `fCos ≤ 1 + ∑ |a_j| = 1.210672` everywhere. -/
lemma fCos_le (s : ℝ) : fCos s ≤ 1210672 / 1000000 := by
  have h := abs_sum_cos_le aC s
  rw [sum_abs_aC] at h
  rw [fCos_eq]
  linarith [(abs_le.mp h).2]

/-- `vProf ≥ (2/5)·0.789328 = 0.3157312 ≥ 0.315` everywhere. -/
lemma vProf_ge (s : ℝ) : 315 / 1000 ≤ vProf s := by
  have := fCos_ge s; unfold vProf; linarith

lemma vProf_pos (s : ℝ) : 0 < vProf s := by
  have := vProf_ge s; linarith

/-- `vProf ≤ (2/5)·1.210672 = 0.4842688 ≤ 0.485` everywhere. -/
lemma vProf_le (s : ℝ) : vProf s ≤ 485 / 1000 := by
  have := fCos_le s; unfold vProf; linarith

/-- `√2 / 2 ≥ 0.7071`. -/
lemma sqrt_two_div_two_ge : 7071 / 10000 ≤ √2 / 2 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

/-- On `[3/8, 1/2]`, `cos(2πs) ≤ cos(3π/4) = -√2/2 ≤ -0.7071`. -/
lemma cosN_one_le_of_mem {s : ℝ} (h1 : 3 / 8 ≤ s) (h2 : s ≤ 1 / 2) :
    Distinct839.Window.cosN 1 s ≤ -(7071 / 10000) := by
  have hpi := Real.pi_pos
  have hc : Distinct839.Window.cosN 1 s ≤ Real.cos (π - π / 4) := by
    unfold Distinct839.Window.cosN
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith) (by push_cast; nlinarith)
    push_cast; nlinarith
  rw [Real.cos_pi_sub, Real.cos_pi_div_four] at hc
  linarith [sqrt_two_div_two_ge]

/-- **Edge bound**: `fCos s ≤ 1.002` for `3/8 ≤ |s| ≤ 1/2`
(`1 - 0.7071·a_1 + ∑_{j ≥ 2} |a_j| = 1.00191…`). -/
lemma fCos_le_edge {s : ℝ} (h1 : 3 / 8 ≤ |s|) (h2 : |s| ≤ 1 / 2) : fCos s ≤ 1002 / 1000 := by
  have key : ∀ t : ℝ, 3 / 8 ≤ t → t ≤ 1 / 2 → fCos t ≤ 1002 / 1000 := by
    intro t ht1 ht2
    have hc1 := cosN_one_le_of_mem ht1 ht2
    have b2 := abs_le.mp (Distinct839.Window.abs_cosN_le_one 2 t)
    have b3 := abs_le.mp (Distinct839.Window.abs_cosN_le_one 3 t)
    have b4 := abs_le.mp (Distinct839.Window.abs_cosN_le_one 4 t)
    have b5 := abs_le.mp (Distinct839.Window.abs_cosN_le_one 5 t)
    have b6 := abs_le.mp (Distinct839.Window.abs_cosN_le_one 6 t)
    have b7 := abs_le.mp (Distinct839.Window.abs_cosN_le_one 7 t)
    have b8 := abs_le.mp (Distinct839.Window.abs_cosN_le_one 8 t)
    have b9 := abs_le.mp (Distinct839.Window.abs_cosN_le_one 9 t)
    have b10 := abs_le.mp (Distinct839.Window.abs_cosN_le_one 10 t)
    rw [fCos_expand]
    linarith [b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2,
      b9.1, b9.2, b10.1, b10.2]
  rcases le_or_gt 0 s with hs | hs
  · rw [abs_of_nonneg hs] at h1 h2; exact key s h1 h2
  · rw [abs_of_neg hs] at h1 h2; rw [← fCos_even]; exact key (-s) h1 h2

/-! ### Derivatives -/

/-- Coefficients of `fCos'`: `-2π (j+1) a_j`. -/
def d1 (j : Fin 10) : ℝ := -(2 * π * ((j.val : ℝ) + 1) * aC j)

/-- Coefficients of `fCos''`: `-(2π (j+1))² a_j`. -/
def d2 (j : Fin 10) : ℝ := -((2 * π * ((j.val : ℝ) + 1)) ^ 2 * aC j)

/-- `fCos' = ∑ d1_j sin(2π (j+1) s)`. -/
def fCos1 (s : ℝ) : ℝ := ∑ j : Fin 10, d1 j * Distinct839.Window.sinN (j.val + 1) s

/-- `fCos'' = ∑ d2_j cos(2π (j+1) s)`. -/
def fCos2 (s : ℝ) : ℝ := ∑ j : Fin 10, d2 j * Distinct839.Window.cosN (j.val + 1) s

lemma hasDerivAt_fCos (s : ℝ) : HasDerivAt fCos (fCos1 s) s := by
  have h : fCos = fun u => 1 + ∑ j : Fin 10, aC j * Distinct839.Window.cosN (j.val + 1) u :=
    funext fCos_eq
  rw [h]
  have hs := HasDerivAt.sum (u := Finset.univ)
    (A := fun (j : Fin 10) u => aC j * Distinct839.Window.cosN (j.val + 1) u)
    (fun j _ => (Distinct839.Window.hasDerivAt_cosN (j.val + 1) s).const_mul (aC j))
  refine (hs.const_add 1).congr_deriv ?_
  unfold fCos1 d1
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

lemma hasDerivAt_fCos1 (s : ℝ) : HasDerivAt fCos1 (fCos2 s) s := by
  have hs := HasDerivAt.sum (u := Finset.univ)
    (A := fun (j : Fin 10) u => d1 j * Distinct839.Window.sinN (j.val + 1) u)
    (fun j _ => (Distinct839.Window.hasDerivAt_sinN (j.val + 1) s).const_mul (d1 j))
  refine hs.congr_deriv ?_
  unfold fCos2 d1 d2
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

lemma continuous_fCos1 : Continuous fCos1 :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (Distinct839.Window.continuous_sinN _)

lemma continuous_fCos2 : Continuous fCos2 :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (Distinct839.Window.continuous_cosN _)

lemma sum_abs_d1 : ∑ j : Fin 10, |d1 j| = 2 * π * (465488 / 1000000) := by
  rw [← sum_mul_abs_aC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [d1, abs_neg, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π * ((j.val : ℝ) + 1))]
  ring

lemma sum_abs_d2 : ∑ j : Fin 10, |d2 j| = 4 * π ^ 2 * (2084874 / 1000000) := by
  rw [← sum_sq_mul_abs_aC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [d2, abs_neg, abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (2 * π * ((j.val : ℝ) + 1)) ^ 2)]
  ring

/-- `|fCos'| ≤ 2π ∑ j |a_j| ≤ 3` (the value is `2.92474…`). -/
lemma abs_fCos1_le (s : ℝ) : |fCos1 s| ≤ 3 := by
  have h := abs_sum_sin_le d1 s
  rw [sum_abs_d1] at h
  have hpi := Real.pi_lt_d4
  unfold fCos1
  linarith

/-- `|fCos''| ≤ 4π² ∑ j² |a_j| ≤ 83` (the value is `82.3075…`). -/
lemma abs_fCos2_le (s : ℝ) : |fCos2 s| ≤ 83 := by
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
  rw [intervalIntegral.integral_add (by simp)
      ((Distinct839.Window.continuous_sum_cos aC).intervalIntegrable _ _),
    Distinct839.Window.integral_sum_cos, Distinct839.Window.integral_one]
  ring

/-- `∫ fCos² = 1 + ∑ a_j² / 2`. -/
lemma integral_fCos_sq :
    ∫ s in (-(1:ℝ)/2)..(1/2), fCos s ^ 2 = 1 + (∑ j : Fin 10, aC j ^ 2) / 2 := by
  have hS := Distinct839.Window.continuous_sum_cos aC
  have h1 : ∀ s, fCos s ^ 2
      = (1 + 2 * ∑ j : Fin 10, aC j * Distinct839.Window.cosN (j.val + 1) s)
        + (∑ j : Fin 10, aC j * Distinct839.Window.cosN (j.val + 1) s) ^ 2 :=
    fun s => by rw [fCos_eq]; ring
  have i1 : IntervalIntegrable
      (fun s => 1 + 2 * ∑ j : Fin 10, aC j * Distinct839.Window.cosN (j.val + 1) s) volume
      (-(1:ℝ)/2) (1/2) := (continuous_const.add (continuous_const.mul hS)).intervalIntegrable _ _
  have i2 : IntervalIntegrable
      (fun s => (∑ j : Fin 10, aC j * Distinct839.Window.cosN (j.val + 1) s) ^ 2) volume
      (-(1:ℝ)/2) (1/2) := (hS.pow 2).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume (-(1:ℝ)/2) (1/2) :=
    continuous_const.intervalIntegrable _ _
  have i4 : IntervalIntegrable
      (fun s => 2 * ∑ j : Fin 10, aC j * Distinct839.Window.cosN (j.val + 1) s) volume
      (-(1:ℝ)/2) (1/2) := (continuous_const.mul hS).intervalIntegrable _ _
  simp_rw [h1]
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_add i3 i4,
    intervalIntegral.integral_const_mul, Distinct839.Window.integral_sum_cos,
    Distinct839.Window.integral_sq_sum_cos, Distinct839.Window.integral_one]
  ring

/-- `∫ fCos'² = ∑ d1_j² / 2 = 2π² ∑ j² a_j²`. -/
lemma integral_fCos1_sq : ∫ s in (-(1:ℝ)/2)..(1/2), fCos1 s ^ 2
    = 2 * π ^ 2 * (8286434549 / 250000000000) := by
  unfold fCos1
  rw [Distinct839.Window.integral_sq_sum_sin, ← sum_sq_mul_aC_sq, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [d1]
  ring

/-- `∫ fCos'² ≤ 0.655` (the value is `0.65427…`). -/
lemma integral_fCos1_sq_le : ∫ s in (-(1:ℝ)/2)..(1/2), fCos1 s ^ 2 ≤ 655 / 1000 := by
  rw [integral_fCos1_sq]
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  nlinarith

end Simple673.Window
