/-
Line889/Majorant/Separated.lean — the norm bound and the quadratic form on separated sets.

* `lMajBound`: `LMaj = (2γ/d)(1 + sinc d) = 1.67931… ≤ 168/100`, from a Taylor bound for
  `sin(17π/20) = sin(3π/20)`.
* `separatedBound`: for points `y_i` with `|y_i - y_j| ≥ d` and a measurable weight `0 ≤ w ≤ gMaj`,
  `∫ w(u) ∑_{i,j} x_i x_j cos(2π (y_i - y_j) u) du ≤ LMaj ∑ x_i²`. The double sum is
  `|∑ x_i e^{2π i y_i u}|² ≥ 0`, so `w` may be replaced by `gMaj`, and then the off-diagonal
  integrals vanish because the cosine transform of `gMaj` vanishes at frequencies `≥ d`.

The file follows `Simple673/Majorant/Separated.lean` and `Distinct839/Majorant/Separated.lean`;
only the last numerical step of `lMajBound` depends on the value of `γ = gammaM = 61/100`:
`2γ/d = 122/85` and `LMaj ≤ (122/85)(1 + (3/17) · 0.963401) = 1.6793113… ≤ 1.68`.
-/
import Line889.Spec
import Distinct839.Majorant.Taylor
import Line889.Majorant.Fourier

open Real MeasureTheory
open scoped BigOperators

namespace Line889

open Majorant

/-! ## The bound for `LMaj` -/

/-- `LMaj ≤ 168/100`. -/
theorem lMajBound : LMajBound := by
  unfold LMajBound LMaj sincN
  have hpos : 0 < π * sep := mul_pos pi_pos sep_pos
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = π * (3 / 20) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hylo : (4712388 : ℝ) / 10000000 ≤ y := by
    rw [hy]
    have h := pi_gt_d6
    norm_num at h
    linarith
  have hyhi : y ≤ (47123895 : ℝ) / 100000000 := by
    rw [hy]
    have h := pi_lt_d6
    norm_num at h
    linarith
  have h2 : (22206 : ℝ) / 100000 ≤ y ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hylo) (sub_nonneg.mpr hylo)]
  have h2' : y ^ 2 ≤ (22207 : ℝ) / 100000 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hyhi) hy0]
  have h4 : y ^ 4 ≤ (4932 : ℝ) / 100000 := by
    have e : y ^ 4 = y ^ 2 * y ^ 2 := by ring
    rw [e]
    nlinarith [mul_nonneg (sub_nonneg.mpr h2') (sq_nonneg y)]
  have hsin : sin (π * sep) = sin y := by
    rw [hy, ← sin_pi_sub]
    congr 1
    unfold sep
    ring
  have hpoly : Distinct839.Majorant.sinPoly y (0 + 1 + 1 + 1)
      = y * (1 - y ^ 2 / 6 + y ^ 4 / 120) := by
    rw [Distinct839.Majorant.sinPoly_succ, Distinct839.Majorant.sinPoly_succ,
      Distinct839.Majorant.sinPoly_succ, Distinct839.Majorant.sinPoly_zero]
    norm_num [Nat.factorial]
    ring
  have hup : sin y ≤ Distinct839.Majorant.sinPoly y (2 * 1 + 1) :=
    Distinct839.Majorant.sin_le_sinPoly hy0 1
  have hQ : 1 - y ^ 2 / 6 + y ^ 4 / 120 ≤ (963401 : ℝ) / 1000000 := by linarith
  have key : sin (π * sep) ≤ y * ((963401 : ℝ) / 1000000) := by
    rw [hsin]
    exact hup.trans ((le_of_eq hpoly).trans (mul_le_mul_of_nonneg_left hQ hy0))
  have hr : sin (π * sep) / (π * sep) ≤ 3 / 17 * ((963401 : ℝ) / 1000000) := by
    rw [div_le_iff₀ hpos]
    refine key.trans (le_of_eq ?_)
    rw [hy]
    unfold sep
    ring
  rw [sinc_of_ne_zero hpos.ne']
  have hc : 2 * gammaM / sep = 122 / 85 := by
    unfold gammaM sep
    norm_num
  rw [hc]
  linarith

end Line889

namespace Line889.Majorant

/-! ## The quadratic form -/

/-- The quadratic form `∑_{i,j} x_i x_j cos(2π (y_i - y_j) u)`. -/
noncomputable def quadForm {ι : Type} [Fintype ι] (y x : ι → ℝ) (u : ℝ) : ℝ :=
  ∑ i, ∑ j, x i * x j * cos (2 * π * (y i - y j) * u)

/-- The quadratic form is `|∑ x_i e^{2π i y_i u}|²`. -/
lemma quadForm_eq {ι : Type} [Fintype ι] (y x : ι → ℝ) (u : ℝ) :
    quadForm y x u = (∑ i, x i * cos (2 * π * y i * u)) ^ 2
      + (∑ i, x i * sin (2 * π * y i * u)) ^ 2 := by
  unfold quadForm
  rw [pow_two, pow_two, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show 2 * π * (y i - y j) * u = 2 * π * y i * u - 2 * π * y j * u by ring, cos_sub]
  ring

lemma quadForm_nonneg {ι : Type} [Fintype ι] (y x : ι → ℝ) (u : ℝ) : 0 ≤ quadForm y x u := by
  rw [quadForm_eq]
  positivity

lemma continuous_quadForm {ι : Type} [Fintype ι] (y x : ι → ℝ) : Continuous (quadForm y x) := by
  have h : Continuous fun u : ℝ => ∑ i, ∑ j, x i * x j * cos (2 * π * (y i - y j) * u) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by fun_prop
  exact h

lemma integrable_gMaj_mul_term (a c : ℝ) :
    Integrable fun u : ℝ => gMaj u * (c * cos (2 * π * a * u)) := by
  have h := (integrable_gMaj_mul_cos a).const_mul c
  have e : (fun u : ℝ => gMaj u * (c * cos (2 * π * a * u)))
      = fun u : ℝ => c * (gMaj u * cos (2 * π * a * u)) := by
    funext u; ring
  rw [e]
  exact h

lemma quadForm_expand {ι : Type} [Fintype ι] (y x : ι → ℝ) :
    (fun u : ℝ => gMaj u * quadForm y x u)
      = fun u : ℝ => ∑ i, ∑ j, gMaj u * (x i * x j * cos (2 * π * (y i - y j) * u)) := by
  funext u
  simp only [quadForm, Finset.mul_sum]

lemma integrable_gMaj_mul_quadForm {ι : Type} [Fintype ι] (y x : ι → ℝ) :
    Integrable fun u : ℝ => gMaj u * quadForm y x u := by
  rw [quadForm_expand]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_gMaj_mul_term (y i - y j) (x i * x j)

/-- On a `sep`-separated set the majorant gives the quadratic form `LMaj ∑ x_i²`. -/
theorem integral_gMaj_mul_quadForm {ι : Type} [Fintype ι] (y x : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → sep ≤ |y i - y j|) :
    ∫ u, gMaj u * quadForm y x u = LMaj * ∑ i, x i ^ 2 := by
  classical
  have hval : ∀ i j, ∫ u, gMaj u * (x i * x j * cos (2 * π * (y i - y j) * u))
      = if i = j then LMaj * x i ^ 2 else 0 := by
    intro i j
    have e : (fun u : ℝ => gMaj u * (x i * x j * cos (2 * π * (y i - y j) * u)))
        = fun u : ℝ => x i * x j * (gMaj u * cos (2 * π * (y i - y j) * u)) := by
      funext u; ring
    rw [e, integral_const_mul]
    split_ifs with hij
    · subst hij
      rw [sub_self, integral_gMaj_mul_cos, FMaj_zero]
      ring
    · rw [integral_gMaj_cos _ (hsep i j hij), mul_zero]
  rw [quadForm_expand]
  calc ∫ u, ∑ i, ∑ j, gMaj u * (x i * x j * cos (2 * π * (y i - y j) * u))
      = ∑ i, ∫ u, ∑ j, gMaj u * (x i * x j * cos (2 * π * (y i - y j) * u)) :=
        integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          integrable_gMaj_mul_term (y i - y j) (x i * x j)
    _ = ∑ i, ∑ j, ∫ u, gMaj u * (x i * x j * cos (2 * π * (y i - y j) * u)) :=
        Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ =>
          integrable_gMaj_mul_term (y i - y j) (x i * x j)
    _ = ∑ i, ∑ j, if i = j then LMaj * x i ^ 2 else 0 :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hval i j
    _ = ∑ i, LMaj * x i ^ 2 := Finset.sum_congr rfl fun i _ => by simp
    _ = LMaj * ∑ i, x i ^ 2 := (Finset.mul_sum _ _ _).symm

end Line889.Majorant

namespace Line889

open Majorant

/-- **The separated bound**: a measurable weight below the majorant has quadratic form at most
`LMaj` on every `sep`-separated finite set. -/
theorem separatedBound : SeparatedBound := by
  intro ι _ y x w hsep hw hw0 hwg
  have hDnn := quadForm_nonneg y x
  have hgD := integrable_gMaj_mul_quadForm y x
  have hwD : Integrable fun u : ℝ => w u * quadForm y x u := by
    refine hgD.mono' (hw.mul (continuous_quadForm y x).measurable).aestronglyMeasurable
      (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 u) (hDnn u))]
    exact mul_le_mul_of_nonneg_right (hwg u) (hDnn u)
  have h1 : ∫ u, w u * quadForm y x u ≤ ∫ u, gMaj u * quadForm y x u :=
    integral_mono hwD hgD fun u => mul_le_mul_of_nonneg_right (hwg u) (hDnn u)
  rw [integral_gMaj_mul_quadForm y x hsep] at h1
  exact h1

end Line889
