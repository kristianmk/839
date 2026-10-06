/-
Ceilings/Distinct/GramBridge.lean — a certificate in the sense of the Gram bound is a pair-energy
certificate: the two hypotheses of the Gram bound hold for every separated chain.

`GramCert.toPairCertAll : GramCert x₁ x₂ b → PairCertAll x₁ x₂ b`, hence the ceilings apply to
the certificates of the paper's method (`ceiling_gram`: no Gram certificate gives more than
`0.83998` with the window of `Distinct839`).

What has to be shown for a chain `y` with gaps at least `17/20` (`Ceilings/Distinct/Gram.lean`):

* the weighted kernel matrix `(√(m_i m_j) K(y_i - y_j))` is positive semidefinite
  (`kernelMatrix_posSemidef`): by `K(t) = ∫ f(u) cos(2π t u) du` with `f > 0`,
  `∑ z_i z_j K(y_i - y_j) = ∫ f(u) |∑ z_i e(y_i u)|² du ≥ 0` (`kernel_form_eq_integral`,
  `kernel_form_nonneg`), and a real symmetric matrix with nonnegative quadratic form is positive
  semidefinite as a complex matrix (`posSemidef_of_real`);
* the kernel matrix is bounded by `c/2` on every subset (`kernel_form_le`): the same integral,
  with the window extended by zero, is bounded by `L ∑ z_i²` by the separated bound of
  `Distinct839/Majorant/` (`separatedBound`, `majorantPointwise`), and `L ≤ 1.6711 < c/2 = 1.675`
  (`lMajBound`).
-/
import Ceilings.Distinct.Gram
import Ceilings.Distinct.All
import Distinct839.Majorant.Separated
import Distinct839.Majorant.Pointwise

open Matrix Finset Real MeasureTheory
open scoped ComplexOrder BigOperators

noncomputable section

namespace Ceilings

open Distinct839 (K sep mulOf phiC clipC fCos fWin gMaj LMaj)
open Distinct839.Majorant (quadForm quadForm_nonneg continuous_quadForm)

/-! ## The quadratic form of the kernel as an integral -/

/-- `∑ z_i z_j K(y_i - y_j) = ∫_{-1/2}^{1/2} f(u) ∑ z_i z_j cos(2π (y_i - y_j) u) du`. -/
theorem kernel_form_eq_integral {ι : Type} [Fintype ι] (y z : ι → ℝ) :
    ∑ i, ∑ j, z i * z j * K (y i - y j)
      = ∫ u in (-(1 : ℝ) / 2)..(1 / 2), fCos u * quadForm y z u := by
  have h1 : ∀ u : ℝ, fCos u * quadForm y z u
      = ∑ i, ∑ j, z i * z j * (fCos u * Real.cos (2 * π * (y i - y j) * u)) := by
    intro u
    unfold Distinct839.Majorant.quadForm
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  simp_rw [h1]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    Continuous.intervalIntegrable (continuous_finsetSum _ fun j _ => by fun_prop) _ _]
  refine sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum fun j _ =>
    Continuous.intervalIntegrable (by fun_prop) _ _]
  refine sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, ← Distinct839.K_eq_integral]

/-- The quadratic form of the kernel is nonnegative (`K` is a positive definite function). -/
theorem kernel_form_nonneg {ι : Type} [Fintype ι] (y z : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, z i * z j * K (y i - y j) := by
  rw [kernel_form_eq_integral]
  exact intervalIntegral.integral_nonneg (by norm_num) fun u _ =>
    mul_nonneg (Distinct839.fCos_pos u).le (quadForm_nonneg y z u)

/-- The same integral with the window extended by zero outside `[-1/2, 1/2]`. -/
theorem integral_fWin_mul (F : ℝ → ℝ) :
    ∫ u, fWin u * F u = ∫ u in (-(1 : ℝ) / 2)..(1 / 2), fCos u * F u := by
  have e : (fun u : ℝ => fWin u * F u)
      = Set.indicator (Set.Icc (-(1 : ℝ) / 2) (1 / 2)) (fun u => fCos u * F u) := by
    funext u
    unfold Distinct839.fWin
    by_cases h : |u| ≤ 1 / 2
    · have hu : u ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) := by
        rw [abs_le] at h
        exact ⟨by linarith [h.1], h.2⟩
      rw [if_pos h, Set.indicator_of_mem hu]
    · have hu : u ∉ Set.Icc (-(1 : ℝ) / 2) (1 / 2) := fun hu => h (by
        rw [abs_le]
        exact ⟨by linarith [hu.1], hu.2⟩)
      rw [if_neg h, Set.indicator_of_notMem hu, zero_mul]
  rw [e, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num)]

/-- **The kernel matrix is bounded by `c/2` on separated sets**: for a chain with gaps at least
`17/20` and every subset `S`, `∑_{i,j ∈ S} x_i K(y_i - y_j) x_j ≤ (c/2) ∑_{i ∈ S} x_i²`. -/
theorem kernel_form_le (ℓ : ℕ) (y : Fin ℓ → ℝ) (hsep : ∀ i j, i < j → sep ≤ y j - y i)
    (S : Finset (Fin ℓ)) (x : Fin ℓ → ℝ) :
    ∑ i ∈ S, ∑ j ∈ S, x i * K (y i - y j) * x j ≤ clipC / 2 * ∑ i ∈ S, x i ^ 2 := by
  -- extend `x` by zero outside `S`
  obtain ⟨z, hz⟩ : ∃ z : Fin ℓ → ℝ, ∀ i, z i = if i ∈ S then x i else 0 := ⟨_, fun _ => rfl⟩
  have e1 : ∑ i ∈ S, ∑ j ∈ S, x i * K (y i - y j) * x j
      = ∑ i, ∑ j, z i * z j * K (y i - y j) := by
    have hin : ∀ i, ∑ j, z i * z j * K (y i - y j)
        = if i ∈ S then ∑ j ∈ S, x i * K (y i - y j) * x j else 0 := by
      intro i
      by_cases hi : i ∈ S
      · rw [if_pos hi, hz i, if_pos hi, ← univ_inter S, ← sum_ite_mem]
        refine sum_congr rfl fun j _ => ?_
        rw [hz j]
        split_ifs <;> ring
      · rw [if_neg hi, hz i, if_neg hi]
        simp
    rw [sum_congr rfl fun i _ => hin i, sum_ite_mem, univ_inter]
  have e2 : ∑ i ∈ S, x i ^ 2 = ∑ i, z i ^ 2 := by
    rw [← univ_inter S, ← sum_ite_mem]
    refine sum_congr rfl fun i _ => ?_
    rw [hz i]
    split_ifs <;> simp
  have hsep' : ∀ i j : Fin ℓ, i ≠ j → sep ≤ |y i - y j| := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · have := hsep i j h
      rw [abs_sub_comm]
      exact this.trans (le_abs_self _)
    · exact (hsep j i h).trans (le_abs_self _)
  have hmeas : Measurable fWin := by
    unfold Distinct839.fWin
    exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
      Distinct839.Kernel.continuous_fCos.measurable measurable_const
  have h0 : ∀ u, 0 ≤ fWin u := by
    intro u
    unfold Distinct839.fWin
    split_ifs
    · exact (Distinct839.fCos_pos u).le
    · exact le_rfl
  have hle : ∀ u, fWin u ≤ gMaj u := by
    intro u
    unfold Distinct839.fWin
    split_ifs with h
    · exact Distinct839.majorantPointwise u h
    · unfold Distinct839.gMaj
      exact mul_nonneg (by norm_num [Distinct839.gammaM]) (sq_nonneg _)
  have hSB := Distinct839.separatedBound (Fin ℓ) y z fWin hsep' hmeas h0 hle
  have hint : ∫ u, fWin u * (∑ i, ∑ j, z i * z j * Real.cos (2 * π * (y i - y j) * u))
      = ∑ i, ∑ j, z i * z j * K (y i - y j) := by
    rw [kernel_form_eq_integral]
    exact integral_fWin_mul (quadForm y z)
  rw [hint] at hSB
  have hL : LMaj ≤ 16711 / 10000 := Distinct839.lMajBound
  have hz2 : 0 ≤ ∑ i, z i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  rw [e1, e2]
  have hc : clipC / 2 = 67 / 40 := by norm_num [Distinct839.clipC]
  rw [hc]
  nlinarith

/-! ## Positive semidefiniteness -/

/-- A real symmetric matrix with nonnegative quadratic form is positive semidefinite as a complex
matrix. -/
theorem posSemidef_of_real {n : Type*} [Fintype n] [DecidableEq n] (B : n → n → ℝ)
    (hsymm : ∀ i j, B i j = B j i) (hQ : ∀ a : n → ℝ, 0 ≤ ∑ i, ∑ j, a i * B i j * a j) :
    (Matrix.of fun i j => ((B i j : ℝ) : ℂ)).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    simp [Matrix.conjTranspose_apply, hsymm j i]
  · have hterm : ∀ i j : n, star (x i) * (((B i j : ℝ) : ℂ) * x j)
        = (((x i).re * B i j * (x j).re + (x i).im * B i j * (x j).im : ℝ) : ℂ)
          + (((x i).re * B i j * (x j).im - (x i).im * B i j * (x j).re : ℝ) : ℂ) * Complex.I := by
      intro i j
      apply Complex.ext <;> simp <;> ring
    have hsum : star x ⬝ᵥ ((Matrix.of fun i j => ((B i j : ℝ) : ℂ)) *ᵥ x)
        = ∑ i, ∑ j, star (x i) * (((B i j : ℝ) : ℂ) * x j) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, mul_sum]
    have hanti : ∑ i, ∑ j, ((x i).re * B i j * (x j).im - (x i).im * B i j * (x j).re) = 0 := by
      have h1 : ∑ i, ∑ j, (x i).im * B i j * (x j).re = ∑ i, ∑ j, (x i).re * B i j * (x j).im := by
        rw [sum_comm]
        exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hsymm j i]; ring
      simp only [sum_sub_distrib]
      rw [h1, sub_self]
    have key : star x ⬝ᵥ ((Matrix.of fun i j => ((B i j : ℝ) : ℂ)) *ᵥ x)
        = (((∑ i, ∑ j, (x i).re * B i j * (x j).re)
            + ∑ i, ∑ j, (x i).im * B i j * (x j).im : ℝ) : ℂ) := by
      rw [hsum, sum_congr rfl fun i _ => sum_congr rfl fun j _ => hterm i j]
      simp only [sum_add_distrib, ← sum_mul, ← Complex.ofReal_sum]
      rw [hanti]
      simp
    rw [key]
    exact Complex.zero_le_real.mpr (add_nonneg (hQ _) (hQ _))

/-- **The weighted kernel matrix of a labelled configuration is positive semidefinite.** -/
theorem kernelMatrix_posSemidef (ℓ : ℕ) (y : Fin ℓ → ℝ) (lab : Fin ℓ → Fin 2) :
    (Matrix.of fun i j : Fin ℓ =>
      ((Real.sqrt (mulOf (lab i) * mulOf (lab j)) * K (y i - y j) : ℝ) : ℂ)).PosSemidef := by
  refine posSemidef_of_real (fun i j => Real.sqrt (mulOf (lab i) * mulOf (lab j)) * K (y i - y j))
    (fun i j => ?_) (fun a => ?_)
  · have hK : K (y i - y j) = K (y j - y i) := by
      rw [← Distinct839.K_neg (y j - y i)]
      congr 1
      ring
    rw [hK, mul_comm (mulOf (lab i))]
  · have h := kernel_form_nonneg y (fun i => a i * Real.sqrt (mulOf (lab i)))
    refine h.trans (le_of_eq ?_)
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [Real.sqrt_mul (mulOf_nonneg (lab i))]
    ring

/-! ## The bridge -/

/-- **A certificate in the sense of the Gram bound is a pair-energy certificate for all
pairs.** -/
theorem GramCert.toPairCertAll {x₁ x₂ b : ℝ} (h : GramCert x₁ x₂ b) : PairCertAll x₁ x₂ b :=
  GramCert.toPairCertAll_of kernelMatrix_posSemidef kernel_form_le h

/-- **Ceiling for the certificates of the Gram bound** (window of `Distinct839`): no triple for
which the finite Gram theorem holds gives more than `0.83998`. -/
theorem ceiling_gram {x₁ x₂ b : ℝ} (h : GramCert x₁ x₂ b) (hb : 0 ≤ b)
    (hD : 0 < 2 - 2 * x₁ + x₂) :
    (3 - energyC + x₂ - x₁ - b) / (2 - 2 * x₁ + x₂) < 83998 / 100000 :=
  ceiling_all h.toPairCertAll hb hD

end Ceilings
