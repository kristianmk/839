/-
Distinct839/Window/Trig.lean — trigonometric integrals over one period `[-1/2, 1/2]`.

The window `fCos u = 1 + ∑ a_j cos(2π j u)` is a trigonometric polynomial. Everything that is needed
about its integrals follows from four facts, proved here for the frequencies `cosN n u = cos(2π n u)`,
`sinN n u = sin(2π n u)` with `n` a natural number:

* `integral_cosN`: `∫ cosN n = 0` for `n ≠ 0`;
* `integral_cosN_mul_cosN`, `integral_sinN_mul_sinN`: orthogonality, `∫ cosN n · cosN m = δ_{nm}/2`;
* `integral_quad_mul_cosN`: `∫ (1/2 - s)²/2 · cosN n s ds = (-1)^n / (4 π² n²)`.

They are then summed over a finite family of frequencies `j + 1`, `j : Fin N`
(`integral_sum_cos`, `integral_sq_sum_cos`, `integral_sq_sum_sin`, `integral_sum_cos_mul_cosN`).
All integrals are interval integrals `∫ s in (-(1:ℝ)/2)..(1/2), _`, the form used by the upstream
window functional `Zeta23.XiPrime.cWin`. Everything here is a helper, in `Distinct839.Window`.
-/
import Distinct839.Defs

open Real MeasureTheory intervalIntegral
open scoped BigOperators

noncomputable section

namespace Distinct839.Window

/-- `cos(2π n u)`. -/
def cosN (n : ℕ) (u : ℝ) : ℝ := Real.cos (2 * π * n * u)

/-- `sin(2π n u)`. -/
def sinN (n : ℕ) (u : ℝ) : ℝ := Real.sin (2 * π * n * u)

lemma continuous_cosN (n : ℕ) : Continuous (cosN n) := by unfold cosN; fun_prop

lemma continuous_sinN (n : ℕ) : Continuous (sinN n) := by unfold sinN; fun_prop

lemma abs_cosN_le_one (n : ℕ) (u : ℝ) : |cosN n u| ≤ 1 := Real.abs_cos_le_one _

lemma abs_sinN_le_one (n : ℕ) (u : ℝ) : |sinN n u| ≤ 1 := Real.abs_sin_le_one _

lemma cosN_neg (n : ℕ) (u : ℝ) : cosN n (-u) = cosN n u := by
  unfold cosN; rw [mul_neg, Real.cos_neg]

lemma cosN_half (n : ℕ) : cosN n (1 / 2) = (-1) ^ n := by
  unfold cosN
  rw [show 2 * π * (n : ℝ) * (1 / 2) = n * π by ring, Real.cos_nat_mul_pi]

lemma sinN_half (n : ℕ) : sinN n (1 / 2) = 0 := by
  unfold sinN
  rw [show 2 * π * (n : ℝ) * (1 / 2) = n * π by ring, Real.sin_nat_mul_pi]

lemma hasDerivAt_cosN (n : ℕ) (u : ℝ) :
    HasDerivAt (cosN n) (-(2 * π * n * sinN n u)) u := by
  have h := (Real.hasDerivAt_cos (2 * π * n * u)).comp u ((hasDerivAt_id u).const_mul (2 * π * (n : ℝ)))
  simp only [mul_one] at h
  refine h.congr_deriv ?_
  unfold sinN
  ring

lemma hasDerivAt_sinN (n : ℕ) (u : ℝ) :
    HasDerivAt (sinN n) (2 * π * n * cosN n u) u := by
  have h := (Real.hasDerivAt_sin (2 * π * n * u)).comp u ((hasDerivAt_id u).const_mul (2 * π * (n : ℝ)))
  simp only [mul_one] at h
  refine h.congr_deriv ?_
  unfold cosN
  ring

/-! ### The basic integrals -/

/-- `∫_{-1/2}^{1/2} cos(2π m s) ds = 0` for an integer `m ≠ 0`. -/
lemma integral_cos_int {m : ℤ} (hm : m ≠ 0) :
    ∫ s in (-(1:ℝ)/2)..(1/2), Real.cos (2 * π * m * s) = 0 := by
  have hc : (2 * π * (m : ℝ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (Int.cast_ne_zero.mpr hm)
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos]
  have h1 : 2 * π * (m : ℝ) * (1 / 2) = m * π := by ring
  have h2 : 2 * π * (m : ℝ) * (-1 / 2) = -(m * π) := by ring
  rw [h1, h2, Real.sin_neg, Real.sin_int_mul_pi]
  simp

/-- `∫ cos(2π n s) ds = 0` over a period, `n ≠ 0`. -/
lemma integral_cosN {n : ℕ} (hn : n ≠ 0) : ∫ s in (-(1:ℝ)/2)..(1/2), cosN n s = 0 := by
  have h := integral_cos_int (m := (n : ℤ)) (by exact_mod_cast hn)
  simpa [cosN] using h

lemma integral_one : ∫ _s in (-(1:ℝ)/2)..(1/2), (1:ℝ) = 1 := by
  rw [intervalIntegral.integral_const, smul_eq_mul]; norm_num

/-- Orthogonality of the cosines: `∫ cos(2π n s) cos(2π m s) ds = δ_{nm}/2` for `n, m ≥ 1`. -/
lemma integral_cosN_mul_cosN {n m : ℕ} (_hn : n ≠ 0) (hm : m ≠ 0) :
    ∫ s in (-(1:ℝ)/2)..(1/2), cosN n s * cosN m s = if n = m then 1 / 2 else 0 := by
  have hprod : ∀ s : ℝ, cosN n s * cosN m s
      = (1 / 2) * Real.cos (2 * π * (((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * s)
        + (1 / 2) * Real.cos (2 * π * (((n : ℤ) + (m : ℤ) : ℤ) : ℝ) * s) := by
    intro s
    unfold cosN
    push_cast
    rw [show 2 * π * ((n : ℝ) - m) * s = 2 * π * n * s - 2 * π * m * s by ring,
      show 2 * π * ((n : ℝ) + m) * s = 2 * π * n * s + 2 * π * m * s by ring,
      Real.cos_sub, Real.cos_add]
    ring
  have hsum : ((n : ℤ) + (m : ℤ)) ≠ 0 := by omega
  have hi : ∀ k : ℤ, IntervalIntegrable (fun s : ℝ => (1 / 2) * Real.cos (2 * π * (k : ℝ) * s))
      volume (-(1:ℝ)/2) (1/2) := fun k => (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (fun s _ => hprod s),
    intervalIntegral.integral_add (hi _) (hi _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_cos_int hsum]
  by_cases h : n = m
  · subst h
    simp only [sub_self, Int.cast_zero, mul_zero, zero_mul, Real.cos_zero, if_true]
    rw [integral_one]; ring
  · have hd : ((n : ℤ) - (m : ℤ)) ≠ 0 := by omega
    rw [integral_cos_int hd, if_neg h]; ring

/-- Orthogonality of the sines: `∫ sin(2π n s) sin(2π m s) ds = δ_{nm}/2` for `n, m ≥ 1`. -/
lemma integral_sinN_mul_sinN {n m : ℕ} (_hn : n ≠ 0) (hm : m ≠ 0) :
    ∫ s in (-(1:ℝ)/2)..(1/2), sinN n s * sinN m s = if n = m then 1 / 2 else 0 := by
  have hprod : ∀ s : ℝ, sinN n s * sinN m s
      = (1 / 2) * Real.cos (2 * π * (((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * s)
        - (1 / 2) * Real.cos (2 * π * (((n : ℤ) + (m : ℤ) : ℤ) : ℝ) * s) := by
    intro s
    unfold sinN
    push_cast
    rw [show 2 * π * ((n : ℝ) - m) * s = 2 * π * n * s - 2 * π * m * s by ring,
      show 2 * π * ((n : ℝ) + m) * s = 2 * π * n * s + 2 * π * m * s by ring,
      Real.cos_sub, Real.cos_add]
    ring
  have hsum : ((n : ℤ) + (m : ℤ)) ≠ 0 := by omega
  have hi : ∀ k : ℤ, IntervalIntegrable (fun s : ℝ => (1 / 2) * Real.cos (2 * π * (k : ℝ) * s))
      volume (-(1:ℝ)/2) (1/2) := fun k => (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (fun s _ => hprod s),
    intervalIntegral.integral_sub (hi _) (hi _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_cos_int hsum]
  by_cases h : n = m
  · subst h
    simp only [sub_self, Int.cast_zero, mul_zero, zero_mul, Real.cos_zero, if_true]
    rw [integral_one]; ring
  · have hd : ((n : ℤ) - (m : ℤ)) ≠ 0 := by omega
    rw [integral_cos_int hd, if_neg h]; ring

/-- `∫_{-1/2}^{1/2} (1/2 - s)²/2 ds = 1/6`. -/
lemma integral_quad : ∫ s in (-(1:ℝ)/2)..(1/2), (1 / 2 - s) ^ 2 / 2 = 1 / 6 := by
  have hd : ∀ s ∈ Set.uIcc (-(1:ℝ)/2) (1/2),
      HasDerivAt (fun s : ℝ => -(1 / 2 - s) ^ 3 / 6) ((1 / 2 - s) ^ 2 / 2) s := by
    intro s _
    have h := ((((hasDerivAt_id' s).const_sub (1 / 2 : ℝ)).pow 3).neg).div_const 6
    refine h.congr_deriv ?_
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun s : ℝ => (1 / 2 - s) ^ 2 / 2).intervalIntegrable _ _)]
  norm_num

/-- `∫_{-1/2}^{1/2} (1/2 - s)²/2 · cos(2π n s) ds = (-1)^n / (4 π² n²)` for `n ≥ 1`. -/
lemma integral_quad_mul_cosN {n : ℕ} (hn : n ≠ 0) :
    ∫ s in (-(1:ℝ)/2)..(1/2), (1 / 2 - s) ^ 2 / 2 * cosN n s
      = (-1) ^ n / (4 * π ^ 2 * (n : ℝ) ^ 2) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hc : (2 * π * (n : ℝ)) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hn'
  set c : ℝ := 2 * π * n with hcdef
  -- antiderivative: g sin/c + g' cos/c² - g'' sin/c³ with g = (1/2 - s)²/2
  have hd : ∀ s ∈ Set.uIcc (-(1:ℝ)/2) (1/2),
      HasDerivAt (fun s : ℝ => (1 / 2 - s) ^ 2 / 2 * sinN n s / c - (1 / 2 - s) * cosN n s / c ^ 2
          - sinN n s / c ^ 3) ((1 / 2 - s) ^ 2 / 2 * cosN n s) s := by
    intro s _
    have hg : HasDerivAt (fun s : ℝ => (1 / 2 - s) ^ 2 / 2) (-(1 / 2 - s)) s := by
      have h := (((hasDerivAt_id' s).const_sub (1 / 2 : ℝ)).pow 2).div_const 2
      refine h.congr_deriv ?_
      push_cast
      ring
    have hg1 : HasDerivAt (fun s : ℝ => 1 / 2 - s) (-1) s := (hasDerivAt_id s).const_sub (1 / 2)
    have hs := hasDerivAt_sinN n s
    have hco := hasDerivAt_cosN n s
    have h := (((hg.mul hs).div_const c).sub ((hg1.mul hco).div_const (c ^ 2))).sub
      (hs.div_const (c ^ 3))
    refine h.congr_deriv ?_
    rw [← hcdef]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((by fun_prop : Continuous fun s : ℝ => (1 / 2 - s) ^ 2 / 2).mul
      (continuous_cosN n)).intervalIntegrable _ _)]
  have hneg : (-(1:ℝ)/2) = -(1/2) := by ring
  have hs1 : sinN n (-(1:ℝ)/2) = 0 := by
    unfold sinN
    rw [show 2 * π * (n : ℝ) * (-1 / 2) = -(n * π) by ring, Real.sin_neg, Real.sin_nat_mul_pi,
      neg_zero]
  have hc1 : cosN n (-(1:ℝ)/2) = (-1) ^ n := by rw [hneg, cosN_neg, cosN_half]
  rw [sinN_half, cosN_half, hs1, hc1, hcdef]
  field_simp
  ring

/-! ### Finite trigonometric sums with frequencies `j + 1` -/

/-- Interval integral of a finite sum of continuous functions over `[-1/2, 1/2]`. -/
lemma integral_sum_fin {N : ℕ} (f : Fin N → ℝ → ℝ) (hf : ∀ j, Continuous (f j)) :
    ∫ s in (-(1:ℝ)/2)..(1/2), ∑ j, f j s = ∑ j, ∫ s in (-(1:ℝ)/2)..(1/2), f j s :=
  intervalIntegral.integral_finsetSum fun j _ => (hf j).intervalIntegrable _ _

section Sums

variable {N : ℕ} (b : Fin N → ℝ)

lemma continuous_sum_cos : Continuous fun s : ℝ => ∑ j : Fin N, b j * cosN (j.val + 1) s :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_cosN _)

lemma continuous_sum_sin : Continuous fun s : ℝ => ∑ j : Fin N, b j * sinN (j.val + 1) s :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_sinN _)

/-- `∫ ∑ b_j cos(2π (j+1) s) ds = 0`. -/
lemma integral_sum_cos :
    ∫ s in (-(1:ℝ)/2)..(1/2), ∑ j : Fin N, b j * cosN (j.val + 1) s = 0 := by
  rw [integral_sum_fin (fun j s => b j * cosN (j.val + 1) s)
    (fun _ => continuous_const.mul (continuous_cosN _))]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_cosN (Nat.succ_ne_zero _), mul_zero]

/-- `∫ (∑ b_j cos(2π (j+1) s)) cos(2π (k+1) s) ds = b_k / 2`. -/
lemma integral_sum_cos_mul_cosN (k : Fin N) :
    ∫ s in (-(1:ℝ)/2)..(1/2), (∑ j : Fin N, b j * cosN (j.val + 1) s) * cosN (k.val + 1) s
      = b k / 2 := by
  have h1 : ∀ s : ℝ, (∑ j : Fin N, b j * cosN (j.val + 1) s) * cosN (k.val + 1) s
      = ∑ j : Fin N, b j * (cosN (j.val + 1) s * cosN (k.val + 1) s) := by
    intro s; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [intervalIntegral.integral_congr (fun s _ => h1 s),
    integral_sum_fin (fun j s => b j * (cosN (j.val + 1) s * cosN (k.val + 1) s))
      (fun _ => continuous_const.mul ((continuous_cosN _).mul (continuous_cosN _)))]
  have h2 : ∀ j : Fin N, ∫ s in (-(1:ℝ)/2)..(1/2), b j * (cosN (j.val + 1) s * cosN (k.val + 1) s)
      = if j = k then b j / 2 else 0 := by
    intro j
    rw [intervalIntegral.integral_const_mul,
      integral_cosN_mul_cosN (Nat.succ_ne_zero _) (Nat.succ_ne_zero _)]
    by_cases h : j = k
    · subst h; rw [if_pos rfl, if_pos rfl]; ring
    · have : ¬ (j.val + 1 = k.val + 1) := fun h' => h (Fin.ext (by omega))
      rw [if_neg this, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl fun j _ => h2 j, Finset.sum_ite_eq' Finset.univ k]
  simp

/-- `∫ (∑ b_j cos(2π (j+1) s))² ds = ∑ b_j² / 2`. -/
lemma integral_sq_sum_cos :
    ∫ s in (-(1:ℝ)/2)..(1/2), (∑ j : Fin N, b j * cosN (j.val + 1) s) ^ 2
      = (∑ j : Fin N, b j ^ 2) / 2 := by
  have h1 : ∀ s : ℝ, (∑ j : Fin N, b j * cosN (j.val + 1) s) ^ 2
      = ∑ k : Fin N, b k * ((∑ j : Fin N, b j * cosN (j.val + 1) s) * cosN (k.val + 1) s) := by
    intro s; rw [sq, Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [intervalIntegral.integral_congr (fun s _ => h1 s),
    integral_sum_fin (fun k s => b k * ((∑ j : Fin N, b j * cosN (j.val + 1) s) * cosN (k.val + 1) s))
      (fun _ => continuous_const.mul ((continuous_sum_cos b).mul (continuous_cosN _))),
    Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_sum_cos_mul_cosN]
  ring

/-- `∫ (∑ b_j sin(2π (j+1) s)) sin(2π (k+1) s) ds = b_k / 2`. -/
lemma integral_sum_sin_mul_sinN (k : Fin N) :
    ∫ s in (-(1:ℝ)/2)..(1/2), (∑ j : Fin N, b j * sinN (j.val + 1) s) * sinN (k.val + 1) s
      = b k / 2 := by
  have h1 : ∀ s : ℝ, (∑ j : Fin N, b j * sinN (j.val + 1) s) * sinN (k.val + 1) s
      = ∑ j : Fin N, b j * (sinN (j.val + 1) s * sinN (k.val + 1) s) := by
    intro s; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [intervalIntegral.integral_congr (fun s _ => h1 s),
    integral_sum_fin (fun j s => b j * (sinN (j.val + 1) s * sinN (k.val + 1) s))
      (fun _ => continuous_const.mul ((continuous_sinN _).mul (continuous_sinN _)))]
  have h2 : ∀ j : Fin N, ∫ s in (-(1:ℝ)/2)..(1/2), b j * (sinN (j.val + 1) s * sinN (k.val + 1) s)
      = if j = k then b j / 2 else 0 := by
    intro j
    rw [intervalIntegral.integral_const_mul,
      integral_sinN_mul_sinN (Nat.succ_ne_zero _) (Nat.succ_ne_zero _)]
    by_cases h : j = k
    · subst h; rw [if_pos rfl, if_pos rfl]; ring
    · have : ¬ (j.val + 1 = k.val + 1) := fun h' => h (Fin.ext (by omega))
      rw [if_neg this, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl fun j _ => h2 j, Finset.sum_ite_eq' Finset.univ k]
  simp

/-- `∫ (∑ b_j sin(2π (j+1) s))² ds = ∑ b_j² / 2`. -/
lemma integral_sq_sum_sin :
    ∫ s in (-(1:ℝ)/2)..(1/2), (∑ j : Fin N, b j * sinN (j.val + 1) s) ^ 2
      = (∑ j : Fin N, b j ^ 2) / 2 := by
  have h1 : ∀ s : ℝ, (∑ j : Fin N, b j * sinN (j.val + 1) s) ^ 2
      = ∑ k : Fin N, b k * ((∑ j : Fin N, b j * sinN (j.val + 1) s) * sinN (k.val + 1) s) := by
    intro s; rw [sq, Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [intervalIntegral.integral_congr (fun s _ => h1 s),
    integral_sum_fin (fun k s => b k * ((∑ j : Fin N, b j * sinN (j.val + 1) s) * sinN (k.val + 1) s))
      (fun _ => continuous_const.mul ((continuous_sum_sin b).mul (continuous_sinN _))),
    Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_sum_sin_mul_sinN]
  ring

end Sums

end Distinct839.Window
