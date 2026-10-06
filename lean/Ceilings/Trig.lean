/-
Ceilings/Trig.lean — a rational upper bound for `(sin(π t)/π)²` at rational points.

For rational `t` let `ρ = reduce t ∈ [0, 1/2]` be the distance from `t` to the nearest integer, so
that `sin²(π t) = sin²(π ρ)`. The sine series with seven terms is an upper bound for `sin` on
`[0, ∞)` (`Distinct839.Kernel.sin_le_sinPoly`); with `π` replaced by the rational bounds
`piLo < π < piHi` in the terms of negative and of positive sign this gives
`sin(π ρ) ≤ π ρ · sincUp ρ` (`sin_le_mul_sincUp`), and therefore

    `(sin(π t)/π)² ≤ sUp t = dyHi ((ρ · sincUp ρ)²)`          (`sin_div_pi_sq_le`),

where `dyHi` rounds upwards to a multiple of `2⁻⁷⁰`. For `ρ ≤ 1/2` the relative error of the bound
is below `10⁻⁹`. The function `sUp` has period one (`sUp_add_intCast`). All functions are
computable on `ℚ`; nothing here depends on a window.
-/
import Distinct839.Kernel.Trig

noncomputable section

open Real

namespace Ceilings

open Distinct839.Kernel (piLo piHi dyHi sinPoly)

/-! ## The functions (computable) -/

/-- Upper bound for `sin(π r)/(π r)`, `r ≥ 0`: the series `∑_{k<7} (-1)^k (π r)^{2k}/(2k+1)!` with
`π` replaced by `piHi` in the positive terms and by `piLo` in the negative terms. -/
def sincUp (r : ℚ) : ℚ :=
  1 - (piLo * r) ^ 2 / 6 + ((piHi * r) ^ 2) ^ 2 / 120 - ((piLo * r) ^ 2) ^ 3 / 5040
    + ((piHi * r) ^ 2) ^ 4 / 362880 - ((piLo * r) ^ 2) ^ 5 / 39916800
    + ((piHi * r) ^ 2) ^ 6 / 6227020800

/-- Distance from `t` to the nearest integer. -/
def reduce (t : ℚ) : ℚ := if Int.fract t ≤ 1 / 2 then Int.fract t else 1 - Int.fract t

/-- Upper bound for `(sin(π t)/π)²`. -/
def sUp (t : ℚ) : ℚ := dyHi ((reduce t * sincUp (reduce t)) ^ 2)

/-! ## The sine bound -/

/-- The sine series with seven terms, written as `x` times a polynomial in `x²`. -/
lemma sinPoly_seven (x : ℝ) :
    sinPoly 7 x = x * (1 - x ^ 2 / 6 + (x ^ 2) ^ 2 / 120 - (x ^ 2) ^ 3 / 5040
      + (x ^ 2) ^ 4 / 362880 - (x ^ 2) ^ 5 / 39916800 + (x ^ 2) ^ 6 / 6227020800) := by
  simp only [sinPoly, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]
  ring

/-- `sin(π r) ≤ π r · sincUp r` for rational `r ≥ 0`. -/
theorem sin_le_mul_sincUp {r : ℚ} (hr : 0 ≤ r) :
    Real.sin (π * r) ≤ π * r * (sincUp r : ℝ) := by
  have hr' : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hx : 0 ≤ π * (r : ℝ) := mul_nonneg pi_pos.le hr'
  have hlo : 0 ≤ ((piLo : ℚ) : ℝ) * r := mul_nonneg Distinct839.Kernel.piLo_pos.le hr'
  have h1 : ((piLo : ℚ) : ℝ) * r ≤ π * r :=
    mul_le_mul_of_nonneg_right Distinct839.Kernel.piLo_lt_pi.le hr'
  have h2 : π * r ≤ ((piHi : ℚ) : ℝ) * r :=
    mul_le_mul_of_nonneg_right Distinct839.Kernel.pi_lt_piHi.le hr'
  -- `uL ≤ u ≤ uH`
  have hL : (((piLo : ℚ) : ℝ) * r) ^ 2 ≤ (π * r) ^ 2 := pow_le_pow_left₀ hlo h1 2
  have hH : (π * r) ^ 2 ≤ (((piHi : ℚ) : ℝ) * r) ^ 2 := pow_le_pow_left₀ hx h2 2
  have hL0 : 0 ≤ (((piLo : ℚ) : ℝ) * r) ^ 2 := sq_nonneg _
  have hu0 : 0 ≤ (π * (r : ℝ)) ^ 2 := sq_nonneg _
  have e : ((sincUp r : ℚ) : ℝ)
      = 1 - (((piLo : ℚ) : ℝ) * r) ^ 2 / 6 + ((((piHi : ℚ) : ℝ) * r) ^ 2) ^ 2 / 120
        - ((((piLo : ℚ) : ℝ) * r) ^ 2) ^ 3 / 5040 + ((((piHi : ℚ) : ℝ) * r) ^ 2) ^ 4 / 362880
        - ((((piLo : ℚ) : ℝ) * r) ^ 2) ^ 5 / 39916800
        + ((((piHi : ℚ) : ℝ) * r) ^ 2) ^ 6 / 6227020800 := by
    unfold sincUp
    push_cast
    ring
  have t2 := pow_le_pow_left₀ hu0 hH 2
  have t3 := pow_le_pow_left₀ hL0 hL 3
  have t4 := pow_le_pow_left₀ hu0 hH 4
  have t5 := pow_le_pow_left₀ hL0 hL 5
  have t6 := pow_le_pow_left₀ hu0 hH 6
  calc Real.sin (π * r) ≤ sinPoly 7 (π * r) :=
        Distinct839.Kernel.sin_le_sinPoly (by decide) hx
    _ = π * r * (1 - (π * r) ^ 2 / 6 + ((π * r) ^ 2) ^ 2 / 120 - ((π * r) ^ 2) ^ 3 / 5040
          + ((π * r) ^ 2) ^ 4 / 362880 - ((π * r) ^ 2) ^ 5 / 39916800
          + ((π * r) ^ 2) ^ 6 / 6227020800) := sinPoly_seven _
    _ ≤ π * r * (sincUp r : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ hx
        rw [e]
        linarith

/-! ## Reduction modulo one -/

lemma reduce_nonneg (t : ℚ) : 0 ≤ reduce t := by
  unfold reduce
  split_ifs with h
  · exact Int.fract_nonneg t
  · linarith [Int.fract_lt_one t]

lemma reduce_le_one (t : ℚ) : reduce t ≤ 1 := by
  unfold reduce
  split_ifs with h
  · linarith
  · linarith [Int.fract_nonneg t]

/-- `reduce` has period one. -/
lemma reduce_add_intCast (t : ℚ) (z : ℤ) : reduce (t + z) = reduce t := by
  unfold reduce
  rw [Int.fract_add_intCast]

/-- `sUp` has period one. -/
lemma sUp_add_intCast (t : ℚ) (z : ℤ) : sUp (t + z) = sUp t := by
  unfold sUp
  rw [reduce_add_intCast]

/-- `sin²(π t) = sin²(π · fract t)`. -/
lemma sin_sq_fract (t : ℚ) :
    Real.sin (π * t) ^ 2 = Real.sin (π * ((Int.fract t : ℚ) : ℝ)) ^ 2 := by
  have ht : (t : ℝ) = ((Int.fract t : ℚ) : ℝ) + ((⌊t⌋ : ℤ) : ℝ) := by
    have h := Int.fract_add_floor t
    exact_mod_cast h.symm
  rw [Real.sin_sq_eq_half_sub, Real.sin_sq_eq_half_sub]
  have e : 2 * (π * (t : ℝ)) = 2 * (π * ((Int.fract t : ℚ) : ℝ)) + ((⌊t⌋ : ℤ) : ℝ) * (2 * π) := by
    rw [ht]
    ring
  rw [e, Real.cos_add_int_mul_two_pi]

/-- `sin²(π t) = sin²(π · reduce t)`. -/
lemma sin_sq_reduce (t : ℚ) :
    Real.sin (π * t) ^ 2 = Real.sin (π * ((reduce t : ℚ) : ℝ)) ^ 2 := by
  rw [sin_sq_fract]
  unfold reduce
  split_ifs with h
  · rfl
  · have e : π * (((1 - Int.fract t : ℚ)) : ℝ) = π - π * ((Int.fract t : ℚ) : ℝ) := by
      push_cast
      ring
    rw [e, Real.sin_pi_sub]

/-- **The bound**: `(sin(π t)/π)² ≤ sUp t` for every rational `t`. -/
theorem sin_div_pi_sq_le (t : ℚ) : (Real.sin (π * t) / π) ^ 2 ≤ ((sUp t : ℚ) : ℝ) := by
  have h0 : (0 : ℝ) ≤ ((reduce t : ℚ) : ℝ) := by exact_mod_cast reduce_nonneg t
  have h1 : ((reduce t : ℚ) : ℝ) ≤ 1 := by exact_mod_cast reduce_le_one t
  have hs0 : 0 ≤ Real.sin (π * ((reduce t : ℚ) : ℝ)) :=
    sin_nonneg_of_nonneg_of_le_pi (mul_nonneg pi_pos.le h0)
      (by nlinarith [pi_pos])
  have hs1 := sin_le_mul_sincUp (reduce_nonneg t)
  have hdiv : Real.sin (π * ((reduce t : ℚ) : ℝ)) / π
      ≤ ((reduce t : ℚ) : ℝ) * ((sincUp (reduce t) : ℚ) : ℝ) := by
    rw [div_le_iff₀ pi_pos]
    linarith
  have hsq : (Real.sin (π * t) / π) ^ 2 = (Real.sin (π * ((reduce t : ℚ) : ℝ)) / π) ^ 2 := by
    rw [div_pow, div_pow, sin_sq_reduce]
  rw [hsq]
  unfold sUp
  refine Distinct839.Kernel.le_cast_dyHi ?_
  push_cast
  exact pow_le_pow_left₀ (div_nonneg hs0 pi_pos.le) hdiv 2

/-- `sUp` is nonnegative. -/
lemma sUp_nonneg (t : ℚ) : 0 ≤ sUp t := by
  have h := (sq_nonneg (Real.sin (π * t) / π)).trans (sin_div_pi_sq_le t)
  exact_mod_cast h

end Ceilings
