/-
Distinct839/Kernel/Trig.lean — correctness of the rational sine and cosine enclosures.

* `piLo < π < piHi` (from Mathlib's `Real.pi_gt_d20`, `Real.pi_lt_d20`);
* `dyLo x ≤ x ≤ dyHi x`;
* `trigEncl_holds`: for `j < H/2` and `r = (2j+1)/(2H)`, the record `trigEncl j` encloses
  `sin(π r)/π` and `cos(π r)`. Here `0 < π r ≤ π/2`, `sin` is increasing and `cos` decreasing on
  `[0, π/2]`, and the alternating Taylor bounds of `Distinct839/Kernel/Taylor.lean` apply;
* `sin_cos_mid_low`, `sin_cos_mid_high`: reduction of the cell midpoint `t = (2k+1)/(2H)` modulo one
  and reflection `r ↦ 1 - r`; up to the common sign `(-1)^⌊k/H⌋` the pair `(sin(π t)/π, cos(π t))`
  is `(sin(π r)/π, ±cos(π r))` with `r < 1/2`.
-/
import Distinct839.Kernel.Compute

noncomputable section

open Real

namespace Distinct839.Kernel

/-! ## Rational bounds for `π` -/

lemma piLo_lt_pi : ((piLo : ℚ) : ℝ) < π := by
  have h := Real.pi_gt_d20
  have e : ((piLo : ℚ) : ℝ) = 3.14159265358979323846 := by
    rw [piLo]
    norm_num
  rw [e]
  exact h

lemma pi_lt_piHi : π < ((piHi : ℚ) : ℝ) := by
  have h := Real.pi_lt_d20
  have e : ((piHi : ℚ) : ℝ) = 3.14159265358979323847 := by
    rw [piHi]
    norm_num
  rw [e]
  exact h

lemma piLo_pos : (0 : ℝ) < ((piLo : ℚ) : ℝ) := by
  have : (0 : ℚ) < piLo := by rw [piLo]; norm_num
  exact_mod_cast this

lemma piHi_pos : (0 : ℝ) < ((piHi : ℚ) : ℝ) := pi_pos.trans pi_lt_piHi

/-! ## Dyadic rounding -/

lemma dyLo_le (x : ℚ) : dyLo x ≤ x := by
  unfold dyLo
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

lemma le_dyHi (x : ℚ) : x ≤ dyHi x := by
  unfold dyHi
  rw [le_div_iff₀ (by positivity)]
  exact (Int.lt_floor_add_one _).le

lemma cast_dyLo_le {x : ℚ} {y : ℝ} (h : (x : ℝ) ≤ y) : ((dyLo x : ℚ) : ℝ) ≤ y :=
  le_trans (by exact_mod_cast dyLo_le x) h

lemma le_cast_dyHi {x : ℚ} {y : ℝ} (h : y ≤ (x : ℝ)) : y ≤ ((dyHi x : ℚ) : ℝ) :=
  le_trans h (by exact_mod_cast le_dyHi x)

/-! ## Correctness of `trigEncl` -/

/-- `e` encloses `S` (a value of `± sin(π t)/π`) and `C` (a value of `± cos(π t)`). -/
def TrigEncl.Holds (e : TrigEncl) (S C : ℝ) : Prop :=
  ((e.sl : ℚ) : ℝ) ≤ S ∧ S ≤ ((e.su : ℚ) : ℝ) ∧ ((e.cl : ℚ) : ℝ) ≤ C ∧ C ≤ ((e.cu : ℚ) : ℝ)

/-- Reflection changes the sign of the cosine part. -/
lemma TrigEncl.Holds.reflect {e : TrigEncl} {S C : ℝ} (h : e.Holds S C) :
    e.reflect.Holds S (-C) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, ?_, ?_⟩
  · simp only [TrigEncl.reflect, Rat.cast_neg]
    linarith
  · simp only [TrigEncl.reflect, Rat.cast_neg]
    linarith

/-- For `j < H/2` the record `trigEncl j` encloses `sin(π r)/π` and `cos(π r)`,
`r = (2j+1)/(2H)`. -/
theorem trigEncl_holds {j : ℕ} (hj : j < 8192) :
    (trigEncl j).Holds (Real.sin (π * ((2 * j + 1) / 32768)) / π)
      (Real.cos (π * ((2 * j + 1) / 32768))) := by
  set r : ℝ := (2 * j + 1) / 32768 with hr_def
  have hrq : (((2 * j + 1) / 32768 : ℚ) : ℝ) = r := by push_cast; rfl
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 16383 / 32768 := by
    have : (j : ℝ) ≤ 8191 := by exact_mod_cast Nat.le_of_lt_succ hj
    rw [hr_def]
    linarith
  -- the evaluation points `xl = piLo·r ≤ π r ≤ xu = piHi·r ≤ π/2`
  set xl : ℝ := ((piLo : ℚ) : ℝ) * r with hxl
  set xu : ℝ := ((piHi : ℚ) : ℝ) * r with hxu
  have hxlq : ((piLo * ((2 * j + 1) / 32768) : ℚ) : ℝ) = xl := by rw [Rat.cast_mul, hrq]
  have hxuq : ((piHi * ((2 * j + 1) / 32768) : ℚ) : ℝ) = xu := by rw [Rat.cast_mul, hrq]
  have hxl0 : 0 ≤ xl := (mul_pos piLo_pos hr0).le
  have hxl1 : xl ≤ π * r := mul_le_mul_of_nonneg_right piLo_lt_pi.le hr0.le
  have hxu0 : π * r ≤ xu := mul_le_mul_of_nonneg_right pi_lt_piHi.le hr0.le
  have hxu1 : xu ≤ π / 2 := by
    have h1 : xu ≤ ((piHi : ℚ) : ℝ) * (16383 / 32768) :=
      mul_le_mul_of_nonneg_left hr1 piHi_pos.le
    have h2 : ((piHi : ℚ) : ℝ) * (16383 / 32768) ≤ ((piLo : ℚ) : ℝ) / 2 := by
      have : piHi * (16383 / 32768) ≤ piLo / 2 := by rw [piHi, piLo]; norm_num
      have h' := (Rat.cast_le (K := ℝ)).mpr this
      push_cast at h'
      exact h'
    linarith [piLo_lt_pi]
  have hpr0 : 0 ≤ π * r := (mul_pos pi_pos hr0).le
  have hxuπ : xu ≤ π := by linarith [pi_pos]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- lower bound for `sin(π r)/π`
    show ((dyLo (sinPoly 10 (piLo * ((2 * j + 1) / 32768)) / piHi) : ℚ) : ℝ) ≤ _
    apply cast_dyLo_le
    rw [Rat.cast_div, sinPoly_cast, hxlq]
    have hsin0 : 0 ≤ Real.sin (π * r) := sin_nonneg_of_nonneg_of_le_pi hpr0 (by linarith)
    rcases le_or_gt (sinPoly 10 xl) 0 with hneg | hpos
    · have h1 : sinPoly 10 xl / ((piHi : ℚ) : ℝ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hneg piHi_pos.le
      have h2 : 0 ≤ Real.sin (π * r) / π := div_nonneg hsin0 pi_pos.le
      linarith
    · calc sinPoly 10 xl / ((piHi : ℚ) : ℝ) ≤ sinPoly 10 xl / π :=
            div_le_div_of_nonneg_left hpos.le pi_pos pi_lt_piHi.le
        _ ≤ Real.sin xl / π := by
            gcongr
            exact sinPoly_le_sin (by decide) (by norm_num) hxl0
        _ ≤ Real.sin (π * r) / π := by
            gcongr
            exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) (by linarith) hxl1
  · -- upper bound for `sin(π r)/π`
    show _ ≤ ((dyHi (sinPoly 11 (piHi * ((2 * j + 1) / 32768)) / piLo) : ℚ) : ℝ)
    apply le_cast_dyHi
    rw [Rat.cast_div, sinPoly_cast, hxuq]
    have hs1 : Real.sin xu ≤ sinPoly 11 xu := sin_le_sinPoly (by decide) (by linarith)
    have hs0 : 0 ≤ Real.sin xu := sin_nonneg_of_nonneg_of_le_pi (by linarith) hxuπ
    calc Real.sin (π * r) / π ≤ Real.sin xu / π := by
          gcongr
          exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hxu1 hxu0
      _ ≤ sinPoly 11 xu / π := by gcongr
      _ ≤ sinPoly 11 xu / ((piLo : ℚ) : ℝ) :=
          div_le_div_of_nonneg_left (by linarith) piLo_pos piLo_lt_pi.le
  · -- lower bound for `cos(π r)`
    show ((dyLo (cosPoly 10 (piHi * ((2 * j + 1) / 32768))) : ℚ) : ℝ) ≤ _
    apply cast_dyLo_le
    rw [cosPoly_cast, hxuq]
    calc cosPoly 10 xu ≤ Real.cos xu := cosPoly_le_cos (by decide) (by norm_num) (by linarith)
      _ ≤ Real.cos (π * r) := cos_le_cos_of_nonneg_of_le_pi hpr0 hxuπ hxu0
  · -- upper bound for `cos(π r)`
    show _ ≤ ((dyHi (cosPoly 11 (piLo * ((2 * j + 1) / 32768))) : ℚ) : ℝ)
    apply le_cast_dyHi
    rw [cosPoly_cast, hxlq]
    calc Real.cos (π * r) ≤ Real.cos xl :=
          cos_le_cos_of_nonneg_of_le_pi hxl0 (by linarith) hxl1
      _ ≤ cosPoly 11 xl := cos_le_cosPoly (by decide) hxl0

/-! ## Reduction of the midpoint modulo one -/

lemma neg_one_pow_sq (q : ℕ) : ((-1 : ℝ) ^ q) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

/-- Midpoints in the first half of a period: `t = q + r`, `r = (2j+1)/(2H)`, `j = k mod H < H/2`. -/
lemma sin_cos_mid_low (k : ℕ) :
    let σ : ℝ := (-1) ^ (k / 16384)
    let t : ℝ := (2 * k + 1) / 32768
    let r : ℝ := (2 * ((k % 16384 : ℕ) : ℝ) + 1) / 32768
    σ * (Real.sin (π * t) / π) = Real.sin (π * r) / π ∧
      σ * Real.cos (π * t) = Real.cos (π * r) := by
  intro σ t r
  have hk : (k : ℝ) = 16384 * ((k / 16384 : ℕ) : ℝ) + ((k % 16384 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod k 16384).symm
  have ht : π * t = π * r + ((k / 16384 : ℕ) : ℝ) * π := by
    simp only [t, r]
    rw [hk]
    ring
  have hσ : σ * σ = 1 := by rw [← sq]; exact neg_one_pow_sq _
  rw [ht, Real.sin_add_nat_mul_pi, Real.cos_add_nat_mul_pi]
  constructor
  · rw [← mul_div_assoc, ← mul_assoc, hσ, one_mul]
  · rw [← mul_assoc, hσ, one_mul]

/-- Midpoints in the second half of a period: `t = q + 1 - r'`, `r' = (2j'+1)/(2H)`,
`j' = H - 1 - (k mod H) < H/2`. -/
lemma sin_cos_mid_high (k : ℕ) :
    let σ : ℝ := (-1) ^ (k / 16384)
    let t : ℝ := (2 * k + 1) / 32768
    let r : ℝ := (2 * ((16383 - k % 16384 : ℕ) : ℝ) + 1) / 32768
    σ * (Real.sin (π * t) / π) = Real.sin (π * r) / π ∧
      σ * Real.cos (π * t) = -Real.cos (π * r) := by
  intro σ t r
  have hk : (k : ℝ) = 16384 * ((k / 16384 : ℕ) : ℝ) + ((k % 16384 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod k 16384).symm
  have hlt : k % 16384 < 16384 := Nat.mod_lt _ (by norm_num)
  have hsub : ((16383 - k % 16384 : ℕ) : ℝ) = 16383 - ((k % 16384 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have ht : π * t = ((k / 16384 + 1 : ℕ) : ℝ) * π - π * r := by
    simp only [t, r]
    rw [hk, hsub]
    push_cast
    ring
  have hσ : σ * σ = 1 := by rw [← sq]; exact neg_one_pow_sq _
  rw [ht, Real.sin_nat_mul_pi_sub, Real.cos_nat_mul_pi_sub, pow_succ]
  constructor
  · have : σ * (-(σ * -1 * Real.sin (π * r)) / π) = (σ * σ) * (Real.sin (π * r) / π) := by ring
    rw [this, hσ, one_mul]
  · have : σ * (σ * -1 * Real.cos (π * r)) = -((σ * σ) * Real.cos (π * r)) := by ring
    rw [this, hσ, one_mul]

end Distinct839.Kernel
