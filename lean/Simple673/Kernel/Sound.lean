/-
Simple673/Kernel/Sound.lean — soundness of the kernel table: `TableSound kTab`.

For the cell `k` with midpoint `t = (2k+1)/(2H)`, `H = 16384`:
* `t` is not an integer, so `K(t) = sin(π t)/π · Q(t)` and
  `K'(t) = cos(π t) Q(t) + sin(π t)/π · Q'(t)` (`Simple673/Kernel/Closed.lean`), and the
  rational functions `ratQ`, `derQ` of `Simple673/Kernel/Compute.lean` are `Q`, `Q'` at `t`;
* the enclosure `e` gives `ℓ = e.sl·|Q(t)| ≤ |K(t)|` and `|K'(t)| ≤ max(|dl|, |du|)`;
* the cell estimate `abs_K_ge_of_abs_sub_le` (mean value theorem, `|K'| ≤ π`, `|K''| ≤ π²`) gives
  `|K(s)| ≥ ℓ - (1/(2H)) min(π, D + π²/(2H))` for `|s - t| ≤ 1/(2H)`;
* the table entry is `⌊V · low²⌋` with `low` the positive part of that bound and `π ≤ piHi`.

The trigonometric enclosures, the bounds for `π` and the reduction of the midpoint modulo one are
those of `Distinct839/Kernel/Trig.lean`; they do not depend on the window.
-/
import Simple673.Kernel.Closed
import Simple673.Kernel.Compute
import Distinct839.Kernel.Trig

noncomputable section

open Real

namespace Simple673.Kernel

/-- The rational upper bound `Distinct839.Kernel.piHi` for `π`, as a real number. -/
local notation "piHiR" => ((Distinct839.Kernel.piHi : ℚ) : ℝ)

/-! ## Rational and real versions of `Q` and `Q'` -/

lemma ratQ_cast (x : ℚ) : ((ratQ x : ℚ) : ℝ) = Qrat (x : ℝ) := by
  simp only [ratQ, Qrat, aC]
  push_cast
  rfl

lemma derQ_cast (x : ℚ) : ((derQ x : ℚ) : ℝ) = Qder (x : ℝ) := by
  simp only [derQ, Qder, aC]
  push_cast
  rfl

/-! ## Elementary facts -/

/-- A product `c·x` with `a ≤ x ≤ b` lies between `c·a` and `c·b`. -/
lemma mul_mem_min_max {a b x : ℝ} (c : ℝ) (ha : a ≤ x) (hb : x ≤ b) :
    min (c * a) (c * b) ≤ c * x ∧ c * x ≤ max (c * a) (c * b) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left ha hc),
      (mul_le_mul_of_nonneg_left hb hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hb hc),
      (mul_le_mul_of_nonpos_left ha hc).trans (le_max_left _ _)⟩

/-- No cell midpoint `(2k+1)/(2H)` is an integer. -/
lemma mid_notInt (k : ℕ) : ∀ n : ℤ, ((2 * k + 1) / 32768 : ℝ) ≠ n := by
  intro n h
  have h2 : ((2 * k + 1 : ℤ) : ℝ) = ((32768 * n : ℤ) : ℝ) := by
    push_cast
    rw [← h]
    ring
  have h3 : (2 * k + 1 : ℤ) = 32768 * n := by exact_mod_cast h2
  omega

/-! ## One cell -/

lemma cellVal_eq (e : Distinct839.Kernel.TrigEncl) (k : ℕ) :
    cellVal e k = ⌊cellLow e k * cellLow e k * 268435456⌋₊ := rfl

/-- Soundness of one table entry: if `e` encloses `σ sin(π t)/π` and `σ cos(π t)` at the midpoint
`t = (2k+1)/(2H)`, for a sign `σ` with `σ² = 1`, then `cellVal e k / V ≤ K(s)²` whenever
`|s - t| ≤ 1/(2H)`. -/
theorem cellVal_sound (e : Distinct839.Kernel.TrigEncl) (k : ℕ) (σ : ℝ) (hσ : σ * σ = 1)
    (he : e.Holds (σ * (Real.sin (π * ((2 * k + 1) / 32768)) / π))
      (σ * Real.cos (π * ((2 * k + 1) / 32768))))
    {s : ℝ} (hs : |s - (2 * k + 1) / 32768| ≤ 1 / 32768) :
    ((cellVal e k : ℕ) : ℝ) / 268435456 ≤ K s ^ 2 := by
  set t : ℝ := (2 * k + 1) / 32768 with ht_def
  have hnot : ∀ n : ℤ, t ≠ n := mid_notInt k
  have htq : ((((2 * k + 1) / 32768 : ℚ)) : ℝ) = t := by push_cast; rfl
  have hR : ((ratQ ((2 * k + 1) / 32768) : ℚ) : ℝ) = Qrat t := by rw [ratQ_cast, htq]
  have hD : ((derQ ((2 * k + 1) / 32768) : ℚ) : ℝ) = Qder t := by rw [derQ_cast, htq]
  have hσabs : |σ| = 1 := by
    have h0 : |σ| * |σ| = 1 := by rw [← abs_mul, hσ, abs_one]
    nlinarith [abs_nonneg σ]
  obtain ⟨h1, h2, h3, h4⟩ := he
  set S : ℝ := σ * (Real.sin (π * t) / π) with hS_def
  set C : ℝ := σ * Real.cos (π * t) with hC_def
  set R : ℝ := Qrat t with hR_def
  set D : ℝ := Qder t with hD_def
  -- `|K(t)| = |S| |Q(t)|` and `|K'(t)| = |C Q(t) + S Q'(t)|`
  have hKt : |K t| = |S| * |R| := by
    rw [K_eq_sin_mul_Qrat hnot, abs_mul, hS_def, abs_mul σ, hσabs, one_mul]
  have hKd : |deriv K t| = |R * C + D * S| := by
    rw [deriv_K_eq hnot]
    have e : R * C + D * S = σ * (Real.cos (π * t) * R + Real.sin (π * t) / π * D) := by
      rw [hS_def, hC_def]
      ring
    rw [e, abs_mul, hσabs, one_mul]
  -- the lower bound `ℓ = sl |Q(t)| ≤ |K(t)|`
  have hl : ((e.sl : ℚ) : ℝ) * |R| ≤ |K t| := by
    rw [hKt]
    exact mul_le_mul_of_nonneg_right (h1.trans (le_abs_self S)) (abs_nonneg R)
  -- the derivative bound `|K'(t)| ≤ max(|dl|, |du|)`
  have hC := mul_mem_min_max R h3 h4
  have hS := mul_mem_min_max D h1 h2
  have hd : |deriv K t| ≤
      max |min (R * e.cl) (R * e.cu) + min (D * e.sl) (D * e.su)|
        |max (R * e.cl) (R * e.cu) + max (D * e.sl) (D * e.su)| := by
    rw [hKd]
    exact abs_le_max_abs_abs (add_le_add hC.1 hS.1) (add_le_add hC.2 hS.2)
  set dmax := max |min (R * e.cl) (R * e.cu) + min (D * e.sl) (D * e.su)|
        |max (R * e.cl) (R * e.cu) + max (D * e.sl) (D * e.su)| with hdmax
  -- the cell estimate
  have hmv := abs_K_ge_of_abs_sub_le (h := 1 / 32768) hs
  have hpi := Distinct839.Kernel.pi_lt_piHi
  have hpi2 : π ^ 2 * (1 / 32768) ≤ piHiR * piHiR / 32768 := by
    have : π ^ 2 ≤ piHiR * piHiR := by nlinarith [pi_pos]
    linarith
  have hdb : min π (|deriv K t| + π ^ 2 * (1 / 32768)) ≤
      min piHiR (dmax + piHiR * piHiR / 32768) :=
    min_le_min hpi.le (add_le_add hd hpi2)
  set low : ℝ := max 0 (|R| * ((e.sl : ℚ) : ℝ) -
    min piHiR (dmax + piHiR * piHiR / 32768) / 32768) with hlow_def
  have hlow : low ≤ |K s| := by
    refine max_le (abs_nonneg _) ?_
    have : |R| * ((e.sl : ℚ) : ℝ) = ((e.sl : ℚ) : ℝ) * |R| := mul_comm _ _
    linarith
  have hlow0 : 0 ≤ low := le_max_left _ _
  have hsq : low * low ≤ K s ^ 2 := by
    rw [← sq_abs]
    nlinarith
  -- the table entry `⌊V low²⌋`
  have key : ∀ x : ℚ, (x : ℝ) = low →
      ((⌊x * x * 268435456⌋₊ : ℕ) : ℝ) / 268435456 ≤ K s ^ 2 := by
    intro x hx
    have hx0 : (0 : ℚ) ≤ x * x * 268435456 := mul_nonneg (mul_self_nonneg x) (by norm_num)
    have hfl : ((⌊x * x * 268435456⌋₊ : ℕ) : ℚ) ≤ x * x * 268435456 := Nat.floor_le hx0
    have hfl' : ((⌊x * x * 268435456⌋₊ : ℕ) : ℝ) ≤ low * low * 268435456 := by
      rw [← hx]
      exact_mod_cast hfl
    rw [div_le_iff₀ (by norm_num)]
    have := mul_le_mul_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ 268435456)
    linarith
  rw [cellVal_eq]
  apply key
  simp only [cellLow]
  push_cast
  rw [hR, hD]

/-! ## The whole table -/

/-- **Soundness of the kernel table**: `kTab k / 2²⁸ ≤ K(t)²` on `[k/16384, (k+1)/16384]`. -/
theorem _root_.Simple673.kTab_sound : TableSound kTab := by
  intro k s hs1 hs2
  have hH : ((gridH : ℕ) : ℝ) = 16384 := by norm_num [gridH]
  have hV : ((scaleV : ℕ) : ℝ) = 268435456 := by norm_num [scaleV]
  rw [hH] at hs1 hs2
  rw [hV]
  have hs : |s - (2 * k + 1) / 32768| ≤ 1 / 32768 := by
    rw [abs_le]
    constructor <;> linarith
  have hσ : ((-1 : ℝ) ^ (k / 16384)) * (-1) ^ (k / 16384) = 1 := by
    rw [← sq]
    exact Distinct839.Kernel.neg_one_pow_sq _
  unfold kTab kTabWith
  dsimp only
  split_ifs with hj
  · obtain ⟨h1, h2⟩ := Distinct839.Kernel.sin_cos_mid_low k
    refine cellVal_sound _ k _ hσ ?_ hs
    rw [h1, h2]
    exact Distinct839.Kernel.trigEncl_holds hj
  · obtain ⟨h1, h2⟩ := Distinct839.Kernel.sin_cos_mid_high k
    refine cellVal_sound _ k _ hσ ?_ hs
    rw [h1, h2]
    exact (Distinct839.Kernel.trigEncl_holds (by omega)).reflect

end Simple673.Kernel
