/-
Simple673/Kernel/Beta.lean — the lower bound `K(t)² ≥ β = 1/20` on `|t| ≤ 17/20`.

The cells `0, …, 13926` cover `[0, 17/20]`. Instead of evaluating all 13927 table entries, a short
covering certificate is checked: a pair `(k, m)` means that the table entry of cell `k` is large
enough to give `K² ≥ β` on the cells `k - m, …, k + m`, because `|K'| ≤ π`. With `w = kTab k / V`
and `c = piHi · m / H`, the condition `(√β + c)² ≤ w` is checked without square roots as
`c² + β ≤ w` and `4 c² β ≤ (w - β - c²)²` (`coverOK`). Eight pairs suffice (`betaCert`); the
check is evaluated by the kernel (`decide +kernel`).

The minimum of the table over these cells is `13707941 / 2²⁸ = 0.05106…`, attained at the last
cell `k = 13926`; the value `β = 1/20` of the interface lies below it, which leaves room for the
covering argument near the right end.
-/
import Simple673.Kernel.Sound

noncomputable section

open Real

namespace Simple673.Kernel

/-! ## The certificate and its checker (computable) -/

/-- `β = 1/20` as a rational number. -/
def betaQ : ℚ := 1 / 20

/-- The table entry of cell `k` gives `K² ≥ β` on the cells `k - m, …, k + m`. -/
def coverOK (k m : ℕ) : Bool :=
  let c : ℚ := Distinct839.Kernel.piHi * m / 16384
  let w : ℚ := (kTab k : ℚ) / 268435456
  decide (c ^ 2 + betaQ ≤ w) && decide (4 * c ^ 2 * betaQ ≤ (w - betaQ - c ^ 2) ^ 2)

/-- `coverCheck n l lo`: the pairs `l` cover the cells `lo, …, n - 1`, each pair `(k, m)` starting
at most at the first cell not yet covered. -/
def coverCheck (n : ℕ) : List (ℕ × ℕ) → ℕ → Bool
  | [], lo => decide (n ≤ lo)
  | (k, m) :: l, lo => decide (k ≤ lo + m) && coverOK k m && coverCheck n l (k + m + 1)

/-- The covering certificate for the cells `0, …, 13926` (computed by a greedy search). -/
def betaCert : List (ℕ × ℕ) :=
  [(3664, 3664), (9228, 1899), (11929, 803), (13074, 343), (13567, 150), (13784, 66),
   (13879, 30), (13923, 13)]

/-- The finite check behind `betaBound`, evaluated by the kernel. -/
theorem betaCert_check : coverCheck 13927 betaCert 0 = true := by decide +kernel

/-! ## Soundness of the checker -/

/-- `K² ≥ β` on the grid cell `j`. -/
def CellGood (j : ℕ) : Prop :=
  ∀ t : ℝ, (j : ℝ) / 16384 ≤ t → t ≤ ((j : ℝ) + 1) / 16384 → betaC ≤ K t ^ 2

lemma betaQ_cast : ((betaQ : ℚ) : ℝ) = betaC := by
  rw [betaQ, betaC]
  norm_num

/-- One pair of the certificate. -/
lemma coverOK_sound {k m : ℕ} (h : coverOK k m = true) {j : ℕ} (hj1 : k ≤ j + m)
    (hj2 : j ≤ k + m) : CellGood j := by
  intro t ht1 ht2
  simp only [coverOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  -- real versions of the two rational conditions
  set c : ℝ := ((Distinct839.Kernel.piHi : ℚ) : ℝ) * m / 16384 with hc_def
  set w : ℝ := (kTab k : ℝ) / 268435456 with hw_def
  have hcq : (((Distinct839.Kernel.piHi * m / 16384 : ℚ)) : ℝ) = c := by push_cast; rfl
  have hwq : ((((kTab k : ℚ) / 268435456 : ℚ)) : ℝ) = w := by push_cast; rfl
  have h1' : c ^ 2 + betaC ≤ w := by
    rw [← hcq, ← hwq, ← betaQ_cast]
    exact_mod_cast h1
  have h2' : 4 * c ^ 2 * betaC ≤ (w - betaC - c ^ 2) ^ 2 := by
    rw [← hcq, ← hwq, ← betaQ_cast]
    exact_mod_cast h2
  have hc0 : 0 ≤ c :=
    div_nonneg (mul_nonneg Distinct839.Kernel.piHi_pos.le (Nat.cast_nonneg _)) (by norm_num)
  have hβ0 : 0 ≤ betaC := by rw [betaC]; norm_num
  set b := Real.sqrt betaC with hb_def
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hbb : b * b = betaC := Real.mul_self_sqrt hβ0
  -- `(√β + c)² ≤ w`
  have h3 : 2 * c * b ≤ w - betaC - c ^ 2 := by
    by_contra hcon
    replace hcon := not_le.mp hcon
    have hpos : 0 ≤ w - betaC - c ^ 2 := by linarith
    have : (w - betaC - c ^ 2) ^ 2 < (2 * c * b) ^ 2 := by
      exact pow_lt_pow_left₀ hcon hpos (by norm_num)
    nlinarith
  have h4 : (b + c) ^ 2 ≤ w := by nlinarith
  -- the point `t' = t + (k - j)/H` of cell `k`
  set t' : ℝ := t + ((k : ℝ) - j) / 16384 with ht'_def
  have hk1 : (k : ℝ) / 16384 ≤ t' := by rw [ht'_def]; linarith
  have hk2 : t' ≤ ((k : ℝ) + 1) / 16384 := by rw [ht'_def]; linarith
  have hsound := kTab_sound k t'
    (by simpa [gridH] using hk1) (by simpa [gridH] using hk2)
  have hV : ((scaleV : ℕ) : ℝ) = 268435456 := by norm_num [scaleV]
  rw [hV, ← hw_def] at hsound
  -- `√β + c ≤ |K(t')|`
  have h5 : b + c ≤ |K t'| := by
    have : (b + c) ^ 2 ≤ |K t'| ^ 2 := by rw [sq_abs]; linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (abs_nonneg _) (by norm_num)).mp this
  -- `|K(t)| ≥ |K(t')| - π m/H ≥ √β`
  have hdist : |t - t'| ≤ (m : ℝ) / 16384 := by
    rw [ht'_def, show t - (t + ((k : ℝ) - j) / 16384) = ((j : ℝ) - k) / 16384 by ring, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 16384)]
    gcongr
    rw [abs_le]
    constructor
    · have : (k : ℝ) ≤ j + m := by exact_mod_cast hj1
      linarith
    · have : (j : ℝ) ≤ k + m := by exact_mod_cast hj2
      linarith
  have hmv := abs_K_ge_of_abs_sub_le hdist
  have hmin : (m : ℝ) / 16384 * min π (|deriv K t'| + π ^ 2 * ((m : ℝ) / 16384)) ≤ c := by
    calc (m : ℝ) / 16384 * min π (|deriv K t'| + π ^ 2 * ((m : ℝ) / 16384))
        ≤ (m : ℝ) / 16384 * ((Distinct839.Kernel.piHi : ℚ) : ℝ) := by
          gcongr
          exact (min_le_left _ _).trans Distinct839.Kernel.pi_lt_piHi.le
      _ = c := by rw [hc_def]; ring
  have h6 : b ≤ |K t| := by linarith
  calc betaC = b * b := hbb.symm
    _ ≤ |K t| * |K t| := mul_le_mul h6 h6 hb0 (abs_nonneg _)
    _ = K t ^ 2 := by rw [← sq, sq_abs]

/-- The checker is sound: cells below `lo` good and a successful check give all cells below `n`. -/
lemma coverCheck_sound (n : ℕ) :
    ∀ (l : List (ℕ × ℕ)) (lo : ℕ), coverCheck n l lo = true →
      (∀ j < lo, CellGood j) → ∀ j < n, CellGood j := by
  intro l
  induction l with
  | nil =>
    intro lo h hlo j hj
    simp only [coverCheck, decide_eq_true_eq] at h
    exact hlo j (by omega)
  | cons p l ih =>
    obtain ⟨k, m⟩ := p
    intro lo h hlo
    simp only [coverCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hk, hok⟩, hl⟩ := h
    refine ih (k + m + 1) hl fun j hj => ?_
    rcases lt_or_ge j lo with hjlo | hjlo
    · exact hlo j hjlo
    · exact coverOK_sound hok (by omega) (by omega)

/-! ## The bound -/

/-- **`K(t)² ≥ β` for `|t| ≤ 17/20`.** -/
theorem _root_.Simple673.betaBound : BetaBound := by
  have hall := coverCheck_sound 13927 betaCert 0 betaCert_check (fun j hj => absurd hj (by omega))
  -- nonnegative `t`
  have hpos : ∀ t : ℝ, 0 ≤ t → t ≤ 17 / 20 → betaC ≤ K t ^ 2 := by
    intro t ht0 ht1
    set j := ⌊t * 16384⌋₊ with hj_def
    have hj1 : (j : ℝ) ≤ t * 16384 := Nat.floor_le (by positivity)
    have hj2 : t * 16384 < j + 1 := Nat.lt_floor_add_one _
    have hjn : j < 13927 := by
      have : (j : ℝ) < 13927 := by linarith
      exact_mod_cast this
    exact hall j hjn t (by rw [div_le_iff₀ (by norm_num)]; linarith)
      (by rw [le_div_iff₀ (by norm_num)]; linarith)
  intro t ht
  rw [abs_le, sep] at ht
  rcases le_total 0 t with h0 | h0
  · exact hpos t h0 ht.2
  · have := hpos (-t) (by linarith) (by linarith)
    rwa [K_neg] at this

end Simple673.Kernel
