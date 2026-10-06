/-
Line889/Majorant/Checker.lean — a rational checker for `fCos ≤ gMaj` on an interval.

For a rational interval `[l, r]` with midpoint `m` and half-length `δ`, the function `leafOK`
computes, in exact rational arithmetic,

* an upper bound `fUp m δ` for `fCos u`, `u ∈ [l, r]`: each `cos(2π j u)` is compared with the
  Taylor polynomial at the rational point `2 p₀ (j m - k)`, `p₀ = 355/113`, `k` the integer
  nearest to `j m`; the error of replacing the argument is bounded by the Lipschitz constant `1`
  of `cos`;
* a lower bound `hLow m δ` for `sinc(π d (u - 1/2)) + sinc(π d (u + 1/2))`, `d = 17/20`, in the
  same way, with the Lipschitz constant `1/2` of `sinc`;

and tests `0 ≤ hLow` and `fUp ≤ γ · hLow²`, `γ = 61/100`. `leafOK_sound` shows that a successful
test implies `fCos u ≤ gMaj u` on `[l, r]`, and `checkAll_sound` extends this to a chain of
intervals given by a list of breakpoints.

The file follows `Simple673/Majorant/Checker.lean` and `Distinct839/Majorant/Checker.lean`, with
the window coefficients of `Line889/Defs.lean` (the third window) and its amplitude `γ`. The Taylor
polynomials `cosPoly`, `sincPoly` and their enclosures are those of
`Distinct839/Majorant/Taylor.lean`.
-/
import Line889.Defs
import Distinct839.Majorant.Taylor

open Real
open scoped BigOperators

namespace Line889.Majorant

/-! ## Rational bounds for `π` -/

/-- The rational approximation `355/113` of `π` used as evaluation point. -/
def piQ : ℚ := 355 / 113

/-- A rational upper bound for `π`. -/
def piUp : ℚ := 3141593 / 1000000

/-- A rational bound for `|π - 355/113|`. -/
def piErr : ℚ := 1 / 1000000

lemma piQ_cast : ((piQ : ℚ) : ℝ) = 355 / 113 := by unfold piQ; norm_num

lemma piUp_cast : ((piUp : ℚ) : ℝ) = 3141593 / 1000000 := by unfold piUp; norm_num

lemma piErr_cast : ((piErr : ℚ) : ℝ) = 1 / 1000000 := by unfold piErr; norm_num

lemma pi_le_piUp : π ≤ ((piUp : ℚ) : ℝ) := by
  rw [piUp_cast]
  have h := pi_lt_d6
  norm_num at h
  linarith

lemma piUp_nonneg : (0 : ℝ) ≤ ((piUp : ℚ) : ℝ) := le_trans pi_pos.le pi_le_piUp

lemma abs_pi_sub_piQ : |π - ((piQ : ℚ) : ℝ)| ≤ ((piErr : ℚ) : ℝ) := by
  rw [piQ_cast, piErr_cast, abs_le]
  have h1 := pi_gt_d6
  have h2 := pi_lt_d6
  norm_num at h1 h2
  constructor <;> linarith

/-! ## Enclosure of `cos(2π j u)` -/

/-- The integer nearest to a rational number (any integer would be sound). -/
def nearest (x : ℚ) : ℤ := (2 * x.num + x.den) / (2 * x.den)

/-- `j m - k`, with `k` the integer nearest to `j m`. -/
def redArg (j : ℕ) (m : ℚ) : ℚ := (j : ℚ) * m - (nearest ((j : ℚ) * m) : ℤ)

/-- The rational evaluation point `2 p₀ (j m - k)` for `cos(2π j u)`, `u` near `m`. -/
def cosArg (j : ℕ) (m : ℚ) : ℚ := 2 * piQ * redArg j m

/-- Bound for the distance from `2π (j u - k)` to `cosArg j m` when `|u - m| ≤ δ`. -/
def cosErr (j : ℕ) (m δ : ℚ) : ℚ := 2 * piUp * (j : ℚ) * δ + 2 * piErr * |redArg j m|

/-- Upper bound for `a · cos(2π j u)` when `|u - m| ≤ δ`. -/
def cosTermUp (a : ℚ) (j : ℕ) (m δ : ℚ) : ℚ :=
  if 0 ≤ a then a * (Distinct839.Majorant.cosPoly (cosArg j m) 9 + cosErr j m δ)
  else a * (Distinct839.Majorant.cosPoly (cosArg j m) 10 - cosErr j m δ)

lemma cos_enclosure (j : ℕ) (m δ : ℚ) (u : ℝ) (hu : |u - (m : ℝ)| ≤ (δ : ℝ)) :
    Distinct839.Majorant.cosPoly ((cosArg j m : ℚ) : ℝ) 10 - ((cosErr j m δ : ℚ) : ℝ)
        ≤ cos (2 * π * (j : ℝ) * u) ∧
      cos (2 * π * (j : ℝ) * u)
        ≤ Distinct839.Majorant.cosPoly ((cosArg j m : ℚ) : ℝ) 9 + ((cosErr j m δ : ℚ) : ℝ) := by
  have hr : ((redArg j m : ℚ) : ℝ)
      = (j : ℝ) * (m : ℝ) - ((nearest ((j : ℚ) * m) : ℤ) : ℝ) := by
    unfold redArg; push_cast; ring
  have hq : ((cosArg j m : ℚ) : ℝ) = 2 * ((piQ : ℚ) : ℝ) * ((redArg j m : ℚ) : ℝ) := by
    unfold cosArg; push_cast; ring
  have he : ((cosErr j m δ : ℚ) : ℝ) = 2 * ((piUp : ℚ) : ℝ) * (j : ℝ) * (δ : ℝ)
      + 2 * ((piErr : ℚ) : ℝ) * |((redArg j m : ℚ) : ℝ)| := by
    unfold cosErr; push_cast; ring
  have hcos : cos (2 * π * (j : ℝ) * u)
      = cos (2 * π * (j : ℝ) * u - ((nearest ((j : ℚ) * m) : ℤ) : ℝ) * (2 * π)) :=
    (cos_sub_int_mul_two_pi _ _).symm
  have hdiff : 2 * π * (j : ℝ) * u - ((nearest ((j : ℚ) * m) : ℤ) : ℝ) * (2 * π)
      - ((cosArg j m : ℚ) : ℝ)
      = 2 * π * (j : ℝ) * (u - (m : ℝ))
        + 2 * (π - ((piQ : ℚ) : ℝ)) * ((redArg j m : ℚ) : ℝ) := by
    rw [hq, hr]; ring
  have h1 : |2 * π * (j : ℝ) * (u - (m : ℝ))| ≤ 2 * ((piUp : ℚ) : ℝ) * (j : ℝ) * (δ : ℝ) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * π * (j : ℝ))]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left pi_le_piUp zero_le_two)
        (Nat.cast_nonneg j))
      hu (abs_nonneg _) (mul_nonneg (mul_nonneg zero_le_two piUp_nonneg) (Nat.cast_nonneg j))
  have h2 : |2 * (π - ((piQ : ℚ) : ℝ)) * ((redArg j m : ℚ) : ℝ)|
      ≤ 2 * ((piErr : ℚ) : ℝ) * |((redArg j m : ℚ) : ℝ)| := by
    rw [abs_mul, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left abs_pi_sub_piQ zero_le_two)
      (abs_nonneg _)
  have habs : |2 * π * (j : ℝ) * u - ((nearest ((j : ℚ) * m) : ℤ) : ℝ) * (2 * π)
      - ((cosArg j m : ℚ) : ℝ)| ≤ ((cosErr j m δ : ℚ) : ℝ) := by
    rw [hdiff, he]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have hlip := abs_le.mp ((abs_cos_sub_cos_le _ _).trans habs)
  have hU : cos ((cosArg j m : ℚ) : ℝ)
      ≤ Distinct839.Majorant.cosPoly ((cosArg j m : ℚ) : ℝ) 9 :=
    Distinct839.Majorant.cos_le_cosPoly _ 4
  have hL : Distinct839.Majorant.cosPoly ((cosArg j m : ℚ) : ℝ) 10
      ≤ cos ((cosArg j m : ℚ) : ℝ) :=
    Distinct839.Majorant.cosPoly_le_cos _ 4
  rw [hcos]
  constructor <;> linarith [hlip.1, hlip.2]

lemma cosTermUp_sound (a : ℚ) (j : ℕ) (m δ : ℚ) (u : ℝ) (hu : |u - (m : ℝ)| ≤ (δ : ℝ)) :
    (a : ℝ) * cos (2 * π * (j : ℝ) * u) ≤ ((cosTermUp a j m δ : ℚ) : ℝ) := by
  obtain ⟨hlo, hhi⟩ := cos_enclosure j m δ u hu
  unfold cosTermUp
  split_ifs with ha
  · rw [Rat.cast_mul, Rat.cast_add, Distinct839.Majorant.cast_cosPoly]
    exact mul_le_mul_of_nonneg_left hhi (by exact_mod_cast ha)
  · rw [Rat.cast_mul, Rat.cast_sub, Distinct839.Majorant.cast_cosPoly]
    have ha' : (a : ℝ) ≤ 0 := by exact_mod_cast le_of_lt (not_le.mp ha)
    exact mul_le_mul_of_nonpos_left hlo ha'

/-! ## The cosine polynomial -/

/-- The window coefficients as rational numbers. -/
def aQ (j : Fin 6) : ℚ := (aInt j : ℚ) / 1000000

/-- Rational upper bound for `fCos u` when `|u - m| ≤ δ`. -/
def fUp (m δ : ℚ) : ℚ := 1 + ∑ j : Fin 6, cosTermUp (aQ j) ((j : ℕ) + 1) m δ

lemma fCos_le_fUp (m δ : ℚ) (u : ℝ) (hu : |u - (m : ℝ)| ≤ (δ : ℝ)) :
    fCos u ≤ ((fUp m δ : ℚ) : ℝ) := by
  unfold fCos fUp
  rw [Rat.cast_add, Rat.cast_one, Rat.cast_sum]
  refine add_le_add le_rfl (Finset.sum_le_sum fun j _ => ?_)
  have h := cosTermUp_sound (aQ j) ((j : ℕ) + 1) m δ u hu
  have ha : ((aQ j : ℚ) : ℝ) = aC j := by
    unfold aQ aC; push_cast; rfl
  rw [ha, Nat.cast_add, Nat.cast_one] at h
  exact h

/-! ## The two sinc terms -/

/-- The rational evaluation point `p₀ d (m + s)` for `sinc(π d (u + s))`, `u` near `m`. -/
def sincArg (m s : ℚ) : ℚ := piQ * (17 / 20) * (m + s)

/-- Half of a bound for the distance from `π d (u + s)` to `sincArg m s` when `|u - m| ≤ δ`. -/
def sincErr (m δ s : ℚ) : ℚ := (piUp * (17 / 20) * δ + piErr * (17 / 20) * |m + s|) / 2

/-- Lower bound for `sincN (d (u + s))` when `|u - m| ≤ δ`. -/
def sincLow (m δ s : ℚ) : ℚ := Distinct839.Majorant.sincPoly (sincArg m s) 8 - sincErr m δ s

lemma sincLow_sound (m δ s : ℚ) (u : ℝ) (hu : |u - (m : ℝ)| ≤ (δ : ℝ)) :
    ((sincLow m δ s : ℚ) : ℝ) ≤ sincN (sep * (u + (s : ℝ))) := by
  have hq : ((sincArg m s : ℚ) : ℝ) = ((piQ : ℚ) : ℝ) * (17 / 20) * ((m : ℝ) + (s : ℝ)) := by
    unfold sincArg; push_cast; ring
  have he : ((sincErr m δ s : ℚ) : ℝ) = (((piUp : ℚ) : ℝ) * (17 / 20) * (δ : ℝ)
      + ((piErr : ℚ) : ℝ) * (17 / 20) * |(m : ℝ) + (s : ℝ)|) / 2 := by
    unfold sincErr; push_cast; ring
  have hdiff : π * (sep * (u + (s : ℝ))) - ((sincArg m s : ℚ) : ℝ)
      = π * (17 / 20) * (u - (m : ℝ))
        + (π - ((piQ : ℚ) : ℝ)) * (17 / 20) * ((m : ℝ) + (s : ℝ)) := by
    rw [hq]; unfold sep; ring
  have h1 : |π * (17 / 20) * (u - (m : ℝ))| ≤ ((piUp : ℚ) : ℝ) * (17 / 20) * (δ : ℝ) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ π * (17 / 20))]
    exact mul_le_mul (mul_le_mul_of_nonneg_right pi_le_piUp (by norm_num)) hu (abs_nonneg _)
      (mul_nonneg piUp_nonneg (by norm_num))
  have h2 : |(π - ((piQ : ℚ) : ℝ)) * (17 / 20) * ((m : ℝ) + (s : ℝ))|
      ≤ ((piErr : ℚ) : ℝ) * (17 / 20) * |(m : ℝ) + (s : ℝ)| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 17 / 20)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right abs_pi_sub_piQ (by norm_num)) (abs_nonneg _)
  have habs : |π * (sep * (u + (s : ℝ))) - ((sincArg m s : ℚ) : ℝ)|
      ≤ 2 * ((sincErr m δ s : ℚ) : ℝ) := by
    rw [hdiff, he]
    have h := (abs_add_le _ _).trans (add_le_add h1 h2)
    linarith
  have hlip := abs_le.mp (Distinct839.Majorant.abs_sinc_sub_sinc_le
    (π * (sep * (u + (s : ℝ)))) ((sincArg m s : ℚ) : ℝ))
  have hpoly : Distinct839.Majorant.sincPoly ((sincArg m s : ℚ) : ℝ) 8
      ≤ sinc ((sincArg m s : ℚ) : ℝ) :=
    Distinct839.Majorant.sincPoly_le_sinc _ 3
  unfold sincLow sincN
  rw [Rat.cast_sub, Distinct839.Majorant.cast_sincPoly]
  linarith [hlip.1]

/-- Rational lower bound for `sincN (d (u - 1/2)) + sincN (d (u + 1/2))` when `|u - m| ≤ δ`. -/
def hLow (m δ : ℚ) : ℚ := sincLow m δ (-1 / 2) + sincLow m δ (1 / 2)

lemma hLow_le (m δ : ℚ) (u : ℝ) (hu : |u - (m : ℝ)| ≤ (δ : ℝ)) :
    ((hLow m δ : ℚ) : ℝ) ≤ sincN (sep * (u - 1 / 2)) + sincN (sep * (u + 1 / 2)) := by
  have h1 := sincLow_sound m δ (-1 / 2) u hu
  have h2 := sincLow_sound m δ (1 / 2) u hu
  have e1 : u + (((-1 / 2 : ℚ)) : ℝ) = u - 1 / 2 := by push_cast; ring
  have e2 : u + (((1 / 2 : ℚ)) : ℝ) = u + 1 / 2 := by push_cast; ring
  rw [e1] at h1
  rw [e2] at h2
  unfold hLow
  rw [Rat.cast_add]
  linarith

/-! ## Leaves and chains of leaves -/

/-- The test for one interval `[l, r]`. -/
def leafOK (l r : ℚ) : Bool :=
  decide (0 ≤ hLow ((l + r) / 2) ((r - l) / 2)) &&
    decide (fUp ((l + r) / 2) ((r - l) / 2) ≤ 61 / 100 * hLow ((l + r) / 2) ((r - l) / 2) ^ 2)

/-- A successful test on `[l, r]` proves the majorant inequality on `[l, r]`. -/
theorem leafOK_sound (l r : ℚ) (h : leafOK l r = true) (u : ℝ) (hl : (l : ℝ) ≤ u)
    (hr : u ≤ (r : ℝ)) : fCos u ≤ gMaj u := by
  have hu : |u - (((l + r) / 2 : ℚ) : ℝ)| ≤ (((r - l) / 2 : ℚ) : ℝ) := by
    push_cast
    rw [abs_le]
    constructor <;> linarith
  simp only [leafOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : (0 : ℝ) ≤ ((hLow ((l + r) / 2) ((r - l) / 2) : ℚ) : ℝ) := by exact_mod_cast h1
  have h2' : ((fUp ((l + r) / 2) ((r - l) / 2) : ℚ) : ℝ)
      ≤ 61 / 100 * ((hLow ((l + r) / 2) ((r - l) / 2) : ℚ) : ℝ) ^ 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr h2
    rw [Rat.cast_mul, Rat.cast_pow] at h
    have e : (((61 / 100 : ℚ)) : ℝ) = 61 / 100 := by norm_num
    rwa [e] at h
  have hf := fCos_le_fUp _ _ u hu
  have hh := hLow_le _ _ u hu
  have hg : gMaj u = 61 / 100 * (sincN (sep * (u - 1 / 2)) + sincN (sep * (u + 1 / 2))) ^ 2 := by
    unfold gMaj gammaM; rfl
  rw [hg]
  exact hf.trans (h2'.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1' hh 2) (by norm_num)))

/-- The test for a chain of intervals with the given breakpoints. -/
def checkAll : List ℚ → Bool
  | a :: b :: rest => leafOK a b && checkAll (b :: rest)
  | _ => true

lemma checkAll_cons_cons (a b : ℚ) (rest : List ℚ) :
    checkAll (a :: b :: rest) = (leafOK a b && checkAll (b :: rest)) := rfl

/-- A successful test on a chain starting at `a` proves the majorant inequality between `a` and
any later breakpoint. -/
theorem checkAll_sound (L : List ℚ) : ∀ a : ℚ, checkAll (a :: L) = true →
    ∀ b ∈ L, ∀ u : ℝ, (a : ℝ) ≤ u → u ≤ (b : ℝ) → fCos u ≤ gMaj u := by
  induction L with
  | nil => intro a _ b hb; simp at hb
  | cons c L ih =>
    intro a h b hb u hau hub
    rw [checkAll_cons_cons, Bool.and_eq_true] at h
    rcases le_or_gt u (c : ℝ) with huc | huc
    · exact leafOK_sound a c h.1 u hau huc
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd hub (not_le.mpr huc)
      · exact ih c h.2 b hb' u (le_of_lt huc) hub

/-! ## Parity -/

lemma fCos_neg (u : ℝ) : fCos (-u) = fCos u := by
  unfold fCos
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_neg, cos_neg]

lemma gMaj_neg (u : ℝ) : gMaj (-u) = gMaj u := by
  unfold gMaj sincN
  rw [show π * (sep * (-u - 1 / 2)) = -(π * (sep * (u + 1 / 2))) by ring,
    show π * (sep * (-u + 1 / 2)) = -(π * (sep * (u - 1 / 2))) by ring, sinc_neg, sinc_neg]
  ring

end Line889.Majorant
