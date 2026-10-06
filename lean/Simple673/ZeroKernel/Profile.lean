/-
Simple673/ZeroKernel/Profile.lean — elementary facts about the profile and the kernel.

The cosine polynomial `fCos = 1 + ∑_{j=1}^{10} a_j cos(2π j u)` satisfies
`|fCos - 1| ≤ ∑ |a_j| = 0.210672`, so the profile `vProf = (2/5) fCos` is even, continuous and
takes values in `(0, 1)`. The majorant `gMaj` is nonnegative, and the kernel `K` (a combination of
shifted sincs) satisfies `K 0 = 1` and `|K| ≤ 2`. These are the only properties of the window
that the zero side uses, apart from the integral formula for `K` and the majorant statements,
which are hypotheses of `gramData`. This is the one file of `Simple673/ZeroKernel/` in which
the values of the ten window coefficients occur.

The three facts about `sincN` used here (`sincN_nat_succ`, `sincN_neg`, `abs_sincN_le_one`) do not
depend on the window; they are those of `Distinct839/ZeroKernel/Profile.lean`.
-/
import Distinct839.ZeroKernel.Profile
import Simple673.Spec2
import Simple673.Sum10

open scoped BigOperators
open Real

noncomputable section

namespace Simple673.ZeroKernel

/-! ## The cosine polynomial -/

/-- The ten window coefficients `a_1, …, a_10` as rational numbers (`aC j` is `a_{j+1}`). -/
lemma aC_vals : aC 0 = 122290 / 1000000 ∧
    aC 1 = -45012 / 1000000 ∧
    aC 2 = 16241 / 1000000 ∧
    aC 3 = 1887 / 1000000 ∧
    aC 4 = 2711 / 1000000 ∧
    aC 5 = 3731 / 1000000 ∧
    aC 6 = -5307 / 1000000 ∧
    aC 7 = 2982 / 1000000 ∧
    aC 8 = -5153 / 1000000 ∧
    aC 9 = 5358 / 1000000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [aC, aInt]

/-- `fCos` written out. -/
lemma fCos_eq (u : ℝ) :
    fCos u = 1 + (122290 / 1000000 * Real.cos (2 * π * 1 * u)
      - 45012 / 1000000 * Real.cos (2 * π * 2 * u)
      + 16241 / 1000000 * Real.cos (2 * π * 3 * u)
      + 1887 / 1000000 * Real.cos (2 * π * 4 * u)
      + 2711 / 1000000 * Real.cos (2 * π * 5 * u)
      + 3731 / 1000000 * Real.cos (2 * π * 6 * u)
      - 5307 / 1000000 * Real.cos (2 * π * 7 * u)
      + 2982 / 1000000 * Real.cos (2 * π * 8 * u)
      - 5153 / 1000000 * Real.cos (2 * π * 9 * u)
      + 5358 / 1000000 * Real.cos (2 * π * 10 * u)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := aC_vals
  simp only [fCos, sum_univ_ten, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  norm_num
  ring

/-- `|fCos u - 1| ≤ ∑ |a_j| = 210672 · 10⁻⁶`. -/
lemma abs_fCos_sub_one_le (u : ℝ) : |fCos u - 1| ≤ 210672 / 1000000 := by
  rw [fCos_eq, abs_le]
  have h1 := Real.cos_le_one (2 * π * 1 * u)
  have h2 := Real.cos_le_one (2 * π * 2 * u)
  have h3 := Real.cos_le_one (2 * π * 3 * u)
  have h4 := Real.cos_le_one (2 * π * 4 * u)
  have h5 := Real.cos_le_one (2 * π * 5 * u)
  have h6 := Real.cos_le_one (2 * π * 6 * u)
  have h7 := Real.cos_le_one (2 * π * 7 * u)
  have h8 := Real.cos_le_one (2 * π * 8 * u)
  have h9 := Real.cos_le_one (2 * π * 9 * u)
  have h10 := Real.cos_le_one (2 * π * 10 * u)
  have g1 := Real.neg_one_le_cos (2 * π * 1 * u)
  have g2 := Real.neg_one_le_cos (2 * π * 2 * u)
  have g3 := Real.neg_one_le_cos (2 * π * 3 * u)
  have g4 := Real.neg_one_le_cos (2 * π * 4 * u)
  have g5 := Real.neg_one_le_cos (2 * π * 5 * u)
  have g6 := Real.neg_one_le_cos (2 * π * 6 * u)
  have g7 := Real.neg_one_le_cos (2 * π * 7 * u)
  have g8 := Real.neg_one_le_cos (2 * π * 8 * u)
  have g9 := Real.neg_one_le_cos (2 * π * 9 * u)
  have g10 := Real.neg_one_le_cos (2 * π * 10 * u)
  constructor <;> linarith

lemma fCos_pos (u : ℝ) : 0 < fCos u := by
  have h := (abs_le.mp (abs_fCos_sub_one_le u)).1
  linarith

lemma fCos_le (u : ℝ) : fCos u ≤ 2 := by
  have h := (abs_le.mp (abs_fCos_sub_one_le u)).2
  linarith

lemma fCos_even (u : ℝ) : fCos (-u) = fCos u := by
  simp only [fCos, mul_neg, Real.cos_neg]

lemma fCos_continuous : Continuous fCos := by
  unfold fCos
  fun_prop

/-! ## The profile -/

lemma vProf_even (s : ℝ) : vProf (-s) = vProf s := by
  simp only [vProf, fCos_even]

lemma vProf_pos (s : ℝ) : 0 < vProf s := by
  have := fCos_pos s
  unfold vProf
  positivity

lemma vProf_nonneg (s : ℝ) : 0 ≤ vProf s := (vProf_pos s).le

lemma vProf_le_one (s : ℝ) : vProf s ≤ 1 := by
  have := fCos_le s
  unfold vProf
  linarith

lemma abs_vProf_le_one (s : ℝ) : |vProf s| ≤ 1 := by
  rw [abs_of_nonneg (vProf_nonneg s)]
  exact vProf_le_one s

lemma vProf_continuous : Continuous vProf := by
  unfold vProf
  exact continuous_const.mul fCos_continuous

/-! ## The majorant and the kernel -/

lemma gMaj_nonneg (u : ℝ) : 0 ≤ gMaj u := by
  unfold gMaj gammaM
  positivity

/-- `K 0 = 1`. -/
lemma K_zero : K 0 = 1 := by
  unfold K
  have h0 : sincN 0 = 1 := by simp [sincN]
  have hterm : ∀ j : Fin 10,
      aC j / 2 * (sincN (0 - (((j : ℕ) : ℝ) + 1)) + sincN (0 + (((j : ℕ) : ℝ) + 1))) = 0 := by
    intro j
    rw [zero_sub, zero_add, Distinct839.ZeroKernel.sincN_neg,
      Distinct839.ZeroKernel.sincN_nat_succ, add_zero, mul_zero]
  rw [h0, Finset.sum_eq_zero fun j _ => hterm j, add_zero]

/-- `|K| ≤ 2`: the sincs are bounded by `1` and `∑ |a_j| < 1`. -/
lemma abs_K_le (t : ℝ) : |K t| ≤ 2 := by
  unfold K
  have hs : ∀ x : ℝ, |sincN x| ≤ 1 := Distinct839.ZeroKernel.abs_sincN_le_one
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := aC_vals
  simp only [sum_univ_ten, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  norm_num
  have a0 := abs_le.mp (hs t)
  have a1 := abs_le.mp (hs (t - 1))
  have b1 := abs_le.mp (hs (t + 1))
  have a2 := abs_le.mp (hs (t - 2))
  have b2 := abs_le.mp (hs (t + 2))
  have a3 := abs_le.mp (hs (t - 3))
  have b3 := abs_le.mp (hs (t + 3))
  have a4 := abs_le.mp (hs (t - 4))
  have b4 := abs_le.mp (hs (t + 4))
  have a5 := abs_le.mp (hs (t - 5))
  have b5 := abs_le.mp (hs (t + 5))
  have a6 := abs_le.mp (hs (t - 6))
  have b6 := abs_le.mp (hs (t + 6))
  have a7 := abs_le.mp (hs (t - 7))
  have b7 := abs_le.mp (hs (t + 7))
  have a8 := abs_le.mp (hs (t - 8))
  have b8 := abs_le.mp (hs (t + 8))
  have a9 := abs_le.mp (hs (t - 9))
  have b9 := abs_le.mp (hs (t + 9))
  have a10 := abs_le.mp (hs (t - 10))
  have b10 := abs_le.mp (hs (t + 10))
  rw [abs_le]
  constructor <;> linarith

end Simple673.ZeroKernel
