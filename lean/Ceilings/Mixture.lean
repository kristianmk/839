/-
Ceilings/Mixture.lean — from inequality (⋆) for several trial states to a ceiling.

Let states `k` have `n₁_k` simple and `n₂_k` double points per period, period `P_k`, and let `e_k`
be an upper bound for the pair energy per period, so that a certificate `(x₁, x₂, b)` satisfies

    `n₁_k x₁ + n₂_k x₂ - b P_k ≤ e_k`.                                              (⋆)

Take weights `w_k ≥ 0` and put `N = ∑ w_k (n₁_k + 2 n₂_k)` (multiplicity) and
`L = ∑ w_k (n₁_k + n₂_k)` (points). If `∑ w_k P_k ≤ N` and `∑ w_k (n₁_k + 4 n₂_k + e_k) ≤ C N`,
then the weighted sum of (⋆), with `b ≥ 0`, is

    `(3 - C + x₂ - x₁ - b) N ≤ (2 - 2 x₁ + x₂) L`                    (`ceiling_of_mixture`),

so the constant `(3 - C + x₂ - x₁ - b)/(2 - 2x₁ + x₂)` of the certificate is at most `L/N`
(`ceiling_of_states`). The weights are not normalised; the paper's normalisation is `N = 1`.

For simple points only (`line_ceiling_of_mixture`, `line_ceiling_of_states`): (⋆) reads
`x n_k - b P_k ≤ e_k`, and `∑ w_k (e_k - n_k) + (2 - C) ∑ w_k P_k ≤ 0` gives
`(2 - C - b) ∑ w_k P_k ≤ (1 - x) ∑ w_k n_k`. No sign condition on `b` is needed there.

`MixOK` and `LineMixOK` collect the conditions on rational data; they are decidable, and are
checked by the kernel for the data of each ceiling.
-/
import Ceilings.State

open scoped BigOperators
open Finset

namespace Ceilings

/-! ## Labelled points -/

/-- **The weighted sum of (⋆).** -/
theorem ceiling_of_mixture {ι : Type*} [Fintype ι] (w n₁ n₂ P e : ι → ℝ) {C x₁ x₂ b : ℝ}
    (hw : ∀ k, 0 ≤ w k) (hstar : ∀ k, n₁ k * x₁ + n₂ k * x₂ - b * P k ≤ e k) (hb : 0 ≤ b)
    (hP : ∑ k, w k * P k ≤ ∑ k, w k * (n₁ k + 2 * n₂ k))
    (hE : ∑ k, w k * (n₁ k + 4 * n₂ k + e k) ≤ C * ∑ k, w k * (n₁ k + 2 * n₂ k)) :
    (3 - C + x₂ - x₁ - b) * ∑ k, w k * (n₁ k + 2 * n₂ k)
      ≤ (2 - 2 * x₁ + x₂) * ∑ k, w k * (n₁ k + n₂ k) := by
  have hN : ∑ k, w k * (n₁ k + 2 * n₂ k) = ∑ k, w k * n₁ k + 2 * ∑ k, w k * n₂ k := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  have hL : ∑ k, w k * (n₁ k + n₂ k) = ∑ k, w k * n₁ k + ∑ k, w k * n₂ k := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  have hE' : ∑ k, w k * (n₁ k + 4 * n₂ k + e k)
      = ∑ k, w k * n₁ k + 4 * ∑ k, w k * n₂ k + ∑ k, w k * e k := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  have hS : x₁ * ∑ k, w k * n₁ k + x₂ * ∑ k, w k * n₂ k - b * ∑ k, w k * P k
      ≤ ∑ k, w k * e k := by
    have h := sum_le_sum fun k (_ : k ∈ univ) => mul_le_mul_of_nonneg_left (hstar k) (hw k)
    have e1 : x₁ * ∑ k, w k * n₁ k + x₂ * ∑ k, w k * n₂ k - b * ∑ k, w k * P k
        = ∑ k, w k * (n₁ k * x₁ + n₂ k * x₂ - b * P k) := by
      rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun k _ => by ring
    rw [e1]
    exact h
  rw [hN] at hP hE ⊢
  rw [hE'] at hE
  rw [hL]
  have hbP := mul_nonneg hb (sub_nonneg.mpr hP)
  nlinarith

/-- multiplicity of a weighted family of states: `N = ∑ w_k (n₁_k + 2 n₂_k)` -/
def mixN {ι : Type*} [Fintype ι] (S : ι → State) (w : ι → ℚ) : ℚ :=
  ∑ k, w k * ((S k).n1 + 2 * (S k).n2)

/-- number of points of a weighted family of states: `L = ∑ w_k (n₁_k + n₂_k)` -/
def mixL {ι : Type*} [Fintype ι] (S : ι → State) (w : ι → ℚ) : ℚ :=
  ∑ k, w k * ((S k).n1 + (S k).n2)

/-- length of a weighted family of states: `∑ w_k P_k` -/
def mixP {ι : Type*} [Fintype ι] (S : ι → State) (w : ι → ℚ) : ℚ := ∑ k, w k * (S k).P

/-- The conditions on the weights `w`, the energy bounds `e` and the lower bound `Clo` for the
energy constant: `w ≥ 0`, `N > 0`, `∑ w_k P_k ≤ N`, `∑ w_k (n₁_k + 4 n₂_k + e_k) ≤ Clo · N`. -/
def MixOK {ι : Type*} [Fintype ι] (S : ι → State) (w e : ι → ℚ) (Clo : ℚ) : Prop :=
  (∀ k, 0 ≤ w k) ∧ 0 < mixN S w ∧ mixP S w ≤ mixN S w
    ∧ ∑ k, w k * ((S k).n1 + 4 * (S k).n2 + e k) ≤ Clo * mixN S w

instance {ι : Type*} [Fintype ι] (S : ι → State) (w e : ι → ℚ) (Clo : ℚ) :
    Decidable (MixOK S w e Clo) :=
  inferInstanceAs (Decidable ((∀ k, 0 ≤ w k) ∧ 0 < mixN S w ∧ mixP S w ≤ mixN S w
    ∧ ∑ k, w k * ((S k).n1 + 4 * (S k).n2 + e k) ≤ Clo * mixN S w))

/-- **The ceiling of a mixture of states**: the constant of a certificate satisfying (⋆) on the
states is at most `L/N`. -/
theorem ceiling_of_states {ι : Type*} [Fintype ι] (S : ι → State) (w e : ι → ℚ) (Clo : ℚ)
    {C x₁ x₂ b : ℝ} (hmix : MixOK S w e Clo)
    (hstar : ∀ k, ((S k).n1 : ℝ) * x₁ + ((S k).n2 : ℝ) * x₂ - b * (((S k).P : ℚ) : ℝ)
      ≤ ((e k : ℚ) : ℝ))
    (hb : 0 ≤ b) (hD : 0 < 2 - 2 * x₁ + x₂) (hC : ((Clo : ℚ) : ℝ) ≤ C) :
    (3 - C + x₂ - x₁ - b) / (2 - 2 * x₁ + x₂) ≤ ((mixL S w / mixN S w : ℚ) : ℝ) := by
  obtain ⟨hw, hN, hP, hE⟩ := hmix
  have hNr : (0 : ℝ) < ((mixN S w : ℚ) : ℝ) := by exact_mod_cast hN
  have eN : ((mixN S w : ℚ) : ℝ)
      = ∑ k, ((w k : ℚ) : ℝ) * (((S k).n1 : ℝ) + 2 * ((S k).n2 : ℝ)) := by
    unfold mixN
    push_cast
    rfl
  have eL : ((mixL S w : ℚ) : ℝ) = ∑ k, ((w k : ℚ) : ℝ) * (((S k).n1 : ℝ) + ((S k).n2 : ℝ)) := by
    unfold mixL
    push_cast
    rfl
  have hP' : ∑ k, ((w k : ℚ) : ℝ) * (((S k).P : ℚ) : ℝ)
      ≤ ∑ k, ((w k : ℚ) : ℝ) * (((S k).n1 : ℝ) + 2 * ((S k).n2 : ℝ)) := by
    rw [← eN]
    have h : ((mixP S w : ℚ) : ℝ) ≤ ((mixN S w : ℚ) : ℝ) := by exact_mod_cast hP
    unfold mixP at h
    push_cast at h
    exact h
  have hE' : ∑ k, ((w k : ℚ) : ℝ) * (((S k).n1 : ℝ) + 4 * ((S k).n2 : ℝ) + ((e k : ℚ) : ℝ))
      ≤ C * ∑ k, ((w k : ℚ) : ℝ) * (((S k).n1 : ℝ) + 2 * ((S k).n2 : ℝ)) := by
    rw [← eN]
    have h : ((∑ k, w k * ((S k).n1 + 4 * (S k).n2 + e k) : ℚ) : ℝ)
        ≤ ((Clo * mixN S w : ℚ) : ℝ) := by exact_mod_cast hE
    push_cast at h
    exact h.trans (mul_le_mul_of_nonneg_right hC hNr.le)
  have key := ceiling_of_mixture (fun k => ((w k : ℚ) : ℝ)) (fun k => ((S k).n1 : ℝ))
    (fun k => ((S k).n2 : ℝ)) (fun k => (((S k).P : ℚ) : ℝ)) (fun k => ((e k : ℚ) : ℝ))
    (fun k => by exact_mod_cast hw k) hstar hb hP' hE'
  rw [← eN, ← eL] at key
  rw [Rat.cast_div, div_le_div_iff₀ hD hNr]
  linarith

/-! ## Simple points -/

/-- **The weighted sum of (⋆), simple points.** -/
theorem line_ceiling_of_mixture {ι : Type*} [Fintype ι] (w n P e : ι → ℝ) {C x b : ℝ}
    (hw : ∀ k, 0 ≤ w k) (hstar : ∀ k, x * n k - b * P k ≤ e k)
    (hE : ∑ k, w k * (e k - n k) + (2 - C) * ∑ k, w k * P k ≤ 0) :
    (2 - C - b) * ∑ k, w k * P k ≤ (1 - x) * ∑ k, w k * n k := by
  have hE' : ∑ k, w k * (e k - n k) = ∑ k, w k * e k - ∑ k, w k * n k := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  have hS : x * ∑ k, w k * n k - b * ∑ k, w k * P k ≤ ∑ k, w k * e k := by
    have h := sum_le_sum fun k (_ : k ∈ univ) => mul_le_mul_of_nonneg_left (hstar k) (hw k)
    have e1 : x * ∑ k, w k * n k - b * ∑ k, w k * P k = ∑ k, w k * (x * n k - b * P k) := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun k _ => by ring
    rw [e1]
    exact h
  rw [hE'] at hE
  nlinarith

/-- The conditions on the weights for simple points: `w ≥ 0`, `∑ w_k P_k > 0`,
`∑ w_k (e_k - n_k) + (2 - Clo) ∑ w_k P_k ≤ 0`. -/
def LineMixOK {ι : Type*} [Fintype ι] (S : ι → State) (w e : ι → ℚ) (Clo : ℚ) : Prop :=
  (∀ k, 0 ≤ w k) ∧ 0 < mixP S w
    ∧ ∑ k, w k * (e k - (S k).m) + (2 - Clo) * mixP S w ≤ 0

instance {ι : Type*} [Fintype ι] (S : ι → State) (w e : ι → ℚ) (Clo : ℚ) :
    Decidable (LineMixOK S w e Clo) :=
  inferInstanceAs (Decidable ((∀ k, 0 ≤ w k) ∧ 0 < mixP S w
    ∧ ∑ k, w k * (e k - (S k).m) + (2 - Clo) * mixP S w ≤ 0))

/-- number of points of a weighted family of states of simple points: `∑ w_k m_k` -/
def mixM {ι : Type*} [Fintype ι] (S : ι → State) (w : ι → ℚ) : ℚ := ∑ k, w k * (S k).m

/-- **The ceiling of a mixture of states of simple points**: the constant `(2 - C - b)/(1 - x)` of
a certificate satisfying (⋆) on the states is at most `(∑ w_k m_k)/(∑ w_k P_k)`. -/
theorem line_ceiling_of_states {ι : Type*} [Fintype ι] (S : ι → State) (w e : ι → ℚ) (Clo : ℚ)
    {C x b : ℝ} (hmix : LineMixOK S w e Clo)
    (hstar : ∀ k, x * ((S k).m : ℝ) - b * (((S k).P : ℚ) : ℝ) ≤ ((e k : ℚ) : ℝ))
    (hx : x < 1) (hC : ((Clo : ℚ) : ℝ) ≤ C) :
    (2 - C - b) / (1 - x) ≤ ((mixM S w / mixP S w : ℚ) : ℝ) := by
  obtain ⟨hw, hP, hE⟩ := hmix
  have hPr : (0 : ℝ) < ((mixP S w : ℚ) : ℝ) := by exact_mod_cast hP
  have eP : ((mixP S w : ℚ) : ℝ) = ∑ k, ((w k : ℚ) : ℝ) * (((S k).P : ℚ) : ℝ) := by
    unfold mixP
    push_cast
    rfl
  have eM : ((mixM S w : ℚ) : ℝ) = ∑ k, ((w k : ℚ) : ℝ) * ((S k).m : ℝ) := by
    unfold mixM
    push_cast
    rfl
  have hE' : ∑ k, ((w k : ℚ) : ℝ) * (((e k : ℚ) : ℝ) - ((S k).m : ℝ))
      + (2 - C) * ∑ k, ((w k : ℚ) : ℝ) * (((S k).P : ℚ) : ℝ) ≤ 0 := by
    rw [← eP]
    have h : ((∑ k, w k * (e k - (S k).m) + (2 - Clo) * mixP S w : ℚ) : ℝ) ≤ ((0 : ℚ) : ℝ) := by
      exact_mod_cast hE
    push_cast at h
    have h2 : (2 - C) * ((mixP S w : ℚ) : ℝ) ≤ (2 - ((Clo : ℚ) : ℝ)) * ((mixP S w : ℚ) : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hPr.le
    linarith
  have key := line_ceiling_of_mixture (fun k => ((w k : ℚ) : ℝ)) (fun k => ((S k).m : ℝ))
    (fun k => (((S k).P : ℚ) : ℝ)) (fun k => ((e k : ℚ) : ℝ))
    (fun k => by exact_mod_cast hw k) hstar hE'
  rw [← eP, ← eM] at key
  rw [Rat.cast_div, div_le_div_iff₀ (by linarith) hPr]
  linarith

end Ceilings
