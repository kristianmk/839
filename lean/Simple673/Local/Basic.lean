/-
Simple673/Local/Basic.lean — elementary facts about the building blocks of the checker
(`Simple673/Local/Checker.lean`): the signed pairs `SInt`, the small loops, and array reads.
-/
import Mathlib
import Simple673.Local.Checker

open Finset

namespace Simple673
namespace Local

/-! ## Signed pairs -/

namespace SInt

@[simp] theorem toInt_zero : zero.toInt = 0 := by simp [toInt, zero]

@[simp] theorem toInt_ofNat (a : ℕ) : (ofNat a).toInt = a := by simp [toInt, ofNat]

@[simp] theorem toInt_mk (p n : ℕ) : (SInt.mk p n).toInt = (p : ℤ) - n := rfl

@[simp] theorem toInt_add (a b : SInt) : (a.add b).toInt = a.toInt + b.toInt := by
  simp only [toInt, add, Nat.cast_add]; ring

@[simp] theorem toInt_sub (a b : SInt) : (a.sub b).toInt = a.toInt - b.toInt := by
  simp only [toInt, sub, Nat.cast_add]; ring

@[simp] theorem toInt_smul (a : SInt) (c : ℕ) : (a.smul c).toInt = a.toInt * c := by
  simp only [toInt, smul, Nat.cast_mul]; ring

theorem le_iff (a b : SInt) : a.le b = true ↔ a.toInt ≤ b.toInt := by
  simp only [le, toInt, decide_eq_true_eq]; omega

theorem toInt_min (a b : SInt) : (a.min b).toInt = Min.min a.toInt b.toInt := by
  unfold min
  by_cases h : a.le b = true
  · rw [if_pos h, min_eq_left ((le_iff a b).1 h)]
  · rw [if_neg h, min_eq_right]
    have := mt (le_iff a b).2 h
    omega

theorem toInt_min_le_left (a b : SInt) : (a.min b).toInt ≤ a.toInt := by
  rw [toInt_min]; exact Int.min_le_left _ _

theorem toInt_min_le_right (a b : SInt) : (a.min b).toInt ≤ b.toInt := by
  rw [toInt_min]; exact Int.min_le_right _ _

end SInt

/-! ## Loops -/

theorem sumTo_eq (f : ℕ → ℕ) (n : ℕ) : sumTo f n = ∑ k ∈ range n, f k := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => rw [sumTo, ih, sum_range_succ]

theorem toInt_ssumTo (f : ℕ → SInt) (n : ℕ) :
    (ssumTo f n).toInt = ∑ k ∈ range n, (f k).toInt := by
  induction n with
  | zero => simp [ssumTo]
  | succ n ih => rw [ssumTo, SInt.toInt_add, ih, sum_range_succ]

theorem allFromTo_spec (p : ℕ → Bool) :
    ∀ n m, allFromTo p n m = true → ∀ k, m ≤ k → k < m + n → p k = true := by
  intro n
  induction n with
  | zero => intro m _ k h1 h2; omega
  | succ n ih =>
    intro m h k h1 h2
    rw [allFromTo, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h3
    · exact h.1
    · exact ih (m + 1) h.2 k h3 (by omega)

/-! ## Array reads -/

theorem getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) (d : α) (h : i < n) :
    (Array.ofFn f).getD i d = f ⟨i, h⟩ := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem g_setIfInBounds (a : Array ℕ) (r v k : ℕ) :
    g (a.setIfInBounds r v) k = if r = k ∧ r < a.size then v else g a k := by
  unfold g
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h1 : r = k
  · subst h1
    by_cases h2 : r < a.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

end Local
end Simple673
