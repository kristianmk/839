/-
Simple673/Sum10.lean — a sum over `Fin 10`, written out.

The window has ten cosine terms, so sums over `Fin 10` occur in every layer that uses the values
of the coefficients. Mathlib writes out sums over `Fin n` for `n ≤ 8` (`Fin.sum_univ_eight`);
this file adds the cases `n = 9` and `n = 10`, in the same form. It depends on Mathlib only and
contains nothing about the window.
-/
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace Simple673

/-- A sum over `Fin 9`, written out. -/
theorem sum_univ_nine {M : Type*} [AddCommMonoid M] (f : Fin 9 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_eight]
  rfl

/-- A sum over `Fin 10`, written out. -/
theorem sum_univ_ten {M : Type*} [AddCommMonoid M] (f : Fin 10 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  rw [Fin.sum_univ_castSucc, sum_univ_nine]
  rfl

end Simple673
