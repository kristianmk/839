/-
Simple673/Transfer/Tables.lean — finite checks on the frozen integer tables.

The transfer lemma uses four properties of the certificate data in `Defs.lean`:

* the pair weights `Wtab` are nonnegative and satisfy the budgets
  `∑_i W_{i,i+s} ≤ 2 · 10⁶` for every index distance `s = 1, …, 7`
  (the seven sums are 1999996, 1999998, 1999998, 1999998, 1999999, 2000000, 2000000);
* the site rewards sum to `10⁶ x₁ = 8722` (only the fourth point of a frame is rewarded);
* the knot table of the potentials sums to zero over the position `r`;
* the partial sums `A_q = ∑_{r ≤ q} B_r`, `q = 0, …, 5`, of the knot table have total
  oscillation `3882 = 10⁶ Ω`: the sum over `q` of the largest minus the smallest knot value of
  `A_q`. The largest values are `647, 647, 222, 425, 0, 0`, the smallest
  `0, 0, -425, -222, -647, -647` (the first knot value of every `A_q` is `0`, so the largest
  value is never negative and the smallest never positive).

All of them are decided by evaluation of the integer tables (`decide`), and then restated for
the real numbers that occur in `LocalInequality`. There are no labels: all points are simple
zeros, so the tables carry no type index.
-/
import Simple673.Defs

open scoped BigOperators

namespace Simple673.Transfer

/-! ## Integer checks -/

/-- Budget cap `10⁶ · 2`: a pair of simple points has total weight `2` in the pair energy. -/
def capTab : ℤ := 2000000

/-- The pair weights are nonnegative. -/
theorem Wtab_nonneg : ∀ i j : Fin 8, 0 ≤ Wtab i j := by decide

/-- Budget: for each index distance `s + 1 ∈ {1, …, 7}`, the weights of the pairs
`(i, i + s + 1)` sum to at most the cap. -/
theorem Wtab_budget : ∀ s : Fin 7,
    ∑ i : Fin 8, ∑ j : Fin 8, (if j.val = i.val + s.val + 1 then Wtab i j else 0)
      ≤ capTab := by
  decide

/-- The site rewards sum to `10⁶ x₁ = 8722`. -/
theorem hTab_sum : ∑ i : Fin 8, hTab i = 8722 := by decide

/-- The knot table of the potentials sums to zero over the position `r`. -/
theorem knotTab_sum_zero : ∀ k : Fin 14, ∑ r : Fin 7, knotTab r k = 0 := by decide

/-- Knot values of the partial sums `A_q = ∑_{r ≤ q} B_r`, `q = 0, …, 5`. -/
def cumTab (q : Fin 6) (k : Fin 14) : ℤ :=
  ∑ r : Fin 7, if r.val ≤ q.val then knotTab r k else 0

/-- Upper bounds for the knot values of `A_q`; each entry is the maximum over the knots. -/
def oscHi : Fin 6 → ℤ := ![647, 647, 222, 425, 0, 0]

/-- Lower bounds for the knot values of `A_q`; each entry is the minimum over the knots. -/
def oscLo : Fin 6 → ℤ := ![0, 0, -425, -222, -647, -647]

/-- Every knot value of `A_q` is at most `oscHi q`. -/
theorem cumTab_le : ∀ (q : Fin 6) (k : Fin 14), cumTab q k ≤ oscHi q := by decide

/-- Every knot value of `A_q` is at least `oscLo q`. -/
theorem le_cumTab : ∀ (q : Fin 6) (k : Fin 14), oscLo q ≤ cumTab q k := by decide

/-- The upper bounds are nonnegative (needed because the hat functions sum to at most `1`). -/
theorem oscHi_nonneg : ∀ q : Fin 6, 0 ≤ oscHi q := by decide

/-- The lower bounds are nonpositive. -/
theorem oscLo_nonpos : ∀ q : Fin 6, oscLo q ≤ 0 := by decide

/-- The total oscillation is `3882 = 10⁶ Ω`. -/
theorem osc_sum : ∑ q : Fin 6, (oscHi q - oscLo q) = 3882 := by decide

/-! ## Weights and rewards as real numbers -/

/-- The pair weights are nonnegative, as real numbers. -/
theorem Wtab_real_nonneg (i j : Fin 8) : 0 ≤ (Wtab i j : ℝ) / 1000000 :=
  div_nonneg (by exact_mod_cast Wtab_nonneg i j) (by norm_num)

/-- Budget, as real numbers: the weights of the pairs at index distance `s + 1` sum to at
most `2`. -/
theorem Wtab_budget_real (s : Fin 7) :
    ∑ i : Fin 8, ∑ j : Fin 8,
        (if j.val = i.val + s.val + 1 then (Wtab i j : ℝ) / 1000000 else 0) ≤ 2 := by
  have h : ((∑ i : Fin 8, ∑ j : Fin 8,
      (if j.val = i.val + s.val + 1 then Wtab i j else 0) : ℤ) : ℝ) ≤ (capTab : ℝ) := by
    exact_mod_cast Wtab_budget s
  have e : ∑ i : Fin 8, ∑ j : Fin 8,
        (if j.val = i.val + s.val + 1 then (Wtab i j : ℝ) / 1000000 else 0)
      = ((∑ i : Fin 8, ∑ j : Fin 8,
          (if j.val = i.val + s.val + 1 then Wtab i j else 0) : ℤ) : ℝ) / 1000000 := by
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hc : (capTab : ℝ) / 1000000 = 2 := by norm_num [capTab]
  rw [e, ← hc]
  exact div_le_div_of_nonneg_right h (by norm_num)

/-- The rewards over the eight local positions sum to `x₁`. -/
theorem sum_hTab_real : ∑ i : Fin 8, (hTab i : ℝ) / 1000000 = rewX := by
  rw [← Finset.sum_div, ← Int.cast_sum, hTab_sum]
  norm_num [rewX]

end Simple673.Transfer
