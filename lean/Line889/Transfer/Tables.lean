/-
Line889/Transfer/Tables.lean — finite checks on the frozen integer tables.

The transfer lemma uses four properties of the certificate data in `Defs.lean`:

* the pair weights `Wtab` are nonnegative and satisfy the budgets
  `∑_i W_{i,i+s} ≤ 2 · 10⁶` for every index distance `s = 1, …, 6`
  (the six sums are 1999998, 1999998, 1999998, 1999998, 2000000, 2000000);
* the site rewards sum to `10⁶ x = 54525` (only the middle point of a frame is rewarded);
* the knot table of the potentials sums to zero over the position `r`;
* the partial sums over `r` of the knot table have total oscillation `75420 = 10⁶ Ω`.

All of them are decided by evaluation of the integer tables (`decide`), and then restated for
the real numbers that occur in `LocalInequality`. There are no labels: all points are simple
zeros, so the tables carry no type index.
-/
import Line889.Defs

open scoped BigOperators

namespace Line889.Transfer

/-! ## Integer checks -/

/-- Budget cap `10⁶ · 2`: a pair of simple points has total weight `2` in the pair energy. -/
def capTab : ℤ := 2000000

/-- The pair weights are nonnegative. -/
theorem Wtab_nonneg : ∀ i j : Fin 7, 0 ≤ Wtab i j := by decide

/-- Budget: for each index distance `s + 1 ∈ {1, …, 6}`, the weights of the pairs
`(i, i + s + 1)` sum to at most the cap. -/
theorem Wtab_budget : ∀ s : Fin 6,
    ∑ i : Fin 7, ∑ j : Fin 7, (if j.val = i.val + s.val + 1 then Wtab i j else 0)
      ≤ capTab := by
  decide

/-- The site rewards sum to `10⁶ x = 54525`. -/
theorem hTab_sum : ∑ i : Fin 7, hTab i = 54525 := by decide

/-- The knot table of the potentials sums to zero over the position `r`. -/
theorem knotTab_sum_zero : ∀ k : Fin 14, ∑ r : Fin 6, knotTab r k = 0 := by decide

/-- Knot values of the partial sums `A_q = ∑_{r ≤ q} B_r`, `q = 0, …, 4`. -/
def cumTab (q : Fin 5) (k : Fin 14) : ℤ :=
  ∑ r : Fin 6, if r.val ≤ q.val then knotTab r k else 0

/-- Upper bounds for the knot values of `A_q`; each entry is the maximum over the knots. -/
def oscHi : Fin 5 → ℤ := ![19098, 16069, 0, 2543, 0]

/-- Lower bounds for the knot values of `A_q`; each entry is the minimum over the knots. -/
def oscLo : Fin 5 → ℤ := ![0, -2543, 0, -16069, -19098]

/-- Every knot value of `A_q` is at most `oscHi q`. -/
theorem cumTab_le : ∀ (q : Fin 5) (k : Fin 14), cumTab q k ≤ oscHi q := by decide

/-- Every knot value of `A_q` is at least `oscLo q`. -/
theorem le_cumTab : ∀ (q : Fin 5) (k : Fin 14), oscLo q ≤ cumTab q k := by decide

/-- The upper bounds are nonnegative (needed because the hat functions sum to at most `1`). -/
theorem oscHi_nonneg : ∀ q : Fin 5, 0 ≤ oscHi q := by decide

/-- The lower bounds are nonpositive. -/
theorem oscLo_nonpos : ∀ q : Fin 5, oscLo q ≤ 0 := by decide

/-- The total oscillation is `75420 = 10⁶ Ω`. -/
theorem osc_sum : ∑ q : Fin 5, (oscHi q - oscLo q) = 75420 := by decide

/-! ## Weights and rewards as real numbers -/

/-- The pair weights are nonnegative, as real numbers. -/
theorem Wtab_real_nonneg (i j : Fin 7) : 0 ≤ (Wtab i j : ℝ) / 1000000 :=
  div_nonneg (by exact_mod_cast Wtab_nonneg i j) (by norm_num)

/-- Budget, as real numbers: the weights of the pairs at index distance `s + 1` sum to at
most `2`. -/
theorem Wtab_budget_real (s : Fin 6) :
    ∑ i : Fin 7, ∑ j : Fin 7,
        (if j.val = i.val + s.val + 1 then (Wtab i j : ℝ) / 1000000 else 0) ≤ 2 := by
  have h : ((∑ i : Fin 7, ∑ j : Fin 7,
      (if j.val = i.val + s.val + 1 then Wtab i j else 0) : ℤ) : ℝ) ≤ (capTab : ℝ) := by
    exact_mod_cast Wtab_budget s
  have e : ∑ i : Fin 7, ∑ j : Fin 7,
        (if j.val = i.val + s.val + 1 then (Wtab i j : ℝ) / 1000000 else 0)
      = ((∑ i : Fin 7, ∑ j : Fin 7,
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

/-- The rewards over the seven local positions sum to `x`. -/
theorem sum_hTab_real : ∑ i : Fin 7, (hTab i : ℝ) / 1000000 = rewX := by
  rw [← Finset.sum_div, ← Int.cast_sum, hTab_sum]
  norm_num [rewX]

end Line889.Transfer
