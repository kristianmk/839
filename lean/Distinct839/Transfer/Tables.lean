/-
Distinct839/Transfer/Tables.lean — finite checks on the frozen integer tables.

The transfer lemma uses four properties of the certificate data in `Defs.lean`:

* the pair weights `Wtab` are nonnegative and satisfy the budgets
  `∑_i W^{ty}_{i,i+s} ≤ 2ab · 10⁶` for every index distance `s = 1, …, 6`;
* the site rewards satisfy `hTab 0 i ≤ hTab 1 i`, and their sums are `10⁶ x` and `10⁶ y`;
* the knot table of the potentials sums to zero over the position `r`;
* the partial sums over `r` of the knot table have total oscillation `15882 = 10⁶ Ω`.

All of them are decided by evaluation of the integer tables (`decide`), and then restated for
the real numbers that occur in `LocalInequality`.
-/
import Distinct839.Defs

open scoped BigOperators

namespace Distinct839.Transfer

/-! ## Integer checks -/

/-- Budget caps `10⁶ · 2ab` for the three pair types `(1,1)`, `(1,2)`, `(2,2)`. -/
def capTab : Fin 3 → ℤ := ![2000000, 4000000, 8000000]

/-- The pair weights are nonnegative. -/
theorem Wtab_nonneg : ∀ (τ : Fin 3) (i j : Fin 7), 0 ≤ Wtab τ i j := by decide

/-- Budget: for each pair type and each index distance `s + 1 ∈ {1, …, 6}`, the weights of the
pairs `(i, i + s + 1)` sum to at most the cap of the type. -/
theorem Wtab_budget : ∀ (τ : Fin 3) (s : Fin 6),
    ∑ i : Fin 7, ∑ j : Fin 7, (if j.val = i.val + s.val + 1 then Wtab τ i j else 0)
      ≤ capTab τ := by
  decide

/-- The cap of the pair type of two labels is `2 · 10⁶` times the product of the
multiplicities. -/
theorem capTab_pairTy : ∀ a b : Fin 2,
    capTab (pairTy a b) = 2000000 * ((a.val : ℤ) + 1) * ((b.val : ℤ) + 1) := by
  decide

/-- The site rewards sum to `10⁶ x = 54350` (simple) and `10⁶ y = 69433` (double). -/
theorem hTab_sum : ∀ a : Fin 2, ∑ i : Fin 7, hTab a i = if a = 0 then 54350 else 69433 := by
  decide

/-- The reward of a simple site is at most the reward of a double site. -/
theorem hTab_le : ∀ (a : Fin 2) (i : Fin 7), hTab a i ≤ hTab 1 i := by decide

/-- The knot table of the potentials sums to zero over the position `r`. -/
theorem knotTab_sum_zero : ∀ (τ : Fin 3) (k : Fin 14), ∑ r : Fin 6, knotTab r τ k = 0 := by
  decide

/-- Knot values of the partial sums `A_q^{ty} = ∑_{r ≤ q} B_r^{ty}`, `q = 0, …, 4`. -/
def cumTab (q : Fin 5) (τ : Fin 3) (k : Fin 14) : ℤ :=
  ∑ r : Fin 6, if r.val ≤ q.val then knotTab r τ k else 0

/-- Upper bounds for the knot values of `A_q`; each entry is the maximum over the types and
the knots. -/
def oscHi : Fin 5 → ℤ := ![2124, 2113, 0, 1790, 1914]

/-- Lower bounds for the knot values of `A_q`; each entry is the minimum over the types and
the knots. -/
def oscLo : Fin 5 → ℤ := ![-1914, -1790, 0, -2113, -2124]

/-- Every knot value of `A_q` is at most `oscHi q`. -/
theorem cumTab_le : ∀ (q : Fin 5) (τ : Fin 3) (k : Fin 14), cumTab q τ k ≤ oscHi q := by decide

/-- Every knot value of `A_q` is at least `oscLo q`. -/
theorem le_cumTab : ∀ (q : Fin 5) (τ : Fin 3) (k : Fin 14), oscLo q ≤ cumTab q τ k := by decide

/-- The upper bounds are nonnegative (needed because the hat functions sum to at most `1`). -/
theorem oscHi_nonneg : ∀ q : Fin 5, 0 ≤ oscHi q := by decide

/-- The lower bounds are nonpositive. -/
theorem oscLo_nonpos : ∀ q : Fin 5, oscLo q ≤ 0 := by decide

/-- The total oscillation is `15882 = 10⁶ Ω`. -/
theorem osc_sum : ∑ q : Fin 5, (oscHi q - oscLo q) = 15882 := by decide

/-! ## Multiplicities and rewards as real numbers -/

theorem mulOf_eq (a : Fin 2) : mulOf a = (a.val : ℝ) + 1 := rfl

theorem one_le_mulOf (a : Fin 2) : 1 ≤ mulOf a := by
  have h : (0 : ℝ) ≤ (a.val : ℝ) := Nat.cast_nonneg a.val
  rw [mulOf_eq]; linarith

theorem mulOf_nonneg (a : Fin 2) : 0 ≤ mulOf a := le_trans zero_le_one (one_le_mulOf a)

theorem mulOf_le_two (a : Fin 2) : mulOf a ≤ 2 := by
  have h' : a.val ≤ 1 := by have := a.isLt; omega
  have h : (a.val : ℝ) ≤ 1 := by exact_mod_cast h'
  rw [mulOf_eq]; linarith

/-- `rew a ≤ y`. -/
theorem rew_le_rewY (a : Fin 2) : rew a ≤ rewY := by
  unfold rew; split_ifs
  · norm_num [rewX, rewY]
  · exact le_rfl

/-- The cap of a pair type, as a real number: `2 m_a m_b`. -/
theorem capTab_pairTy_real (a b : Fin 2) :
    (capTab (pairTy a b) : ℝ) / 1000000 = 2 * mulOf a * mulOf b := by
  rw [capTab_pairTy a b, mulOf_eq, mulOf_eq]
  push_cast
  ring

/-- The pair weights are nonnegative, as real numbers. -/
theorem Wtab_real_nonneg (τ : Fin 3) (i j : Fin 7) : 0 ≤ (Wtab τ i j : ℝ) / 1000000 :=
  div_nonneg (by exact_mod_cast Wtab_nonneg τ i j) (by norm_num)

/-- Budget, as real numbers: the weights of the pairs at index distance `s + 1` with labels
`a`, `b` sum to at most `2 m_a m_b`. -/
theorem Wtab_budget_real (a b : Fin 2) (s : Fin 6) :
    ∑ i : Fin 7, ∑ j : Fin 7,
        (if j.val = i.val + s.val + 1 then (Wtab (pairTy a b) i j : ℝ) / 1000000 else 0)
      ≤ 2 * mulOf a * mulOf b := by
  have h : ((∑ i : Fin 7, ∑ j : Fin 7,
      (if j.val = i.val + s.val + 1 then Wtab (pairTy a b) i j else 0) : ℤ) : ℝ)
        ≤ (capTab (pairTy a b) : ℝ) := by
    exact_mod_cast Wtab_budget (pairTy a b) s
  have e : ∑ i : Fin 7, ∑ j : Fin 7,
        (if j.val = i.val + s.val + 1 then (Wtab (pairTy a b) i j : ℝ) / 1000000 else 0)
      = ((∑ i : Fin 7, ∑ j : Fin 7,
          (if j.val = i.val + s.val + 1 then Wtab (pairTy a b) i j else 0) : ℤ) : ℝ)
        / 1000000 := by
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [e, ← capTab_pairTy_real]
  exact div_le_div_of_nonneg_right h (by norm_num)

/-- The rewards of a label over the seven local positions sum to `rew`. -/
theorem sum_hTab_real (a : Fin 2) : ∑ i : Fin 7, (hTab a i : ℝ) / 1000000 = rew a := by
  rw [← Finset.sum_div, ← Int.cast_sum, hTab_sum a]
  unfold rew
  split_ifs <;> norm_num [rewX, rewY]

/-- `0 ≤ h_{i,a} ≤ h_{i,2}`, as real numbers. -/
theorem hTab_real_le (a : Fin 2) (i : Fin 7) :
    (hTab a i : ℝ) / 1000000 ≤ (hTab 1 i : ℝ) / 1000000 :=
  div_le_div_of_nonneg_right (by exact_mod_cast hTab_le a i) (by norm_num)

/-- `∑_i h_{i,2} = y`. -/
theorem sum_hTab_one_real : ∑ i : Fin 7, (hTab 1 i : ℝ) / 1000000 = rewY := by
  rw [sum_hTab_real]; simp [rew]

end Distinct839.Transfer
