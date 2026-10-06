/-
Simple673/Transfer/Potential.lean — the piecewise linear potentials telescope.

The potentials `B_r` of `Defs.lean` are combinations of hat functions with knots
`3/4 + k/8`, `k = 0, …, 13`. Two facts are proved here:

* `Bpot_sum_zero`: `∑_r B_r(t) = 0` for every `t`;
* `Apot_le`, `le_Apot`: the partial sums `A_q = ∑_{r ≤ q} B_r` take values between the
  smallest and the largest of their knot values (the hat functions are nonnegative and add up
  to at most `1`).

Together with the telescoping identity of `Simple673/Transfer/Sums.lean` they give
`sum_window_potential_le`: the potential terms of all windows of a chain add up to at most
`Ω = omegaB = 3882 · 10⁻⁶`.

The hat function is the one of `Distinct839`, and the potentials have the same fourteen knots,
so the lemmas about the hat functions (`hat_nonneg`, `sum_hat_le_one`, `sum_mul_hat_le`,
`le_sum_mul_hat`) are imported from `Distinct839/Transfer/Potential.lean`; the statements about
`Bpot`, `Apot` and `omegaB` concern the tables of `Simple673/Defs.lean` and are proved here.
-/
import Simple673.Transfer.Tables
import Simple673.Transfer.Sums
import Distinct839.Transfer.Potential

open scoped BigOperators
open Finset

namespace Simple673.Transfer

/-! ## The potentials and their partial sums -/

/-- The potentials sum to zero over the position: `∑_r B_r(t) = 0`. -/
theorem Bpot_sum_zero (t : ℝ) : ∑ r : Fin 7, Bpot r t = 0 := by
  unfold Bpot
  rw [sum_comm]
  refine sum_eq_zero fun k _ => ?_
  rw [← sum_mul, ← sum_div]
  have h : ∑ r : Fin 7, (knotTab r k : ℝ) = 0 := by
    exact_mod_cast knotTab_sum_zero k
  rw [h]
  simp

/-- The partial sum `A_q = ∑_{r ≤ q} B_r`, `q = 0, …, 5`. -/
noncomputable def Apot (q : Fin 6) (t : ℝ) : ℝ :=
  ∑ r : Fin 7, if r.val ≤ q.val then Bpot r t else 0

/-- `A_q` is the combination of hat functions with the knot values `cumTab`. -/
theorem Apot_eq (q : Fin 6) (t : ℝ) :
    Apot q t
      = ∑ k : Fin 14, (cumTab q k : ℝ) / 1000000 * hat (8 * (t - (3 / 4 + (k : ℕ) / 8))) := by
  unfold Apot Bpot cumTab
  have h : ∀ r : Fin 7,
      (if r.val ≤ q.val then
        ∑ k : Fin 14, (knotTab r k : ℝ) / 1000000 * hat (8 * (t - (3 / 4 + (k : ℕ) / 8)))
        else 0)
      = ∑ k : Fin 14, (if r.val ≤ q.val then (knotTab r k : ℝ) else 0) / 1000000
          * hat (8 * (t - (3 / 4 + (k : ℕ) / 8))) := by
    intro r
    split_ifs
    · rfl
    · simp
  refine (sum_congr rfl fun r _ => h r).trans ?_
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [← sum_mul, ← sum_div]
  congr 1
  congr 1
  rw [Int.cast_sum]
  refine sum_congr rfl fun r _ => ?_
  split_ifs <;> simp

/-- Upper bound for `A_q`: the largest knot value. -/
theorem Apot_le (q : Fin 6) (t : ℝ) : Apot q t ≤ (oscHi q : ℝ) / 1000000 := by
  rw [Apot_eq]
  refine Distinct839.Transfer.sum_mul_hat_le _ _
    (div_nonneg (by exact_mod_cast oscHi_nonneg q) (by norm_num)) (fun k => ?_) t
  exact div_le_div_of_nonneg_right (by exact_mod_cast cumTab_le q k) (by norm_num)

/-- Lower bound for `A_q`: the smallest knot value. -/
theorem le_Apot (q : Fin 6) (t : ℝ) : (oscLo q : ℝ) / 1000000 ≤ Apot q t := by
  rw [Apot_eq]
  refine Distinct839.Transfer.le_sum_mul_hat _ _
    (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast oscLo_nonpos q) (by norm_num))
    (fun k => ?_) t
  exact div_le_div_of_nonneg_right (by exact_mod_cast le_cumTab q k) (by norm_num)

/-- The total oscillation of the state function is `Ω`. -/
theorem osc_sum_real :
    ∑ q : Fin 6, (oscHi q : ℝ) / 1000000 - ∑ q : Fin 6, (oscLo q : ℝ) / 1000000 = omegaB := by
  have h : ∀ q : Fin 6, (oscHi q : ℝ) / 1000000 - (oscLo q : ℝ) / 1000000
      = ((oscHi q - oscLo q : ℤ) : ℝ) / 1000000 := by
    intro q
    push_cast
    ring
  rw [← sum_sub_distrib, sum_congr rfl fun q _ => h q, ← sum_div, ← Int.cast_sum, osc_sum]
  norm_num [omegaB]

/-! ## The potential terms of all windows -/

/-- Potentials: along a chain with gaps `g p` of consecutive sites, the potential terms of the
`n` windows telescope, and their sum is at most `Ω`. -/
theorem sum_window_potential_le (g : ℕ → ℝ) (n : ℕ) :
    ∑ w ∈ range n, ∑ r : Fin 7, Bpot r (g (w + r)) ≤ omegaB := by
  have h : ∑ w ∈ range n, ∑ r : Fin 7, Bpot r (g (w + r))
      = winState (fun r p => Bpot r (g p)) 0 - winState (fun r p => Bpot r (g p)) n :=
    sum_window_state (fun r p => Bpot r (g p)) (fun p => Bpot_sum_zero _) n
  have hst : ∀ w : ℕ, winState (fun r p => Bpot r (g p)) w
      = ∑ q : Fin 6, Apot q (g (w + q)) := fun w => rfl
  have hhi : winState (fun r p => Bpot r (g p)) 0 ≤ ∑ q : Fin 6, (oscHi q : ℝ) / 1000000 := by
    rw [hst]
    exact sum_le_sum fun q _ => Apot_le _ _
  have hlo : ∑ q : Fin 6, (oscLo q : ℝ) / 1000000 ≤ winState (fun r p => Bpot r (g p)) n := by
    rw [hst]
    exact sum_le_sum fun q _ => le_Apot _ _
  have hosc := osc_sum_real
  linarith

end Simple673.Transfer
