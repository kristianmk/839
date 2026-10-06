/-
Distinct839/Transfer/Potential.lean — the piecewise linear potentials telescope.

The potentials `B_r^{ty}` of `Defs.lean` are combinations of hat functions with knots
`3/4 + k/8`, `k = 0, …, 13`. Two facts are proved here:

* `Bpot_sum_zero`: `∑_r B_r^{ty}(t) = 0` for every type and every `t`;
* `Apot_le`, `le_Apot`: the partial sums `A_q^{ty} = ∑_{r ≤ q} B_r^{ty}` take values between
  the smallest and the largest of their knot values (the hat functions are nonnegative and add
  up to at most `1`).

Together with the telescoping identity of `Sums.lean` they give `sum_window_potential_le`: the
potential terms of all windows of a chain add up to at most `Ω = omegaB`.
-/
import Distinct839.Transfer.Tables
import Distinct839.Transfer.Sums

open scoped BigOperators
open Finset

namespace Distinct839.Transfer

/-! ## Hat functions -/

theorem hat_nonneg (s : ℝ) : 0 ≤ hat s := le_max_left _ _

/-- The ramp: `0` for `u ≤ 0`, `u` on `[0, 1]`, `1` for `u ≥ 1`. -/
def ramp (u : ℝ) : ℝ := max 0 (min u 1)

theorem ramp_nonneg (u : ℝ) : 0 ≤ ramp u := le_max_left _ _

theorem ramp_le_one (u : ℝ) : ramp u ≤ 1 := max_le zero_le_one (min_le_right _ _)

/-- A hat function is a difference of two ramps. -/
theorem hat_eq_ramp_sub (u : ℝ) : hat u = ramp (u + 1) - ramp u := by
  unfold hat ramp
  rw [abs_eq_max_neg]
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- Hat functions at consecutive integer knots add up to at most `1`. -/
theorem sum_range_hat_le_one (s : ℝ) (N : ℕ) : ∑ k ∈ range N, hat (s - (k : ℝ)) ≤ 1 := by
  have h : ∀ k : ℕ, hat (s - (k : ℝ))
      = (-ramp (s - ((k + 1 : ℕ) : ℝ) + 1)) - (-ramp (s - (k : ℝ) + 1)) := by
    intro k
    have e : s - ((k + 1 : ℕ) : ℝ) + 1 = s - (k : ℝ) := by push_cast; ring
    rw [hat_eq_ramp_sub, e]
    ring
  calc ∑ k ∈ range N, hat (s - (k : ℝ))
      = ∑ k ∈ range N,
          ((-ramp (s - ((k + 1 : ℕ) : ℝ) + 1)) - (-ramp (s - (k : ℝ) + 1))) :=
        sum_congr rfl fun k _ => h k
    _ = (-ramp (s - (N : ℝ) + 1)) - (-ramp (s - ((0 : ℕ) : ℝ) + 1)) :=
        sum_range_sub (fun k : ℕ => -ramp (s - (k : ℝ) + 1)) N
    _ ≤ 1 := by
        have h1 := ramp_le_one (s - ((0 : ℕ) : ℝ) + 1)
        have h2 := ramp_nonneg (s - (N : ℝ) + 1)
        linarith

/-- The fourteen hat functions of the potentials add up to at most `1`. -/
theorem sum_hat_le_one (t : ℝ) :
    ∑ k : Fin 14, hat (8 * (t - (3 / 4 + (k : ℕ) / 8))) ≤ 1 := by
  have e : ∑ k : Fin 14, hat (8 * (t - (3 / 4 + ((k : ℕ) : ℝ) / 8)))
      = ∑ k ∈ range 14, hat (8 * t - 6 - (k : ℝ)) := by
    refine Eq.trans ?_ (Fin.sum_univ_eq_sum_range (fun k : ℕ => hat (8 * t - 6 - (k : ℝ))) 14)
    refine sum_congr rfl fun k _ => ?_
    show hat (8 * (t - (3 / 4 + ((k : ℕ) : ℝ) / 8))) = hat (8 * t - 6 - ((k : ℕ) : ℝ))
    congr 1
    ring
  rw [e]
  exact sum_range_hat_le_one _ _

/-- A combination of the hat functions with coefficients `≤ M`, `M ≥ 0`, is at most `M`. -/
theorem sum_mul_hat_le (c : Fin 14 → ℝ) (M : ℝ) (hM : 0 ≤ M) (hc : ∀ k, c k ≤ M) (t : ℝ) :
    ∑ k : Fin 14, c k * hat (8 * (t - (3 / 4 + (k : ℕ) / 8))) ≤ M :=
  calc ∑ k : Fin 14, c k * hat (8 * (t - (3 / 4 + (k : ℕ) / 8)))
      ≤ ∑ k : Fin 14, M * hat (8 * (t - (3 / 4 + (k : ℕ) / 8))) :=
        sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hc k) (hat_nonneg _)
    _ = M * ∑ k : Fin 14, hat (8 * (t - (3 / 4 + (k : ℕ) / 8))) := by rw [mul_sum]
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left (sum_hat_le_one t) hM
    _ = M := mul_one M

/-- A combination of the hat functions with coefficients `≥ m`, `m ≤ 0`, is at least `m`. -/
theorem le_sum_mul_hat (c : Fin 14 → ℝ) (m : ℝ) (hm : m ≤ 0) (hc : ∀ k, m ≤ c k) (t : ℝ) :
    m ≤ ∑ k : Fin 14, c k * hat (8 * (t - (3 / 4 + (k : ℕ) / 8))) := by
  have h := sum_mul_hat_le (fun k => -c k) (-m) (by linarith) (fun k => by linarith [hc k]) t
  simp only [neg_mul, sum_neg_distrib] at h
  linarith

/-! ## The potentials and their partial sums -/

/-- The potentials sum to zero over the position: `∑_r B_r^{ty}(t) = 0`. -/
theorem Bpot_sum_zero (τ : Fin 3) (t : ℝ) : ∑ r : Fin 6, Bpot r τ t = 0 := by
  unfold Bpot
  rw [sum_comm]
  refine sum_eq_zero fun k _ => ?_
  rw [← sum_mul, ← sum_div]
  have h : ∑ r : Fin 6, (knotTab r τ k : ℝ) = 0 := by
    exact_mod_cast knotTab_sum_zero τ k
  rw [h]
  simp

/-- The partial sum `A_q^{ty} = ∑_{r ≤ q} B_r^{ty}`, `q = 0, …, 4`. -/
noncomputable def Apot (q : Fin 5) (τ : Fin 3) (t : ℝ) : ℝ :=
  ∑ r : Fin 6, if r.val ≤ q.val then Bpot r τ t else 0

/-- `A_q^{ty}` is the combination of hat functions with the knot values `cumTab`. -/
theorem Apot_eq (q : Fin 5) (τ : Fin 3) (t : ℝ) :
    Apot q τ t
      = ∑ k : Fin 14, (cumTab q τ k : ℝ) / 1000000 * hat (8 * (t - (3 / 4 + (k : ℕ) / 8))) := by
  unfold Apot Bpot cumTab
  have h : ∀ r : Fin 6,
      (if r.val ≤ q.val then
        ∑ k : Fin 14, (knotTab r τ k : ℝ) / 1000000 * hat (8 * (t - (3 / 4 + (k : ℕ) / 8)))
        else 0)
      = ∑ k : Fin 14, (if r.val ≤ q.val then (knotTab r τ k : ℝ) else 0) / 1000000
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

/-- Upper bound for `A_q^{ty}`: the largest knot value. -/
theorem Apot_le (q : Fin 5) (τ : Fin 3) (t : ℝ) : Apot q τ t ≤ (oscHi q : ℝ) / 1000000 := by
  rw [Apot_eq]
  refine sum_mul_hat_le _ _
    (div_nonneg (by exact_mod_cast oscHi_nonneg q) (by norm_num)) (fun k => ?_) t
  exact div_le_div_of_nonneg_right (by exact_mod_cast cumTab_le q τ k) (by norm_num)

/-- Lower bound for `A_q^{ty}`: the smallest knot value. -/
theorem le_Apot (q : Fin 5) (τ : Fin 3) (t : ℝ) : (oscLo q : ℝ) / 1000000 ≤ Apot q τ t := by
  rw [Apot_eq]
  refine le_sum_mul_hat _ _
    (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast oscLo_nonpos q) (by norm_num))
    (fun k => ?_) t
  exact div_le_div_of_nonneg_right (by exact_mod_cast le_cumTab q τ k) (by norm_num)

/-- The total oscillation of the state function is `Ω`. -/
theorem osc_sum_real :
    ∑ q : Fin 5, (oscHi q : ℝ) / 1000000 - ∑ q : Fin 5, (oscLo q : ℝ) / 1000000 = omegaB := by
  have h : ∀ q : Fin 5, (oscHi q : ℝ) / 1000000 - (oscLo q : ℝ) / 1000000
      = ((oscHi q - oscLo q : ℤ) : ℝ) / 1000000 := by
    intro q
    push_cast
    ring
  rw [← sum_sub_distrib, sum_congr rfl fun q _ => h q, ← sum_div, ← Int.cast_sum, osc_sum]
  norm_num [omegaB]

/-! ## The potential terms of all windows -/

/-- Potentials: along a chain with pair types `τ p` and gaps `g p` of consecutive sites, the
potential terms of the `n` windows telescope, and their sum is at most `Ω`. -/
theorem sum_window_potential_le (τ : ℕ → Fin 3) (g : ℕ → ℝ) (n : ℕ) :
    ∑ w ∈ range n, ∑ r : Fin 6, Bpot r (τ (w + r)) (g (w + r)) ≤ omegaB := by
  have h : ∑ w ∈ range n, ∑ r : Fin 6, Bpot r (τ (w + r)) (g (w + r))
      = winState (fun r p => Bpot r (τ p) (g p)) 0
        - winState (fun r p => Bpot r (τ p) (g p)) n :=
    sum_window_state (fun r p => Bpot r (τ p) (g p)) (fun p => Bpot_sum_zero _ _) n
  have hst : ∀ w : ℕ, winState (fun r p => Bpot r (τ p) (g p)) w
      = ∑ q : Fin 5, Apot q (τ (w + q)) (g (w + q)) := fun w => rfl
  have hhi : winState (fun r p => Bpot r (τ p) (g p)) 0
      ≤ ∑ q : Fin 5, (oscHi q : ℝ) / 1000000 := by
    rw [hst]
    exact sum_le_sum fun q _ => Apot_le _ _ _
  have hlo : ∑ q : Fin 5, (oscLo q : ℝ) / 1000000
      ≤ winState (fun r p => Bpot r (τ p) (g p)) n := by
    rw [hst]
    exact sum_le_sum fun q _ => le_Apot _ _ _
  have hosc := osc_sum_real
  linarith

end Distinct839.Transfer
