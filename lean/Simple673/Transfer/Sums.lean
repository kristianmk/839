/-
Simple673/Transfer/Sums.lean — finite sums over the windows of a chain.

A chain has `n + 7` sites `0, …, n + 6` and `n` windows of eight consecutive sites; window `w`
consists of the sites `w, …, w + 7`. This file contains the bookkeeping that turns sums over
windows into sums over sites, gaps and pairs. Nothing here depends on the certificate data, so
the file imports only the part of Mathlib it uses. (`Distinct839/Transfer/Sums.lean` has the
same statements for windows of seven sites.) Main statements:

* `sum_range_le_sum_shift_add`: a local position misses exactly seven sites (rewards);
* `sum_window_gaps`: every gap lies in at most seven windows (pressure);
* `sum_window_state`: a family `b r p` with `∑_r b r p = 0` telescopes (potentials);
* `sum_window_pairs_le`: pairs, grouped by index distance, with a weight budget;
* `sum_offdiag_eq`, `sum_near_pairs_le`: pairs at index distance at most seven inside the
  sum over all ordered pairs.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open scoped BigOperators
open Finset

namespace Simple673.Transfer

/-! ## Shifted sums -/

/-- A sum over `range (i + n + k)` splits into a head of `i` terms, a middle of `n` terms and a
tail of `k` terms. -/
theorem sum_range_split (f : ℕ → ℝ) (i n k : ℕ) :
    ∑ p ∈ range (i + n + k), f p
      = ∑ p ∈ range i, f p + ∑ w ∈ range n, f (w + i) + ∑ x ∈ range k, f (i + n + x) := by
  rw [sum_range_add, sum_range_add]
  have h : ∑ x ∈ range n, f (i + x) = ∑ w ∈ range n, f (w + i) :=
    sum_congr rfl fun w _ => by rw [add_comm]
  rw [h]

/-- A shifted sum of a nonnegative function is at most the full sum. -/
theorem sum_shift_le (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p) (n i N : ℕ) (h : i + n ≤ N) :
    ∑ w ∈ range n, f (w + i) ≤ ∑ p ∈ range N, f p := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [sum_range_split]
  have h1 : 0 ≤ ∑ p ∈ range i, f p := sum_nonneg fun p _ => hf p
  have h2 : 0 ≤ ∑ x ∈ range k, f (i + n + x) := sum_nonneg fun x _ => hf _
  linarith

/-- Rewards: the local position `i` of the `n` windows visits all `n + 7` sites except seven. If
`f ≤ c`, the full sum exceeds the sum over the windows by at most `7 c`. -/
theorem sum_range_le_sum_shift_add (f : ℕ → ℝ) (c : ℝ) (n i : ℕ) (hi : i ≤ 7)
    (hf : ∀ p, f p ≤ c) :
    ∑ p ∈ range (n + 7), f p ≤ ∑ w ∈ range n, f (w + i) + 7 * c := by
  have h7 : n + 7 = i + n + (7 - i) := by omega
  rw [h7, sum_range_split]
  have h1 : ∑ p ∈ range i, f p ≤ (i : ℝ) * c :=
    calc ∑ p ∈ range i, f p ≤ ∑ _p ∈ range i, c := sum_le_sum fun p _ => hf p
      _ = (i : ℝ) * c := by simp
  have h2 : ∑ x ∈ range (7 - i), f (i + n + x) ≤ ((7 - i : ℕ) : ℝ) * c :=
    calc ∑ x ∈ range (7 - i), f (i + n + x) ≤ ∑ _x ∈ range (7 - i), c :=
          sum_le_sum fun x _ => hf _
      _ = ((7 - i : ℕ) : ℝ) * c := by simp
  have h3 : (i : ℝ) + ((7 - i : ℕ) : ℝ) = 7 := by
    have : i + (7 - i) = 7 := by omega
    exact_mod_cast this
  have h4 : (i : ℝ) * c + ((7 - i : ℕ) : ℝ) * c = 7 * c := by rw [← add_mul, h3]
  linarith

/-! ## Gaps -/

/-- Pressure: the gaps of all windows add up to seven differences `Y (n + r) - Y r`. -/
theorem sum_window_gaps (Y : ℕ → ℝ) (n : ℕ) :
    ∑ w ∈ range n, ∑ r : Fin 7, (Y (w + r + 1) - Y (w + r))
      = ∑ r : Fin 7, (Y (n + r) - Y r) := by
  rw [sum_comm]
  refine sum_congr rfl fun r _ => ?_
  have h := sum_range_sub (fun w => Y (w + r)) n
  simp only [zero_add] at h
  rw [← h]
  refine sum_congr rfl fun w _ => ?_
  rw [add_right_comm w (r : ℕ) 1]

/-! ## Telescoping of a family with zero sum over the position -/

/-- The state function: with `A_q = ∑_{r ≤ q} b_r`, the state of window `w` is
`∑_{q=0}^{5} A_q (w + q)`. -/
def winState (b : Fin 7 → ℕ → ℝ) (w : ℕ) : ℝ :=
  ∑ q : Fin 6, ∑ r : Fin 7, if r.val ≤ q.val then b r (w + q) else 0

/-- One window: `∑_r b_r (w + r)` is the state of window `w` minus the state of window `w + 1`,
if the `b_r (w + 6)` sum to zero. -/
theorem sum_window_eq_state_sub (b : Fin 7 → ℕ → ℝ) (w : ℕ)
    (hb : ∑ r : Fin 7, b r (w + 6) = 0) :
    ∑ r : Fin 7, b r (w + r) = winState b w - winState b (w + 1) := by
  unfold winState
  rw [Fin.sum_univ_seven] at hb
  simp only [Fin.sum_univ_seven, Fin.sum_univ_six]
  norm_num [add_assoc]
  linarith

/-- All windows: the sum telescopes to the first state minus the state after the last. -/
theorem sum_window_state (b : Fin 7 → ℕ → ℝ) (hb : ∀ p, ∑ r : Fin 7, b r p = 0) (n : ℕ) :
    ∑ w ∈ range n, ∑ r : Fin 7, b r (w + r) = winState b 0 - winState b n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, sum_window_eq_state_sub b n (hb _)]; ring

/-! ## Pairs -/

/-- Two local positions `i < j` have exactly one index distance `s + 1`, `s = 0, …, 6`. -/
theorem sum_dist_ite (i j : Fin 8) (x : ℝ) :
    ∑ s : Fin 7, (if j.val = i.val + s.val + 1 then x else 0) = if i < j then x else 0 := by
  have hj := j.isLt
  by_cases h : i < j
  · have hlt : i.val < j.val := h
    have hs : ∀ s : Fin 7,
        (j.val = i.val + s.val + 1) ↔ s = ⟨j.val - i.val - 1, by omega⟩ := by
      intro s
      constructor
      · intro hji
        apply Fin.ext
        show s.val = j.val - i.val - 1
        omega
      · intro hs
        have : s.val = j.val - i.val - 1 := congrArg Fin.val hs
        omega
    simp [hs, h]
  · have hs : ∀ s : Fin 7, ¬ (j.val = i.val + s.val + 1) := by
      intro s hji
      exact h (Fin.lt_def.mpr (by omega))
    simp [hs, h]

/-- A sum over the pairs `i < j` of local positions, grouped by index distance. -/
theorem sum_pairs_by_dist (X : Fin 8 → Fin 8 → ℝ) :
    ∑ i : Fin 8, ∑ j : Fin 8, (if i < j then X i j else 0)
      = ∑ s : Fin 7, ∑ i : Fin 8, ∑ j : Fin 8,
          (if j.val = i.val + s.val + 1 then X i j else 0) := by
  calc ∑ i : Fin 8, ∑ j : Fin 8, (if i < j then X i j else 0)
      = ∑ i : Fin 8, ∑ j : Fin 8, ∑ s : Fin 7,
          (if j.val = i.val + s.val + 1 then X i j else 0) :=
        sum_congr rfl fun i _ => sum_congr rfl fun j _ => (sum_dist_ite i j _).symm
    _ = ∑ i : Fin 8, ∑ s : Fin 7, ∑ j : Fin 8,
          (if j.val = i.val + s.val + 1 then X i j else 0) :=
        sum_congr rfl fun i _ => sum_comm
    _ = ∑ s : Fin 7, ∑ i : Fin 8, ∑ j : Fin 8,
          (if j.val = i.val + s.val + 1 then X i j else 0) := sum_comm

/-- A sum over a finite set commutes with a conditional double sum over local positions. -/
theorem sum_sum_sum_ite_comm (S : Finset ℕ) (P : Fin 8 → Fin 8 → Prop)
    [∀ i j, Decidable (P i j)] (G : Fin 8 → Fin 8 → ℕ → ℝ) :
    ∑ p ∈ S, ∑ i : Fin 8, ∑ j : Fin 8, (if P i j then G i j p else 0)
      = ∑ i : Fin 8, ∑ j : Fin 8, (if P i j then ∑ p ∈ S, G i j p else 0) := by
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  split_ifs
  · rfl
  · simp

/-- The contribution of the local pair `(i, j)` at the site `p`, for the index distance
`s + 1`: the site `p` is paired with `p + s + 1`, if this is a site of the chain. -/
def pairTerm (n : ℕ) (c : ℕ → ℕ → Fin 8 → Fin 8 → ℝ) (u : ℕ → ℕ → ℝ)
    (s : Fin 7) (i j : Fin 8) (p : ℕ) : ℝ :=
  if p + s + 1 < n + 7 then c p (p + s + 1) i j * u p (p + s + 1) else 0

/-- Pairs. In each window the pair of local positions `i < j` has the weight
`c (w + i) (w + j) i j ≥ 0`, which depends on the two sites only through the pair. If the
weights of the local pairs at each index distance sum to at most `cap`, then the sum over all
windows is at most the sum, over the pairs of sites at index distance at most seven, of
`cap · u`. -/
theorem sum_window_pairs_le (n : ℕ) (c : ℕ → ℕ → Fin 8 → Fin 8 → ℝ) (cap u : ℕ → ℕ → ℝ)
    (hc : ∀ p q i j, 0 ≤ c p q i j)
    (hcap : ∀ p q (s : Fin 7),
      ∑ i : Fin 8, ∑ j : Fin 8, (if j.val = i.val + s.val + 1 then c p q i j else 0) ≤ cap p q)
    (hu : ∀ p q, p < q → q < n + 7 → 0 ≤ u p q) :
    ∑ w ∈ range n, ∑ i : Fin 8, ∑ j : Fin 8,
        (if i < j then c (w + i) (w + j) i j * u (w + i) (w + j) else 0)
      ≤ ∑ s : Fin 7, ∑ p ∈ range (n + 7),
          (if p + s + 1 < n + 7 then cap p (p + s + 1) * u p (p + s + 1) else 0) := by
  have hF0 : ∀ (s : Fin 7) (i j : Fin 8) (p : ℕ), 0 ≤ pairTerm n c u s i j p := by
    intro s i j p
    unfold pairTerm
    split_ifs with h
    · exact mul_nonneg (hc _ _ _ _) (hu _ _ (by omega) h)
    · exact le_rfl
  -- Step 1: group the pairs by index distance and sum over the windows first.
  have h1 : ∑ w ∈ range n, ∑ i : Fin 8, ∑ j : Fin 8,
        (if i < j then c (w + i) (w + j) i j * u (w + i) (w + j) else 0)
      = ∑ s : Fin 7, ∑ i : Fin 8, ∑ j : Fin 8,
          (if j.val = i.val + s.val + 1 then ∑ w ∈ range n, pairTerm n c u s i j (w + i)
            else 0) := by
    calc ∑ w ∈ range n, ∑ i : Fin 8, ∑ j : Fin 8,
          (if i < j then c (w + i) (w + j) i j * u (w + i) (w + j) else 0)
        = ∑ w ∈ range n, ∑ s : Fin 7, ∑ i : Fin 8, ∑ j : Fin 8,
            (if j.val = i.val + s.val + 1 then pairTerm n c u s i j (w + i) else 0) := by
          refine sum_congr rfl fun w hw => ?_
          refine (sum_pairs_by_dist
            (fun i j => c (w + i) (w + j) i j * u (w + i) (w + j))).trans ?_
          refine sum_congr rfl fun s _ => sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
          split_ifs with hj
          · have hw' := mem_range.mp hw
            have hj' := j.isLt
            have e : w + j.val = w + i.val + s.val + 1 := by omega
            have e2 : w + i.val + s.val + 1 < n + 7 := by omega
            show c (w + i) (w + j) i j * u (w + i) (w + j) = pairTerm n c u s i j (w + i)
            rw [pairTerm, if_pos e2, e]
          · rfl
      _ = ∑ s : Fin 7, ∑ w ∈ range n, ∑ i : Fin 8, ∑ j : Fin 8,
            (if j.val = i.val + s.val + 1 then pairTerm n c u s i j (w + i) else 0) :=
          sum_comm
      _ = ∑ s : Fin 7, ∑ i : Fin 8, ∑ j : Fin 8,
          (if j.val = i.val + s.val + 1 then ∑ w ∈ range n, pairTerm n c u s i j (w + i)
            else 0) :=
          sum_congr rfl fun s _ =>
            sum_sum_sum_ite_comm (range n) (fun i j => j.val = i.val + s.val + 1)
              (fun i j w => pairTerm n c u s i j (w + i))
  rw [h1]
  refine sum_le_sum fun s _ => ?_
  -- Step 2: a local pair, summed over the windows, is at most its sum over all sites.
  have h2 : ∀ i j : Fin 8, j.val = i.val + s.val + 1 →
      ∑ w ∈ range n, pairTerm n c u s i j (w + i)
        ≤ ∑ p ∈ range (n + 7), pairTerm n c u s i j p := by
    intro i j hj
    have hj' := j.isLt
    exact sum_shift_le _ (hF0 s i j) n i (n + 7) (by omega)
  calc ∑ i : Fin 8, ∑ j : Fin 8,
        (if j.val = i.val + s.val + 1 then ∑ w ∈ range n, pairTerm n c u s i j (w + i) else 0)
      ≤ ∑ i : Fin 8, ∑ j : Fin 8,
        (if j.val = i.val + s.val + 1 then ∑ p ∈ range (n + 7), pairTerm n c u s i j p
          else 0) := by
        refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
        split_ifs with hj
        · exact h2 i j hj
        · exact le_rfl
    _ = ∑ p ∈ range (n + 7), ∑ i : Fin 8, ∑ j : Fin 8,
          (if j.val = i.val + s.val + 1 then pairTerm n c u s i j p else 0) :=
        (sum_sum_sum_ite_comm (range (n + 7)) (fun i j => j.val = i.val + s.val + 1)
          (fun i j p => pairTerm n c u s i j p)).symm
    _ ≤ ∑ p ∈ range (n + 7),
          (if p + s + 1 < n + 7 then cap p (p + s + 1) * u p (p + s + 1) else 0) := by
        -- Step 3: at each site, use the budget.
        refine sum_le_sum fun p _ => ?_
        unfold pairTerm
        by_cases hp : p + s + 1 < n + 7
        · simp only [if_pos hp]
          calc ∑ i : Fin 8, ∑ j : Fin 8,
                (if j.val = i.val + s.val + 1 then c p (p + s + 1) i j * u p (p + s + 1)
                  else 0)
              = (∑ i : Fin 8, ∑ j : Fin 8,
                  (if j.val = i.val + s.val + 1 then c p (p + s + 1) i j else 0))
                  * u p (p + s + 1) := by
                rw [sum_mul]
                refine sum_congr rfl fun i _ => ?_
                rw [sum_mul]
                refine sum_congr rfl fun j _ => ?_
                split_ifs <;> simp
            _ ≤ cap p (p + s + 1) * u p (p + s + 1) :=
                mul_le_mul_of_nonneg_right (hcap _ _ s) (hu _ _ (by omega) hp)
        · simp only [if_neg hp]
          simp

/-- A sum over ordered pairs of distinct sites is a sum over the pairs `p < q` of the two
orders. -/
theorem sum_offdiag_eq (ℓ : ℕ) (c : ℕ → ℕ → ℝ) :
    ∑ p ∈ range ℓ, ∑ q ∈ range ℓ, (if p ≠ q then c p q else 0)
      = ∑ p ∈ range ℓ, ∑ q ∈ range ℓ, (if p < q then c p q + c q p else 0) := by
  have h : ∀ p q : ℕ, (if p ≠ q then c p q else 0)
      = (if p < q then c p q else 0) + (if q < p then c p q else 0) := by
    intro p q
    rcases lt_trichotomy p q with h | h | h
    · simp [h, h.ne, lt_asymm h]
    · subst h; simp
    · simp [h, h.ne', lt_asymm h]
  calc ∑ p ∈ range ℓ, ∑ q ∈ range ℓ, (if p ≠ q then c p q else 0)
      = ∑ p ∈ range ℓ, ∑ q ∈ range ℓ,
          ((if p < q then c p q else 0) + (if q < p then c p q else 0)) :=
        sum_congr rfl fun p _ => sum_congr rfl fun q _ => h p q
    _ = ∑ p ∈ range ℓ, ∑ q ∈ range ℓ, (if p < q then c p q else 0)
          + ∑ p ∈ range ℓ, ∑ q ∈ range ℓ, (if q < p then c p q else 0) := by
        simp only [sum_add_distrib]
    _ = ∑ p ∈ range ℓ, ∑ q ∈ range ℓ, (if p < q then c p q else 0)
          + ∑ p ∈ range ℓ, ∑ q ∈ range ℓ, (if p < q then c q p else 0) := by
        congr 1
        exact sum_comm
    _ = ∑ p ∈ range ℓ, ∑ q ∈ range ℓ, (if p < q then c p q + c q p else 0) := by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun p _ => ?_
        rw [← sum_add_distrib]
        refine sum_congr rfl fun q _ => ?_
        split_ifs <;> simp

/-- The pairs of sites at index distance at most seven are among the pairs `p < q`. -/
theorem sum_near_pairs_le (ℓ : ℕ) (d : ℕ → ℕ → ℝ) (hd : ∀ p q, p < q → q < ℓ → 0 ≤ d p q) :
    ∑ s : Fin 7, ∑ p ∈ range ℓ, (if p + s + 1 < ℓ then d p (p + s + 1) else 0)
      ≤ ∑ p ∈ range ℓ, ∑ q ∈ range ℓ, (if p < q then d p q else 0) := by
  rw [sum_comm]
  refine sum_le_sum fun p _ => ?_
  rw [← sum_filter, ← sum_filter]
  have hinj : Set.InjOn (fun s : Fin 7 => p + s.val + 1)
      ↑(univ.filter fun s : Fin 7 => p + s.val + 1 < ℓ) := by
    intro a _ b _ hab
    apply Fin.ext
    have hab' : p + a.val + 1 = p + b.val + 1 := hab
    omega
  calc ∑ s ∈ univ.filter (fun s : Fin 7 => p + s.val + 1 < ℓ), d p (p + s.val + 1)
      = ∑ q ∈ (univ.filter fun s : Fin 7 => p + s.val + 1 < ℓ).image
          (fun s : Fin 7 => p + s.val + 1), d p q := (sum_image hinj).symm
    _ ≤ ∑ q ∈ (range ℓ).filter (fun q => p < q), d p q := by
        refine sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro q hq
          obtain ⟨s, hs, rfl⟩ := mem_image.mp hq
          rw [mem_filter] at hs ⊢
          exact ⟨mem_range.mpr hs.2, Nat.lt_succ_of_le (Nat.le_add_right p s)⟩
        · intro q hq _
          rw [mem_filter, mem_range] at hq
          exact hd p q hq.2 hq.1

end Simple673.Transfer
