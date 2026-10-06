/-
Simple673/Transfer/Main.lean — the telescoping transfer lemma, without labels.

The eight-point local inequality `LocalInequality`, summed over all windows of eight consecutive
points of a separated chain of simple points, gives a lower bound for the pair energy. Two forms
are proved.

* `Transfer.transfer_range7` (the exact form): only the pairs at index distance at most seven
  appear on the right, with the exact kernel values and no tolerance,

    `x₁ ℓ - 7α R - (7 x₁ + Ω) ≤ ∑_{i ≠ j, |i - j| ≤ 7} K(y_j - y_i)²`.

  So `(x₁, 7α)` is a pair-energy certificate of range `7`: a lower bound for the pair energy of
  the pairs at index distance at most seven that is linear in the number `ℓ` of points and in the
  length `R` of an interval that contains the chain. `Transfer.transfer_range7_abs` is the same
  statement with the index condition written as `|i - j| ≤ 7` for integers.
* `transfer` (the form `TransferStatement` of `Spec.lean`): all pairs appear on the right, with
  nonnegative pair energies `e i j ≥ K(y_j - y_i)² - ε`,

    `x₁ ℓ - 7α R - (7 x₁ + Ω) - 14 ε ℓ ≤ ∑_{i ≠ j} e i j`.

  It follows from the exact form: a point has at most fourteen neighbours at index distance at
  most seven (`card_near_le`), and the other pairs have nonnegative energy.

The constants are those of `Defs.lean`: `x₁ = rewX = 8722 · 10⁻⁶`, `7α = spanB = 4389 · 10⁻⁶`,
`Ω = omegaB = 3882 · 10⁻⁶`, so that `7 x₁ + Ω = 64936 · 10⁻⁶`.

The proof of the exact form works with sequences indexed by `ℕ` (`transfer_nat_range7`): a chain
of `n + 7` sites has `n` windows, and the four parts of the summed local inequality are treated
separately:

* rewards (`sum_window_reward`): each window rewards one of its points (the fourth), `n x₁` in
  all, which is `(n + 7) x₁` up to the loss `7 x₁` at the ends;
* pressure (`sum_window_pressure_le`): each gap is charged at most seven times;
* potentials (`sum_window_potential_le'`): they telescope, with oscillation at most `Ω`;
* pairs (`sum_window_pair_le`): the budgets bound the weight of a pair of sites by `2`, the
  weight of the two ordered pairs on the right.

`transfer_range7` then passes from `Fin ℓ` to `ℕ`, and treats `ℓ < 7` directly.

The sums over the windows of a chain are those of `Simple673/Transfer/Sums.lean`.

All auxiliary statements of the layer live in the namespace `Simple673.Transfer`, so that they
cannot clash with the auxiliary statements of other layers; only `Simple673.transfer` is
exported to the namespace `Simple673`.
-/
import Simple673.Spec
import Simple673.Transfer.Potential

open scoped BigOperators
open Finset

namespace Simple673

namespace Transfer

/-! ## The kernel is even -/

theorem sincN_neg (t : ℝ) : sincN (-t) = sincN t := by
  unfold sincN
  rw [mul_neg, Real.sinc_neg]

/-- `K(-t) = K(t)`. -/
theorem K_neg (t : ℝ) : K (-t) = K t := by
  unfold K
  rw [sincN_neg]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  have h1 : -t - ((j : ℕ) + 1) = -(t + ((j : ℕ) + 1)) := by ring
  have h2 : -t + ((j : ℕ) + 1) = -(t - ((j : ℕ) + 1)) := by ring
  rw [h1, h2, sincN_neg, sincN_neg]
  ring

/-- `K(s - t)² = K(t - s)²`. -/
theorem K_sub_sq_comm (s t : ℝ) : K (s - t) ^ 2 = K (t - s) ^ 2 := by
  rw [← K_neg (t - s), neg_sub]

/-! ## The local inequality for a window of a chain -/

/-- The position `pos g i` is the sum of the first `i` gaps. -/
theorem pos_eq_sum_range (g : Fin 7 → ℝ) (G : ℕ → ℝ) (hG : ∀ r : Fin 7, g r = G r)
    (i : Fin 8) : pos g i = ∑ r ∈ range i, G r := by
  unfold pos
  calc ∑ r : Fin 7, (if r.val < i.val then g r else 0)
      = ∑ r : Fin 7, (fun m : ℕ => if m < i.val then G m else 0) r.val :=
        sum_congr rfl fun r _ => by rw [hG]
    _ = ∑ m ∈ range 7, (if m < i.val then G m else 0) :=
        Fin.sum_univ_eq_sum_range (fun m : ℕ => if m < i.val then G m else 0) 7
    _ = ∑ m ∈ (range 7).filter (fun m => m < i.val), G m := (sum_filter _ _).symm
    _ = ∑ m ∈ range i.val, G m := by
        congr 1
        ext m
        simp only [mem_filter, mem_range]
        have := i.isLt
        omega

/-- In the window `w` of a chain `Y`, the local position `i` is `Y (w + i) - Y w`. -/
theorem pos_window (Y : ℕ → ℝ) (w : ℕ) (i : Fin 8) :
    pos (fun r : Fin 7 => Y (w + r + 1) - Y (w + r)) i = Y (w + i) - Y w := by
  rw [pos_eq_sum_range (fun r : Fin 7 => Y (w + r + 1) - Y (w + r))
    (fun r : ℕ => Y (w + (r + 1)) - Y (w + r)) (fun r => by
      show Y (w + (r : ℕ) + 1) - Y (w + r) = Y (w + ((r : ℕ) + 1)) - Y (w + r)
      rw [Nat.add_assoc]) i]
  exact sum_range_sub (fun r : ℕ => Y (w + r)) i.val

/-- `LocalInequality` for the window `w` of a chain `Y`. -/
theorem window_inequality (hloc : LocalInequality) (Y : ℕ → ℝ) (w : ℕ)
    (hsep : ∀ r : Fin 7, sep ≤ Y (w + r + 1) - Y (w + r)) :
    ∑ i : Fin 8, (hTab i : ℝ) / 1000000 ≤
      alphaP * ∑ r : Fin 7, (Y (w + r + 1) - Y (w + r))
      + ∑ i : Fin 8, ∑ j : Fin 8,
          (if i < j then (Wtab i j : ℝ) / 1000000 * K (Y (w + j) - Y (w + i)) ^ 2 else 0)
      + ∑ r : Fin 7, Bpot r (Y (w + r + 1) - Y (w + r)) := by
  have h := hloc (fun r => Y (w + r + 1) - Y (w + r)) hsep
  have hp : ∀ i : Fin 8,
      pos (fun r : Fin 7 => Y (w + r + 1) - Y (w + r)) i = Y (w + i) - Y w := pos_window Y w
  have e : ∀ i j : Fin 8, Y (w + j) - Y w - (Y (w + i) - Y w) = Y (w + j) - Y (w + i) :=
    fun i j => by ring
  simp only [hp, e] at h
  exact h

/-! ## The four parts of the sum over the windows -/

/-- Rewards: each of the `n` windows rewards its fourth point with `x₁`; compared with a reward
for every one of the `n + 7` sites, the loss is `7 x₁` (the first three sites and the last four). -/
theorem sum_window_reward (n : ℕ) :
    rewX * ((n + 7 : ℕ) : ℝ)
      = ∑ _w ∈ range n, ∑ i : Fin 8, (hTab i : ℝ) / 1000000 + 7 * rewX := by
  rw [sum_const, card_range, nsmul_eq_mul, sum_hTab_real]
  push_cast
  ring

/-- Pressure: each gap lies in at most seven windows, and the gaps add up to at most `R`. -/
theorem sum_window_pressure_le (Y : ℕ → ℝ) (n : ℕ) (R : ℝ)
    (hR : ∀ p q, p < n + 7 → q < n + 7 → Y q - Y p ≤ R) :
    alphaP * ∑ w ∈ range n, ∑ r : Fin 7, (Y (w + r + 1) - Y (w + r)) ≤ spanB * R := by
  have h1 : ∑ r : Fin 7, (Y (n + r) - Y r) ≤ 7 * R :=
    calc ∑ r : Fin 7, (Y (n + r) - Y r) ≤ ∑ _r : Fin 7, R :=
          sum_le_sum fun r _ =>
            hR _ _ (by have := r.isLt; omega) (by have := r.isLt; omega)
      _ = 7 * R := by simp
  have hα : (0 : ℝ) ≤ alphaP := by norm_num [alphaP]
  rw [sum_window_gaps]
  calc alphaP * ∑ r : Fin 7, (Y (n + r) - Y r) ≤ alphaP * (7 * R) :=
        mul_le_mul_of_nonneg_left h1 hα
    _ = spanB * R := by unfold spanB; ring

/-- Potentials: the potential terms of all windows add up to at most `Ω`. -/
theorem sum_window_potential_le' (Y : ℕ → ℝ) (n : ℕ) :
    ∑ w ∈ range n, ∑ r : Fin 7, Bpot r (Y (w + r + 1) - Y (w + r)) ≤ omegaB :=
  sum_window_potential_le (fun p => Y (p + 1) - Y p) n

/-- Pairs: the pair terms of all windows are at most the sum of `K²` over the ordered pairs of
distinct sites at index distance at most seven. No pair at a larger index distance is used, and
there is no error term. -/
theorem sum_window_pair_le (n : ℕ) (Y : ℕ → ℝ) :
    ∑ w ∈ range n, ∑ i : Fin 8, ∑ j : Fin 8,
        (if i < j then (Wtab i j : ℝ) / 1000000 * K (Y (w + j) - Y (w + i)) ^ 2 else 0)
      ≤ ∑ p ∈ range (n + 7), ∑ q ∈ range (n + 7),
          (if p ≠ q ∧ p ≤ q + 7 ∧ q ≤ p + 7 then K (Y q - Y p) ^ 2 else 0) := by
  calc ∑ w ∈ range n, ∑ i : Fin 8, ∑ j : Fin 8,
        (if i < j then (Wtab i j : ℝ) / 1000000 * K (Y (w + j) - Y (w + i)) ^ 2 else 0)
      ≤ ∑ s : Fin 7, ∑ p ∈ range (n + 7),
          (if p + s + 1 < n + 7 then 2 * K (Y (p + s + 1) - Y p) ^ 2 else 0) :=
        -- the budgets: a pair of sites at index distance `s + 1` has weight at most `2`
        sum_window_pairs_le n
          (fun _ _ i j => (Wtab i j : ℝ) / 1000000) (fun _ _ => 2)
          (fun p q => K (Y q - Y p) ^ 2)
          (fun _ _ i j => Wtab_real_nonneg i j) (fun _ _ s => Wtab_budget_real s)
          (fun _ _ _ _ => sq_nonneg _)
    _ = ∑ s : Fin 7, ∑ p ∈ range (n + 7),
          (if p + s + 1 < n + 7 then
            (fun p q : ℕ => if q ≤ p + 7 then 2 * K (Y q - Y p) ^ 2 else 0) p (p + s + 1)
            else 0) := by
        refine sum_congr rfl fun s _ => sum_congr rfl fun p _ => ?_
        have hs : p + (s : ℕ) + 1 ≤ p + 7 := by have := s.isLt; omega
        simp only [if_pos hs]
    _ ≤ ∑ p ∈ range (n + 7), ∑ q ∈ range (n + 7),
          (if p < q then
            (fun p q : ℕ => if q ≤ p + 7 then 2 * K (Y q - Y p) ^ 2 else 0) p q else 0) :=
        -- the pairs `(p, p + s + 1)` are among the pairs `p < q`
        sum_near_pairs_le (n + 7)
          (fun p q : ℕ => if q ≤ p + 7 then 2 * K (Y q - Y p) ^ 2 else 0)
          (fun p q _ _ => by
            show 0 ≤ if q ≤ p + 7 then 2 * K (Y q - Y p) ^ 2 else 0
            split_ifs
            · exact mul_nonneg (by norm_num) (sq_nonneg _)
            · exact le_rfl)
    _ = ∑ p ∈ range (n + 7), ∑ q ∈ range (n + 7),
          (if p < q then
            (fun p q : ℕ => if p ≤ q + 7 ∧ q ≤ p + 7 then K (Y q - Y p) ^ 2 else 0) p q
              + (fun p q : ℕ => if p ≤ q + 7 ∧ q ≤ p + 7 then K (Y q - Y p) ^ 2 else 0) q p
            else 0) := by
        -- the unordered pair `{p, q}` is the two ordered pairs; `K` is even
        refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
        by_cases hpq : p < q
        · rw [if_pos hpq, if_pos hpq]
          by_cases hq : q ≤ p + 7
          · have h1 : p ≤ q + 7 ∧ q ≤ p + 7 := ⟨by omega, hq⟩
            have h2 : q ≤ p + 7 ∧ p ≤ q + 7 := ⟨hq, by omega⟩
            simp only [if_pos hq, if_pos h1, if_pos h2]
            rw [K_sub_sq_comm (Y p) (Y q)]
            ring
          · have h1 : ¬ (p ≤ q + 7 ∧ q ≤ p + 7) := fun h => hq h.2
            have h2 : ¬ (q ≤ p + 7 ∧ p ≤ q + 7) := fun h => hq h.1
            simp only [if_neg hq, if_neg h1, if_neg h2, add_zero]
        · rw [if_neg hpq, if_neg hpq]
    _ = ∑ p ∈ range (n + 7), ∑ q ∈ range (n + 7),
          (if p ≠ q then
            (fun p q : ℕ => if p ≤ q + 7 ∧ q ≤ p + 7 then K (Y q - Y p) ^ 2 else 0) p q
            else 0) :=
        (sum_offdiag_eq (n + 7)
          (fun p q : ℕ => if p ≤ q + 7 ∧ q ≤ p + 7 then K (Y q - Y p) ^ 2 else 0)).symm
    _ = ∑ p ∈ range (n + 7), ∑ q ∈ range (n + 7),
          (if p ≠ q ∧ p ≤ q + 7 ∧ q ≤ p + 7 then K (Y q - Y p) ^ 2 else 0) := by
        refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
        by_cases hpq : p ≠ q
        · by_cases h2 : p ≤ q + 7 ∧ q ≤ p + 7
          · rw [if_pos hpq, if_pos (⟨hpq, h2⟩ : p ≠ q ∧ p ≤ q + 7 ∧ q ≤ p + 7)]
            exact if_pos h2
          · rw [if_pos hpq, if_neg (fun h : p ≠ q ∧ p ≤ q + 7 ∧ q ≤ p + 7 => h2 h.2)]
            exact if_neg h2
        · rw [if_neg hpq, if_neg (fun h : p ≠ q ∧ p ≤ q + 7 ∧ q ≤ p + 7 => hpq h.1)]

/-! ## The exact form: pairs at index distance at most seven -/

/-- The transfer lemma for a chain of `n + 7` sites indexed by `ℕ`, in the exact form: on the
right are the kernel values of the ordered pairs of distinct sites at index distance at most
seven. Only the values of `Y` at indices below `n + 7` matter. -/
theorem transfer_nat_range7 (hloc : LocalInequality) (n : ℕ) (Y : ℕ → ℝ) (R : ℝ)
    (hsep : ∀ p, p + 1 < n + 7 → sep ≤ Y (p + 1) - Y p)
    (hR : ∀ p q, p < n + 7 → q < n + 7 → Y q - Y p ≤ R) :
    rewX * ((n + 7 : ℕ) : ℝ) - spanB * R - (7 * rewX + omegaB)
      ≤ ∑ p ∈ range (n + 7), ∑ q ∈ range (n + 7),
          (if p ≠ q ∧ p ≤ q + 7 ∧ q ≤ p + 7 then K (Y q - Y p) ^ 2 else 0) := by
  have hsum := sum_le_sum fun w (hw : w ∈ range n) =>
    window_inequality hloc Y w (fun r => hsep (w + r)
      (by have := mem_range.mp hw; have := r.isLt; omega))
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum] at hsum
  have h1 := sum_window_reward n
  have h2 := sum_window_pressure_le Y n R hR
  have h3 := sum_window_potential_le' Y n
  have h4 := sum_window_pair_le n Y
  linarith

/-- **The transfer lemma with pairs of range seven.** For a separated chain of `ℓ` simple points
in an interval of length `R`,

  `x₁ ℓ - 7α R - (7 x₁ + Ω) ≤ ∑_{i ≠ j, |i - j| ≤ 7} K(y_j - y_i)²`,

with the exact kernel values and no tolerance. On the right are the ordered pairs of distinct
points whose indices differ by at most seven. -/
theorem transfer_range7 (hloc : LocalInequality) (ℓ : ℕ) (y : Fin ℓ → ℝ) (R : ℝ)
    (hsep : ∀ i j, i < j → sep ≤ y j - y i) (hR0 : 0 ≤ R) (hR : ∀ i j, y j - y i ≤ R) :
    rewX * ℓ - spanB * R - (7 * rewX + omegaB)
      ≤ ∑ i : Fin ℓ, ∑ j : Fin ℓ,
          if i ≠ j ∧ (i : ℕ) ≤ (j : ℕ) + 7 ∧ (j : ℕ) ≤ (i : ℕ) + 7 then K (y j - y i) ^ 2
          else 0 := by
  rcases Nat.lt_or_ge ℓ 7 with hℓ | hℓ
  · -- fewer than seven points: the left side is nonpositive, the right side nonnegative
    have hrhs : 0 ≤ ∑ i : Fin ℓ, ∑ j : Fin ℓ,
        if i ≠ j ∧ (i : ℕ) ≤ (j : ℕ) + 7 ∧ (j : ℕ) ≤ (i : ℕ) + 7 then K (y j - y i) ^ 2
        else 0 := by
      refine sum_nonneg fun i _ => sum_nonneg fun j _ => ?_
      split_ifs
      · exact sq_nonneg _
      · exact le_rfl
    have hℓ' : (ℓ : ℝ) ≤ 7 := by exact_mod_cast hℓ.le
    have hx : (0 : ℝ) ≤ rewX := by norm_num [rewX]
    have hω : (0 : ℝ) ≤ omegaB := by norm_num [omegaB]
    have hsp : 0 ≤ spanB * R := mul_nonneg (by norm_num [spanB, alphaP]) hR0
    have hmul : rewX * (ℓ : ℝ) ≤ rewX * 7 := mul_le_mul_of_nonneg_left hℓ' hx
    linarith
  · -- at least seven points: extend the data to a sequence indexed by `ℕ`
    obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 7 := ⟨ℓ - 7, by omega⟩
    obtain ⟨Y, hY⟩ : ∃ Y : ℕ → ℝ, ∀ (p : ℕ) (h : p < n + 7), Y p = y ⟨p, h⟩ :=
      ⟨fun p => if h : p < n + 7 then y ⟨p, h⟩ else 0, fun p h => dif_pos h⟩
    have key := transfer_nat_range7 hloc n Y R
      (fun p hp => by
        rw [hY (p + 1) hp, hY p (by omega)]
        exact hsep ⟨p, by omega⟩ ⟨p + 1, hp⟩ (Fin.mk_lt_mk.mpr (Nat.lt_succ_self p)))
      (fun p q hp hq => by
        rw [hY q hq, hY p hp]
        exact hR ⟨p, hp⟩ ⟨q, hq⟩)
    have e2 : ∑ p ∈ range (n + 7), ∑ q ∈ range (n + 7),
          (if p ≠ q ∧ p ≤ q + 7 ∧ q ≤ p + 7 then K (Y q - Y p) ^ 2 else 0)
        = ∑ i : Fin (n + 7), ∑ j : Fin (n + 7),
          (if i ≠ j ∧ (i : ℕ) ≤ (j : ℕ) + 7 ∧ (j : ℕ) ≤ (i : ℕ) + 7 then K (y j - y i) ^ 2
            else 0) := by
      rw [Finset.sum_range]
      refine sum_congr rfl fun i _ => ?_
      rw [Finset.sum_range]
      refine sum_congr rfl fun j _ => ?_
      rw [hY i i.isLt, hY j j.isLt]
      exact if_congr (and_congr Fin.val_ne_iff Iff.rfl) rfl rfl
    rw [e2] at key
    exact key

/-- The same statement with the index distance written as an absolute value of integers. -/
theorem transfer_range7_abs (hloc : LocalInequality) (ℓ : ℕ) (y : Fin ℓ → ℝ) (R : ℝ)
    (hsep : ∀ i j, i < j → sep ≤ y j - y i) (hR0 : 0 ≤ R) (hR : ∀ i j, y j - y i ≤ R) :
    rewX * ℓ - spanB * R - (7 * rewX + omegaB)
      ≤ ∑ i : Fin ℓ, ∑ j : Fin ℓ,
          if i ≠ j ∧ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ 7 then K (y j - y i) ^ 2 else 0 := by
  refine (transfer_range7 hloc ℓ y R hsep hR0 hR).trans (le_of_eq ?_)
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  refine if_congr (and_congr Iff.rfl ?_) rfl rfl
  rw [abs_le]
  omega

/-! ## From the exact form to the form with a tolerance -/

/-- A point has at most fourteen neighbours at index distance at most seven. -/
theorem card_near_le (ℓ : ℕ) (i : Fin ℓ) :
    (univ.filter fun j : Fin ℓ =>
      i ≠ j ∧ (i : ℕ) ≤ (j : ℕ) + 7 ∧ (j : ℕ) ≤ (i : ℕ) + 7).card ≤ 14 := by
  have h1 : (univ.filter fun j : Fin ℓ =>
        i ≠ j ∧ (i : ℕ) ≤ (j : ℕ) + 7 ∧ (j : ℕ) ≤ (i : ℕ) + 7).card
      ≤ ((Icc ((i : ℕ) - 7) ((i : ℕ) + 7)).erase (i : ℕ)).card := by
    refine card_le_card_of_injOn (fun j : Fin ℓ => (j : ℕ)) ?_ ?_
    · intro j hj
      have hj' := (mem_filter.mp (mem_coe.mp hj)).2
      refine mem_coe.mpr (mem_erase.mpr ⟨fun h => hj'.1 (Fin.ext h.symm), mem_Icc.mpr ?_⟩)
      have := hj'.2
      show (i : ℕ) - 7 ≤ (j : ℕ) ∧ (j : ℕ) ≤ (i : ℕ) + 7
      omega
    · intro a _ b _ hab
      exact Fin.ext hab
  have h2 : ((Icc ((i : ℕ) - 7) ((i : ℕ) + 7)).erase (i : ℕ)).card ≤ 14 := by
    rw [card_erase_of_mem (mem_Icc.mpr ⟨by omega, by omega⟩), Nat.card_Icc]
    omega
  exact h1.trans h2

/-- The transfer lemma in the form with a tolerance, from the exact form: the pairs at index
distance at most seven cost `ε` each, at most `14 ε` per point, and the other pairs have
nonnegative energy. -/
theorem transfer_of_range7 (ℓ : ℕ) (y : Fin ℓ → ℝ) (e : Fin ℓ → Fin ℓ → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (he0 : ∀ i j, i ≠ j → 0 ≤ e i j)
    (heK : ∀ i j, i ≠ j → K (y j - y i) ^ 2 - ε ≤ e i j) :
    (∑ i : Fin ℓ, ∑ j : Fin ℓ,
        if i ≠ j ∧ (i : ℕ) ≤ (j : ℕ) + 7 ∧ (j : ℕ) ≤ (i : ℕ) + 7 then K (y j - y i) ^ 2 else 0)
      ≤ (∑ i : Fin ℓ, ∑ j : Fin ℓ, if i ≠ j then e i j else 0) + 14 * ε * ℓ := by
  have hterm : ∀ i j : Fin ℓ,
      (if i ≠ j ∧ (i : ℕ) ≤ (j : ℕ) + 7 ∧ (j : ℕ) ≤ (i : ℕ) + 7 then K (y j - y i) ^ 2 else 0)
        ≤ (if i ≠ j then e i j else 0)
          + (if i ≠ j ∧ (i : ℕ) ≤ (j : ℕ) + 7 ∧ (j : ℕ) ≤ (i : ℕ) + 7 then ε else 0) := by
    intro i j
    by_cases hij : i ≠ j
    · by_cases hn : i ≠ j ∧ (i : ℕ) ≤ (j : ℕ) + 7 ∧ (j : ℕ) ≤ (i : ℕ) + 7
      · rw [if_pos hn, if_pos hij, if_pos hn]
        linarith [heK i j hij]
      · rw [if_neg hn, if_pos hij, if_neg hn]
        linarith [he0 i j hij]
    · have hn : ¬ (i ≠ j ∧ (i : ℕ) ≤ (j : ℕ) + 7 ∧ (j : ℕ) ≤ (i : ℕ) + 7) := fun h => hij h.1
      simp only [if_neg hn, if_neg hij, add_zero, le_refl]
  have hcount : ∀ i : Fin ℓ,
      ∑ j : Fin ℓ, (if i ≠ j ∧ (i : ℕ) ≤ (j : ℕ) + 7 ∧ (j : ℕ) ≤ (i : ℕ) + 7 then ε else 0)
        ≤ 14 * ε := by
    intro i
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hc : ((univ.filter fun j : Fin ℓ =>
        i ≠ j ∧ (i : ℕ) ≤ (j : ℕ) + 7 ∧ (j : ℕ) ≤ (i : ℕ) + 7).card : ℝ) ≤ 14 := by
      exact_mod_cast card_near_le ℓ i
    exact mul_le_mul_of_nonneg_right hc hε
  calc (∑ i : Fin ℓ, ∑ j : Fin ℓ,
          if i ≠ j ∧ (i : ℕ) ≤ (j : ℕ) + 7 ∧ (j : ℕ) ≤ (i : ℕ) + 7 then K (y j - y i) ^ 2 else 0)
      ≤ ∑ i : Fin ℓ, ∑ j : Fin ℓ, ((if i ≠ j then e i j else 0)
          + (if i ≠ j ∧ (i : ℕ) ≤ (j : ℕ) + 7 ∧ (j : ℕ) ≤ (i : ℕ) + 7 then ε else 0)) :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => hterm i j
    _ = (∑ i : Fin ℓ, ∑ j : Fin ℓ, if i ≠ j then e i j else 0)
          + ∑ i : Fin ℓ, ∑ j : Fin ℓ,
              (if i ≠ j ∧ (i : ℕ) ≤ (j : ℕ) + 7 ∧ (j : ℕ) ≤ (i : ℕ) + 7 then ε else 0) := by
        simp only [sum_add_distrib]
    _ ≤ (∑ i : Fin ℓ, ∑ j : Fin ℓ, if i ≠ j then e i j else 0) + ∑ _i : Fin ℓ, 14 * ε :=
        add_le_add le_rfl (sum_le_sum fun i _ => hcount i)
    _ = (∑ i : Fin ℓ, ∑ j : Fin ℓ, if i ≠ j then e i j else 0) + 14 * ε * ℓ := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Transfer

open Transfer in
/-- **The telescoping transfer lemma**: the local eight-point inequality implies the lower bound
of `TransferStatement` for every separated chain of simple points. -/
theorem transfer (hloc : LocalInequality) : TransferStatement := by
  intro ℓ y e ε R hsep hR0 hR hε he0 heK
  have h1 := transfer_range7 hloc ℓ y R hsep hR0 hR
  have h2 := transfer_of_range7 ℓ y e ε hε he0 heK
  linarith

end Simple673
