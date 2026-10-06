/-
Distinct839/Transfer/Main.lean — the labelled telescoping transfer lemma.

The transfer lemma of the paper, as `TransferStatement` of `Spec.lean`: the seven-point local
inequality `LocalInequality`, summed over all windows of seven consecutive points of a separated
labelled chain, gives

  `∑_i rew(lab i) - 6α R - (6y + Ω) - 48 ε ℓ ≤ ∑_{i ≠ j} m_i m_j e_ij`.

The proof works with sequences indexed by `ℕ` (`transfer_nat`): a chain of `n + 6` sites has
`n` windows, and the four parts of the summed local inequality are bounded separately:

* rewards (`sum_window_reward_ge`): all sites are rewarded, up to a loss `6y` at the ends;
* pressure (`sum_window_pressure_le`): each gap is charged at most six times;
* potentials (`sum_window_potential_le'`): they telescope, with oscillation at most `Ω`;
* pairs (`sum_window_pair_le`): the budgets bound the weight of a pair by `2 m_i m_j`.

`transfer` then passes from `Fin ℓ` to `ℕ`, and treats `ℓ < 6` directly.

All auxiliary statements of the layer live in the namespace `Distinct839.Transfer`, so that they
cannot clash with the auxiliary statements of other layers; only `Distinct839.transfer` is
exported to the namespace `Distinct839`.
-/
import Distinct839.Spec
import Distinct839.Transfer.Potential

open scoped BigOperators
open Finset

namespace Distinct839

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

/-! ## The local inequality for a window of a chain -/

/-- The position `pos g i` is the sum of the first `i` gaps. -/
theorem pos_eq_sum_range (g : Fin 6 → ℝ) (G : ℕ → ℝ) (hG : ∀ r : Fin 6, g r = G r)
    (i : Fin 7) : pos g i = ∑ r ∈ range i, G r := by
  unfold pos
  calc ∑ r : Fin 6, (if r.val < i.val then g r else 0)
      = ∑ r : Fin 6, (fun m : ℕ => if m < i.val then G m else 0) r.val :=
        sum_congr rfl fun r _ => by rw [hG]
    _ = ∑ m ∈ range 6, (if m < i.val then G m else 0) :=
        Fin.sum_univ_eq_sum_range (fun m : ℕ => if m < i.val then G m else 0) 6
    _ = ∑ m ∈ (range 6).filter (fun m => m < i.val), G m := (sum_filter _ _).symm
    _ = ∑ m ∈ range i.val, G m := by
        congr 1
        ext m
        simp only [mem_filter, mem_range]
        have := i.isLt
        omega

/-- In the window `w` of a chain `Y`, the local position `i` is `Y (w + i) - Y w`. -/
theorem pos_window (Y : ℕ → ℝ) (w : ℕ) (i : Fin 7) :
    pos (fun r : Fin 6 => Y (w + r + 1) - Y (w + r)) i = Y (w + i) - Y w := by
  rw [pos_eq_sum_range (fun r : Fin 6 => Y (w + r + 1) - Y (w + r))
    (fun r : ℕ => Y (w + (r + 1)) - Y (w + r)) (fun r => by
      show Y (w + (r : ℕ) + 1) - Y (w + r) = Y (w + ((r : ℕ) + 1)) - Y (w + r)
      rw [Nat.add_assoc]) i]
  exact sum_range_sub (fun r : ℕ => Y (w + r)) i.val

/-- `LocalInequality` for the window `w` of a chain `Y` with labels `L`. -/
theorem window_inequality (hloc : LocalInequality) (Y : ℕ → ℝ) (L : ℕ → Fin 2) (w : ℕ)
    (hsep : ∀ r : Fin 6, sep ≤ Y (w + r + 1) - Y (w + r)) :
    ∑ i : Fin 7, (hTab (L (w + i)) i : ℝ) / 1000000 ≤
      alphaP * ∑ r : Fin 6, (Y (w + r + 1) - Y (w + r))
      + ∑ i : Fin 7, ∑ j : Fin 7,
          (if i < j then (Wtab (pairTy (L (w + i)) (L (w + j))) i j : ℝ) / 1000000
              * K (Y (w + j) - Y (w + i)) ^ 2 else 0)
      + ∑ r : Fin 6, Bpot r (pairTy (L (w + r)) (L (w + r + 1))) (Y (w + r + 1) - Y (w + r)) := by
  have h := hloc (fun r => Y (w + r + 1) - Y (w + r)) (fun i => L (w + i)) hsep
  have hp : ∀ i : Fin 7,
      pos (fun r : Fin 6 => Y (w + r + 1) - Y (w + r)) i = Y (w + i) - Y w := pos_window Y w
  have e : ∀ i j : Fin 7, Y (w + j) - Y w - (Y (w + i) - Y w) = Y (w + j) - Y (w + i) :=
    fun i j => by ring
  simp only [hp, e, Fin.val_castSucc, Fin.val_succ, ← Nat.add_assoc] at h
  exact h

/-! ## The four parts of the sum over the windows -/

/-- Rewards: the windows reward every site, except for a loss of at most `6y` at the ends. -/
theorem sum_window_reward_ge (L : ℕ → Fin 2) (n : ℕ) :
    ∑ p ∈ range (n + 6), rew (L p)
      ≤ ∑ w ∈ range n, ∑ i : Fin 7, (hTab (L (w + i)) i : ℝ) / 1000000 + 6 * rewY :=
  calc ∑ p ∈ range (n + 6), rew (L p)
      = ∑ p ∈ range (n + 6), ∑ i : Fin 7, (hTab (L p) i : ℝ) / 1000000 :=
        sum_congr rfl fun p _ => (sum_hTab_real _).symm
    _ = ∑ i : Fin 7, ∑ p ∈ range (n + 6), (hTab (L p) i : ℝ) / 1000000 := sum_comm
    _ ≤ ∑ i : Fin 7, (∑ w ∈ range n, (hTab (L (w + i)) i : ℝ) / 1000000
          + 6 * ((hTab 1 i : ℝ) / 1000000)) :=
        sum_le_sum fun i _ =>
          sum_range_le_sum_shift_add (fun p => (hTab (L p) i : ℝ) / 1000000) _ n i
            (by have := i.isLt; omega) (fun p => hTab_real_le _ _)
    _ = ∑ w ∈ range n, ∑ i : Fin 7, (hTab (L (w + i)) i : ℝ) / 1000000 + 6 * rewY := by
        rw [sum_add_distrib, ← mul_sum, sum_hTab_one_real, sum_comm]

/-- Pressure: each gap lies in at most six windows, and the gaps add up to at most `R`. -/
theorem sum_window_pressure_le (Y : ℕ → ℝ) (n : ℕ) (R : ℝ)
    (hR : ∀ p q, p < n + 6 → q < n + 6 → Y q - Y p ≤ R) :
    alphaP * ∑ w ∈ range n, ∑ r : Fin 6, (Y (w + r + 1) - Y (w + r)) ≤ spanB * R := by
  have h1 : ∑ r : Fin 6, (Y (n + r) - Y r) ≤ 6 * R :=
    calc ∑ r : Fin 6, (Y (n + r) - Y r) ≤ ∑ _r : Fin 6, R :=
          sum_le_sum fun r _ =>
            hR _ _ (by have := r.isLt; omega) (by have := r.isLt; omega)
      _ = 6 * R := by simp
  have hα : (0 : ℝ) ≤ alphaP := by norm_num [alphaP]
  rw [sum_window_gaps]
  calc alphaP * ∑ r : Fin 6, (Y (n + r) - Y r) ≤ alphaP * (6 * R) :=
        mul_le_mul_of_nonneg_left h1 hα
    _ = spanB * R := by unfold spanB; ring

/-- Potentials: the potential terms of all windows add up to at most `Ω`. -/
theorem sum_window_potential_le' (Y : ℕ → ℝ) (L : ℕ → Fin 2) (n : ℕ) :
    ∑ w ∈ range n, ∑ r : Fin 6,
        Bpot r (pairTy (L (w + r)) (L (w + r + 1))) (Y (w + r + 1) - Y (w + r)) ≤ omegaB :=
  sum_window_potential_le (fun p => pairTy (L p) (L (p + 1))) (fun p => Y (p + 1) - Y p) n

/-- Pairs: the pair terms of all windows are at most the weighted pair energy, up to the error
`48 ε ℓ`. -/
theorem sum_window_pair_le (n : ℕ) (Y : ℕ → ℝ) (L : ℕ → Fin 2) (E : ℕ → ℕ → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hE0 : ∀ p q, p < n + 6 → q < n + 6 → p ≠ q → 0 ≤ E p q)
    (hEK : ∀ p q, p < n + 6 → q < n + 6 → p ≠ q → K (Y q - Y p) ^ 2 - ε ≤ E p q) :
    ∑ w ∈ range n, ∑ i : Fin 7, ∑ j : Fin 7,
        (if i < j then (Wtab (pairTy (L (w + i)) (L (w + j))) i j : ℝ) / 1000000
            * K (Y (w + j) - Y (w + i)) ^ 2 else 0)
      ≤ ∑ p ∈ range (n + 6), ∑ q ∈ range (n + 6),
          (if p ≠ q then mulOf (L p) * mulOf (L q) * E p q else 0)
        + 48 * ε * ((n + 6 : ℕ) : ℝ) := by
  -- the kernel value of a pair is controlled by the mean of the two energies
  have hK : ∀ p q, p < q → q < n + 6 → K (Y q - Y p) ^ 2 ≤ (E p q + E q p) / 2 + ε := by
    intro p q hpq hq
    have h1 := hEK p q (by omega) hq (by omega)
    have h2 := hEK q p hq (by omega) (by omega)
    have e : K (Y p - Y q) = K (Y q - Y p) := by
      rw [← K_neg (Y q - Y p)]
      congr 1
      ring
    rw [e] at h2
    linarith
  have hu : ∀ p q, p < q → q < n + 6 → 0 ≤ (E p q + E q p) / 2 + ε := by
    intro p q hpq hq
    have h1 := hE0 p q (by omega) hq (by omega)
    have h2 := hE0 q p hq (by omega) (by omega)
    linarith
  have hd : ∀ p q, p < q → q < n + 6 →
      0 ≤ mulOf (L p) * mulOf (L q) * E p q + mulOf (L q) * mulOf (L p) * E q p := by
    intro p q hpq hq
    have h1 := hE0 p q (by omega) hq (by omega)
    have h2 := hE0 q p hq (by omega) (by omega)
    exact add_nonneg (mul_nonneg (mul_nonneg (mulOf_nonneg _) (mulOf_nonneg _)) h1)
      (mul_nonneg (mul_nonneg (mulOf_nonneg _) (mulOf_nonneg _)) h2)
  calc ∑ w ∈ range n, ∑ i : Fin 7, ∑ j : Fin 7,
        (if i < j then (Wtab (pairTy (L (w + i)) (L (w + j))) i j : ℝ) / 1000000
            * K (Y (w + j) - Y (w + i)) ^ 2 else 0)
      ≤ ∑ w ∈ range n, ∑ i : Fin 7, ∑ j : Fin 7,
          (if i < j then (Wtab (pairTy (L (w + i)) (L (w + j))) i j : ℝ) / 1000000
            * ((E (w + i) (w + j) + E (w + j) (w + i)) / 2 + ε) else 0) := by
        refine sum_le_sum fun w hw => sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
        have hw' := mem_range.mp hw
        have hj := j.isLt
        by_cases hij : i < j
        · have hij' : i.val < j.val := hij
          rw [if_pos hij, if_pos hij]
          exact mul_le_mul_of_nonneg_left (hK _ _ (by omega) (by omega))
            (Wtab_real_nonneg _ _ _)
        · rw [if_neg hij, if_neg hij]
    _ ≤ ∑ s : Fin 6, ∑ p ∈ range (n + 6),
          (if p + s + 1 < n + 6 then 2 * mulOf (L p) * mulOf (L (p + s + 1))
            * ((E p (p + s + 1) + E (p + s + 1) p) / 2 + ε) else 0) :=
        sum_window_pairs_le n (fun p q i j => (Wtab (pairTy (L p) (L q)) i j : ℝ) / 1000000)
          (fun p q => 2 * mulOf (L p) * mulOf (L q)) (fun p q => (E p q + E q p) / 2 + ε)
          (fun p q i j => Wtab_real_nonneg _ _ _) (fun p q s => Wtab_budget_real _ _ s) hu
    _ ≤ ∑ s : Fin 6, ∑ p ∈ range (n + 6),
          ((if p + s + 1 < n + 6 then
              mulOf (L p) * mulOf (L (p + s + 1)) * E p (p + s + 1)
                + mulOf (L (p + s + 1)) * mulOf (L p) * E (p + s + 1) p else 0) + 8 * ε) := by
        refine sum_le_sum fun s _ => sum_le_sum fun p _ => ?_
        by_cases hp : p + s + 1 < n + 6
        · rw [if_pos hp, if_pos hp]
          have h2 := mulOf_le_two (L p)
          have h4 := mulOf_le_two (L (p + s + 1))
          have h5 : mulOf (L p) * mulOf (L (p + s + 1)) ≤ 4 :=
            calc mulOf (L p) * mulOf (L (p + s + 1)) ≤ 2 * 2 :=
                  mul_le_mul h2 h4 (mulOf_nonneg _) (by norm_num)
              _ = 4 := by norm_num
          linarith [mul_nonneg hε (sub_nonneg.mpr h5)]
        · rw [if_neg hp, if_neg hp]
          linarith
    _ = ∑ s : Fin 6, ∑ p ∈ range (n + 6),
          (if p + s + 1 < n + 6 then
              mulOf (L p) * mulOf (L (p + s + 1)) * E p (p + s + 1)
                + mulOf (L (p + s + 1)) * mulOf (L p) * E (p + s + 1) p else 0)
        + 48 * ε * ((n + 6 : ℕ) : ℝ) := by
        simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, card_range,
          nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ∑ p ∈ range (n + 6), ∑ q ∈ range (n + 6),
          (if p < q then mulOf (L p) * mulOf (L q) * E p q + mulOf (L q) * mulOf (L p) * E q p
            else 0)
        + 48 * ε * ((n + 6 : ℕ) : ℝ) :=
        add_le_add
          (sum_near_pairs_le (n + 6)
            (fun p q => mulOf (L p) * mulOf (L q) * E p q + mulOf (L q) * mulOf (L p) * E q p)
            hd) le_rfl
    _ = ∑ p ∈ range (n + 6), ∑ q ∈ range (n + 6),
          (if p ≠ q then mulOf (L p) * mulOf (L q) * E p q else 0)
        + 48 * ε * ((n + 6 : ℕ) : ℝ) := by
        congr 1
        exact (sum_offdiag_eq (n + 6) (fun p q => mulOf (L p) * mulOf (L q) * E p q)).symm

/-! ## The transfer lemma -/

/-- The transfer lemma for a chain of `n + 6` sites indexed by `ℕ`. Only the values of `Y`, `L`
and `E` at indices below `n + 6` matter. -/
theorem transfer_nat (hloc : LocalInequality) (n : ℕ) (Y : ℕ → ℝ) (L : ℕ → Fin 2)
    (E : ℕ → ℕ → ℝ) (ε R : ℝ)
    (hsep : ∀ p, p + 1 < n + 6 → sep ≤ Y (p + 1) - Y p)
    (hR : ∀ p q, p < n + 6 → q < n + 6 → Y q - Y p ≤ R)
    (hε : 0 ≤ ε)
    (hE0 : ∀ p q, p < n + 6 → q < n + 6 → p ≠ q → 0 ≤ E p q)
    (hEK : ∀ p q, p < n + 6 → q < n + 6 → p ≠ q → K (Y q - Y p) ^ 2 - ε ≤ E p q) :
    ∑ p ∈ range (n + 6), rew (L p) - spanB * R - (6 * rewY + omegaB)
        - 48 * ε * ((n + 6 : ℕ) : ℝ)
      ≤ ∑ p ∈ range (n + 6), ∑ q ∈ range (n + 6),
          (if p ≠ q then mulOf (L p) * mulOf (L q) * E p q else 0) := by
  have hsum := sum_le_sum fun w (hw : w ∈ range n) =>
    window_inequality hloc Y L w (fun r => hsep (w + r)
      (by have := mem_range.mp hw; have := r.isLt; omega))
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum] at hsum
  have h1 := sum_window_reward_ge L n
  have h2 := sum_window_pressure_le Y n R hR
  have h3 := sum_window_potential_le' Y L n
  have h4 := sum_window_pair_le n Y L E ε hε hE0 hEK
  linarith

end Transfer

open Transfer in
/-- **The labelled telescoping transfer lemma** of the paper: the local seven-point
inequality implies the lower bound of `TransferStatement` for every separated labelled chain. -/
theorem transfer (hloc : LocalInequality) : TransferStatement := by
  intro ℓ y lab e ε R hsep hR0 hR hε he0 heK
  rcases Nat.lt_or_ge ℓ 6 with hℓ | hℓ
  · -- fewer than six points: the left side is nonpositive, the right side nonnegative
    have hrhs : 0 ≤ ∑ i, ∑ j, if i ≠ j then mulOf (lab i) * mulOf (lab j) * e i j else 0 := by
      refine sum_nonneg fun i _ => sum_nonneg fun j _ => ?_
      by_cases h : i = j
      · simp [h]
      · rw [if_pos h]
        exact mul_nonneg (mul_nonneg (mulOf_nonneg _) (mulOf_nonneg _)) (he0 i j h)
    have hlhs : ∑ i, rew (lab i) ≤ (ℓ : ℝ) * rewY :=
      calc ∑ i, rew (lab i) ≤ ∑ _i : Fin ℓ, rewY := sum_le_sum fun i _ => rew_le_rewY _
        _ = (ℓ : ℝ) * rewY := by simp
    have hℓ' : (ℓ : ℝ) ≤ 6 := by exact_mod_cast hℓ.le
    have hy : (0 : ℝ) ≤ rewY := by norm_num [rewY]
    have hω : (0 : ℝ) ≤ omegaB := by norm_num [omegaB]
    have hsp : 0 ≤ spanB * R := mul_nonneg (by norm_num [spanB, alphaP]) hR0
    have h48 : 0 ≤ 48 * ε * (ℓ : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) hε) (Nat.cast_nonneg ℓ)
    have hmul : (ℓ : ℝ) * rewY ≤ 6 * rewY := mul_le_mul_of_nonneg_right hℓ' hy
    linarith
  · -- at least six points: extend the data to sequences indexed by `ℕ`
    obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 6 := ⟨ℓ - 6, by omega⟩
    obtain ⟨Y, hY⟩ : ∃ Y : ℕ → ℝ, ∀ (p : ℕ) (h : p < n + 6), Y p = y ⟨p, h⟩ :=
      ⟨fun p => if h : p < n + 6 then y ⟨p, h⟩ else 0, fun p h => dif_pos h⟩
    obtain ⟨L, hL⟩ : ∃ L : ℕ → Fin 2, ∀ (p : ℕ) (h : p < n + 6), L p = lab ⟨p, h⟩ :=
      ⟨fun p => if h : p < n + 6 then lab ⟨p, h⟩ else 0, fun p h => dif_pos h⟩
    obtain ⟨E, hE⟩ : ∃ E : ℕ → ℕ → ℝ,
        ∀ (p q : ℕ) (hp : p < n + 6) (hq : q < n + 6), E p q = e ⟨p, hp⟩ ⟨q, hq⟩ :=
      ⟨fun p q => if h : p < n + 6 ∧ q < n + 6 then e ⟨p, h.1⟩ ⟨q, h.2⟩ else 0,
        fun p q hp hq => dif_pos ⟨hp, hq⟩⟩
    have key := transfer_nat hloc n Y L E ε R
      (fun p hp => by
        rw [hY (p + 1) hp, hY p (by omega)]
        exact hsep ⟨p, by omega⟩ ⟨p + 1, hp⟩ (Fin.mk_lt_mk.mpr (Nat.lt_succ_self p)))
      (fun p q hp hq => by
        rw [hY q hq, hY p hp]
        exact hR ⟨p, hp⟩ ⟨q, hq⟩)
      hε
      (fun p q hp hq hpq => by
        rw [hE p q hp hq]
        exact he0 _ _ (fun h => hpq (congrArg Fin.val h)))
      (fun p q hp hq hpq => by
        rw [hE p q hp hq, hY q hq, hY p hp]
        exact heK _ _ (fun h => hpq (congrArg Fin.val h)))
    have e1 : ∑ p ∈ range (n + 6), rew (L p) = ∑ i : Fin (n + 6), rew (lab i) := by
      rw [Finset.sum_range]
      exact sum_congr rfl fun i _ => by rw [hL i i.isLt]
    have e2 : ∑ p ∈ range (n + 6), ∑ q ∈ range (n + 6),
          (if p ≠ q then mulOf (L p) * mulOf (L q) * E p q else 0)
        = ∑ i : Fin (n + 6), ∑ j : Fin (n + 6),
          (if i ≠ j then mulOf (lab i) * mulOf (lab j) * e i j else 0) := by
      rw [Finset.sum_range]
      refine sum_congr rfl fun i _ => ?_
      rw [Finset.sum_range]
      refine sum_congr rfl fun j _ => ?_
      rw [hL i i.isLt, hL j j.isLt, hE i j i.isLt j.isLt]
      by_cases h : i = j
      · subst h
        simp
      · have h' : (i : ℕ) ≠ (j : ℕ) := fun hh => h (Fin.ext hh)
        rw [if_pos h', if_pos h]
    rw [e1, e2] at key
    exact key

end Distinct839
