/-
Ceilings/Distinct/Paper.lean — the certificate of the paper is a pair-energy certificate of range
six.

The proof of the 83.90% theorem bounds the pair energy from below by the seven-point local
inequality `Distinct839.LocalInequality`, summed over all windows of seven consecutive points
(`Distinct839/Transfer/`). The statement `Distinct839.TransferStatement` has all pairs on the
right and a tolerance; the summation itself uses only the pairs inside a window, that is the pairs
at index distance at most six. This file redoes the last step of that argument with the exact
kernel values and the pairs of range six, importing the four parts of the summation
(`window_inequality`, `sum_window_reward_ge`, `sum_window_pressure_le`,
`sum_window_potential_le'`, `sum_window_pairs_le`) from `Distinct839/Transfer/`:

    `LocalInequality → PairCert 6 rewX rewY spanB`        (`Distinct.paper_certificate_of_local`),

with the constant `C₃ = 6 y + Ω`. The local inequality itself is proved in
`Distinct839/Local/FinalAll.lean` (with one `native_decide`); the statement without hypothesis,
`paper_certificate`, is in `Ceilings/Distinct/PaperCert.lean`, so that the files of the ceilings
do not depend on that computation.

`Distinct.qFinal_eq` records that the constant `q` of the theorem is the constant of this
certificate, `(3 - C₀ + y - x - b)/(2 - 2x + y)`, with the upper bound `C₀` for `energyC`.
-/
import Ceilings.Periodic
import Ceilings.Distinct.Defs
import Distinct839.Transfer.Main

open scoped BigOperators
open Finset

namespace Ceilings.Distinct

open Distinct839 (K sep mulOf rew rewX rewY spanB omegaB alphaP LocalInequality Wtab pairTy)
open Distinct839.Transfer

/-- Pairs: the pair terms of all windows are at most the energy of the pairs of the chain at index
distance at most six. -/
theorem sum_window_pair_le_chain (n : ℕ) (Y : ℕ → ℝ) (L : ℕ → Fin 2) :
    ∑ w ∈ range n, ∑ i : Fin 7, ∑ j : Fin 7,
        (if i < j then (Wtab (pairTy (L (w + i)) (L (w + j))) i j : ℝ) / 1000000
            * K (Y (w + j) - Y (w + i)) ^ 2 else 0)
      ≤ chainEnergy K 6 (fun p => mulOf (L p)) Y (n + 6) := by
  have h1 : ∑ w ∈ range n, ∑ i : Fin 7, ∑ j : Fin 7,
        (if i < j then (Wtab (pairTy (L (w + i)) (L (w + j))) i j : ℝ) / 1000000
            * K (Y (w + j) - Y (w + i)) ^ 2 else 0)
      ≤ ∑ s : Fin 6, ∑ p ∈ range (n + 6),
          (if p + s + 1 < n + 6 then
            2 * mulOf (L p) * mulOf (L (p + s + 1)) * K (Y (p + s + 1) - Y p) ^ 2 else 0) :=
    sum_window_pairs_le n (fun p q i j => (Wtab (pairTy (L p) (L q)) i j : ℝ) / 1000000)
      (fun p q => 2 * mulOf (L p) * mulOf (L q)) (fun p q => K (Y q - Y p) ^ 2)
      (fun _ _ _ _ => Wtab_real_nonneg _ _ _) (fun _ _ s => Wtab_budget_real _ _ s)
      (fun _ _ _ _ => sq_nonneg _)
  refine h1.trans (le_of_eq ?_)
  rw [chainEnergy_eq_sum Distinct839.Transfer.K_neg, sum_comm]
  refine sum_congr rfl fun p _ => ?_
  exact Fin.sum_univ_eq_sum_range (fun s =>
    (if p + s + 1 < n + 6 then
      2 * mulOf (L p) * mulOf (L (p + s + 1)) * K (Y (p + s + 1) - Y p) ^ 2 else 0)) 6

/-- The transfer argument for a chain of `n + 6` sites indexed by `ℕ`, with the pairs of range
six and the exact kernel values. -/
theorem transfer_nat_range6 (hloc : LocalInequality) (n : ℕ) (Y : ℕ → ℝ) (L : ℕ → Fin 2)
    (R : ℝ) (hsep : ∀ p, p + 1 < n + 6 → sep ≤ Y (p + 1) - Y p)
    (hR : ∀ p q, p < n + 6 → q < n + 6 → Y q - Y p ≤ R) :
    ∑ p ∈ range (n + 6), rew (L p) - spanB * R - (6 * rewY + omegaB)
      ≤ chainEnergy K 6 (fun p => mulOf (L p)) Y (n + 6) := by
  have hsum := sum_le_sum fun w (hw : w ∈ range n) =>
    window_inequality hloc Y L w (fun r => hsep (w + r)
      (by have := mem_range.mp hw; have := r.isLt; omega))
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum] at hsum
  have h1 := sum_window_reward_ge L n
  have h2 := sum_window_pressure_le Y n R hR
  have h3 := sum_window_potential_le' Y L n
  have h4 := sum_window_pair_le_chain n Y L
  linarith

/-- **The certificate of the paper is a pair-energy certificate of range six**, given the
seven-point local inequality. -/
theorem paper_certificate_of_local (hloc : LocalInequality) : PairCert 6 rewX rewY spanB := by
  refine ⟨6 * rewY + omegaB, fun ℓ y lab R hsep hR0 hR => ?_⟩
  rcases Nat.lt_or_ge ℓ 6 with hℓ | hℓ
  · -- fewer than six points: the left side is nonpositive, the right side nonnegative
    have hrhs : 0 ≤ ∑ i : Fin ℓ, ∑ j : Fin ℓ,
        if i ≠ j ∧ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ ((6 : ℕ) : ℤ) then
          mulOf (lab i) * mulOf (lab j) * K (y j - y i) ^ 2 else 0 := by
      refine sum_nonneg fun i _ => sum_nonneg fun j _ => ?_
      split_ifs
      · exact pairTerm_nonneg K _ _ _
      · exact le_rfl
    have hlhs : ∑ i : Fin ℓ, (if lab i = 0 then rewX else rewY) ≤ (ℓ : ℝ) * rewY :=
      calc ∑ i : Fin ℓ, (if lab i = 0 then rewX else rewY) ≤ ∑ _i : Fin ℓ, rewY :=
            sum_le_sum fun i _ => rew_le_rewY (lab i)
        _ = (ℓ : ℝ) * rewY := by simp
    have hℓ' : (ℓ : ℝ) ≤ 6 := by exact_mod_cast hℓ.le
    have hy : (0 : ℝ) ≤ rewY := by norm_num [rewY]
    have hω : (0 : ℝ) ≤ omegaB := by norm_num [omegaB]
    have hsp : 0 ≤ spanB * R := mul_nonneg (by norm_num [spanB, alphaP]) hR0
    have hmul : (ℓ : ℝ) * rewY ≤ 6 * rewY := mul_le_mul_of_nonneg_right hℓ' hy
    linarith
  · -- at least six points: extend the data to sequences indexed by `ℕ`
    obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 6 := ⟨ℓ - 6, by omega⟩
    obtain ⟨Y, hY⟩ : ∃ Y : ℕ → ℝ, ∀ (p : ℕ) (h : p < n + 6), Y p = y ⟨p, h⟩ :=
      ⟨fun p => if h : p < n + 6 then y ⟨p, h⟩ else 0, fun p h => dif_pos h⟩
    obtain ⟨L, hL⟩ : ∃ L : ℕ → Fin 2, ∀ (p : ℕ) (h : p < n + 6), L p = lab ⟨p, h⟩ :=
      ⟨fun p => if h : p < n + 6 then lab ⟨p, h⟩ else 0, fun p h => dif_pos h⟩
    have key := transfer_nat_range6 hloc n Y L R
      (fun p hp => by
        rw [hY (p + 1) hp, hY p (by omega)]
        exact hsep ⟨p, by omega⟩ ⟨p + 1, hp⟩ (Fin.mk_lt_mk.mpr (Nat.lt_succ_self p)))
      (fun p q hp hq => by
        rw [hY q hq, hY p hp]
        exact hR ⟨p, hp⟩ ⟨q, hq⟩)
    have e1 : ∑ p ∈ range (n + 6), rew (L p)
        = ∑ i : Fin (n + 6), (if lab i = 0 then rewX else rewY) := by
      rw [Finset.sum_range]
      exact sum_congr rfl fun i _ => by rw [hL i i.isLt]; rfl
    have e2 : chainEnergy K 6 (fun p => mulOf (L p)) Y (n + 6)
        = ∑ i : Fin (n + 6), ∑ j : Fin (n + 6),
          if i ≠ j ∧ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ ((6 : ℕ) : ℤ) then
            mulOf (lab i) * mulOf (lab j) * K (y j - y i) ^ 2 else 0 := by
      rw [← sum_fin_range_energy]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      have hLi : L i = lab i := hL i i.isLt
      have hLj : L j = lab j := hL j j.isLt
      have hYi : Y i = y i := hY i i.isLt
      have hYj : Y j = y j := hY j j.isLt
      simp only [hLi, hLj, hYi, hYj]
    rw [e1, e2] at key
    exact key

/-- The constant of the 83.90% theorem is the constant of this certificate, with the upper bound
`C₀ = Distinct839.energyC0` for the energy constant. -/
theorem qFinal_eq : Distinct839.qFinal
    = (3 - Distinct839.energyC0 + rewY - rewX - spanB) / (2 - 2 * rewX + rewY) := by
  norm_num [Distinct839.qFinal, Distinct839.energyC0, rewX, rewY, spanB, alphaP]

end Ceilings.Distinct
