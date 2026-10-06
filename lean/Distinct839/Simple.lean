/-
Distinct839/Simple.lean — a corollary for simple zeros.

    liminf_{T → ∞} N_s(T) / N(T) ≥ 2 · 1645064/1960733 − 1 = 1329395/1960733 = 0.6780091935…

Here N_s(T) counts the simple zeros (multiplicity exactly 1) in the critical strip with ordinate
in (0, T]. A zero that is not simple has multiplicity at least 2, so in every window

    N ≥ N_s + 2 (N_d − N_s),   that is   2 N_d ≤ N + N_s        (`two_mul_Ndist_le`).

With N_d ≥ (q − ε/2) N from `distinct_zeros_839` this gives N_s ≥ 2 N_d − N ≥ (2q − 1 − ε) N.

The counting inequality uses two facts of the library `zeta23` about the zeros of `riemannZeta`:
a window contains finitely many zeros (`Zeta23.zerosIn_finite`) and the order of vanishing at a
zero of the strip is a natural number ≥ 1 (`Zeta23.zetaSeam.one_le_mult`).
-/
import Distinct839.Main

open Zeta23

namespace Distinct839

/-- **Counting inequality.** In every window, twice the number of distinct zeros is at most the
number of zeros with multiplicity plus the number of simple zeros: each zero ρ contributes `2` on
the left and `m_ρ + [m_ρ = 1]` on the right, and `m_ρ ≥ 1`. -/
theorem two_mul_Ndist_le (T₁ T₂ : ℝ) :
    2 * Ndist T₁ T₂ ≤ Ncount T₁ T₂ + Nsimple T₁ T₂ := by
  classical
  have hfin : (zerosIn T₁ T₂).Finite := zerosIn_finite T₁ T₂
  have hN : Ncount T₁ T₂ = ∑ ρ ∈ hfin.toFinset, zeroMult ρ :=
    finsum_mem_eq_finite_toFinset_sum _ hfin
  have hD : Ndist T₁ T₂ = hfin.toFinset.card := Set.ncard_eq_toFinset_card _ hfin
  have hS : Nsimple T₁ T₂ = (hfin.toFinset.filter fun ρ => zeroMult ρ = 1).card := by
    have hfin' : (zerosIn T₁ T₂ ∩ {ρ | zeroMult ρ = 1}).Finite := hfin.subset Set.inter_subset_left
    unfold Nsimple
    rw [Set.ncard_eq_toFinset_card _ hfin']
    congr 1
    ext ρ
    simp [Set.Finite.mem_toFinset]
  rw [hN, hD, hS, Finset.card_filter, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have h1 : 1 ≤ zeroMult ρ := zetaSeam.one_le_mult ρ (hfin.mem_toFinset.mp hρ).1
  split_ifs with h <;> omega

/-- The same inequality for the simple zeros alone: `2 N_d − N ≤ N_s`, over the reals. -/
theorem two_mul_Ndist_sub_Ncount_le (T₁ T₂ : ℝ) :
    2 * (Ndist T₁ T₂ : ℝ) - Ncount T₁ T₂ ≤ Nsimple T₁ T₂ := by
  have h : (2 : ℝ) * (Ndist T₁ T₂ : ℝ) ≤ (Ncount T₁ T₂ : ℝ) + (Nsimple T₁ T₂ : ℝ) := by
    exact_mod_cast two_mul_Ndist_le T₁ T₂
  linarith

/-- A lower bound `q` for the proportion of distinct zeros gives the lower bound `2 q − 1` for the
proportion of simple zeros. -/
theorem simple_of_distinct {q : ℝ}
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (q - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 * q - 1 - ε) * (Ncount 0 T : ℝ) ≤ Nsimple 0 T := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := h (ε / 2) (half_pos hε)
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have h2 := two_mul_Ndist_sub_Ncount_le 0 T
  linarith

/-- **More than 67.8% of the zeros of the Riemann zeta function are simple.** -/
theorem simple_zeros_678 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1329395 / 1960733 - ε) * (Ncount 0 T : ℝ) ≤ Nsimple 0 T := by
  have h := simple_of_distinct distinct_zeros_839
  have hq : (2 : ℝ) * (1645064 / 1960733) - 1 = 1329395 / 1960733 := by norm_num
  rwa [hq] at h

end Distinct839
