/-
Simple673/Gram/Main.lean — the finite Gram theorem at clipping level 2 (`GramEnergyStatement`).

For positions `y` of simple points, a symmetric real matrix `κ` within `η` of the kernel matrix
`K(y_i - y_j)` which is bounded by `normS = 19/10` on `sep`-separated subsets, and the positive
semidefinite matrix `G` with the entries of `κ`:

    tr φ_2(G) ≥ (1 + x₁) |ι| - spanB · R - (7 x₁ + omegaB) - C η |ι|,

with `C = 44` and for `η ≤ η₀ = 1/100`. Here `x₁ = rewX = 8722 · 10⁻⁶`,
`spanB = 7α = 4389 · 10⁻⁶` and `7 x₁ + omegaB = 64936 · 10⁻⁶` (`Defs.lean`), and `R` bounds the
differences of the positions.

Proof: take a maximal matching of pairs at distance less than `sep`
(`Distinct839/Gram/Matching.lean`); the unmatched set is `sep`-separated. Pinch `G` onto the
pairs and the unmatched set (`Distinct839/Gram/Pinching.lean`). Each pair block gives
`2(1 + x₁) - 10η` (`PairBlock.lean`, from `x₁ ≤ β`); the unmatched block is not clipped, because
`normS ≤ 2`, and is handled by the transfer statement (`Remainder.lean`). The loss per point is
`5η` in a pair and `44η` in the unmatched set (`2η` on the diagonal and `14 · 3η` for the at most
fourteen neighbours at index distance at most seven).

Unlike `Distinct839/Gram/Main.lean` there are no labels: all points have multiplicity `1`.
-/
import Distinct839.Gram.Matching
import Simple673.Gram.PairBlock
import Simple673.Gram.Remainder

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Simple673.Gram

/-- **The finite Gram theorem at clipping level 2**, with explicit constants: for `η ≤ 1/100`,
`(1 + x₁) |ι| - spanB · R - (7 x₁ + omegaB) - 44 η |ι| ≤ tr φ_2(G)`. -/
theorem gramEnergy_explicit (hβ : BetaBound) (htr : TransferStatement)
    {ι : Type} [Fintype ι] [DecidableEq ι] {y : ι → ℝ} {κ : ι → ι → ℝ}
    {η R : ℝ} {G : Matrix ι ι ℂ} (hG : G.PosSemidef) (D : GramData y κ η G)
    (hform : ∀ S : Finset ι, (∀ i ∈ S, ∀ j ∈ S, i ≠ j → sep ≤ |y i - y j|) →
      ∀ x : ι → ℝ, ∑ i ∈ S, ∑ j ∈ S, x i * κ i j * x j ≤ normS * ∑ i ∈ S, x i ^ 2)
    (hR : 0 ≤ R) (hspan : ∀ i j, y i - y j ≤ R) :
    (1 + rewX) * Fintype.card ι - spanB * R - (7 * rewX + omegaB) - 44 * η * Fintype.card ι
      ≤ ∑ k, phiC clipC (hG.1.eigenvalues k) := by
  have hη0 := D.eta_nonneg
  -- a maximal matching of close pairs; its fixed points are separated
  obtain ⟨σ, hσ, hσsep⟩ := Distinct839.Gram.exists_maximal_matching y sep
  -- pinching onto the pairs and the set of fixed points
  have hpinch := Distinct839.Gram.pinching_phiC (Distinct839.Gram.matchLabel σ) hG (c := clipC)
    (by unfold clipC; norm_num)
  refine le_trans ?_ hpinch
  -- the estimate for each block
  have hblock : ∀ k : Option (Sym2 ι),
      ∑ _a : {l // Distinct839.Gram.matchLabel σ l = k}, (1 + rewX - 44 * η)
          - (if k = none then spanB * R + (7 * rewX + omegaB) else 0)
        ≤ ∑ t, phiC clipC ((Distinct839.Gram.blockOf_posSemidef
            (Distinct839.Gram.matchLabel σ) hG k).1.eigenvalues t) := by
    intro k
    rcases k with _ | z
    · -- the remainder block
      rw [if_pos rfl]
      exact remainder_block_ge htr D hG (Distinct839.Gram.matchLabel σ) none
        (fun i j hi hj hij =>
          hσsep i j (Distinct839.Gram.matchLabel_eq_none.1 hi)
            (Distinct839.Gram.matchLabel_eq_none.1 hj) hij)
        hform hR hspan
    · -- a pair block (or an empty block)
      rw [if_neg (Option.some_ne_none z), sub_zero]
      by_cases hne : Nonempty {l // Distinct839.Gram.matchLabel σ l = some z}
      · obtain ⟨⟨i, hi⟩⟩ := hne
        obtain ⟨hi1, hi2⟩ := Distinct839.Gram.matchLabel_eq_some.1 hi
        subst hi2
        have h := pair_block_ge hβ D hG (Distinct839.Gram.matchLabel σ) (some s(i, σ i))
          (i := i) (j := σ i) (fun h => hi1 h.symm) (hσ.close i hi1) hi
          (Distinct839.Gram.matchLabel_partner hσ.invol hi1)
          (fun l hl => Distinct839.Gram.eq_or_eq_of_matchLabel hl)
        refine le_trans (Finset.sum_le_sum fun a _ => ?_) h
        linarith
      · have : IsEmpty {l // Distinct839.Gram.matchLabel σ l = some z} := not_nonempty_iff.1 hne
        rw [Finset.univ_eq_empty]
        simp
  -- add up the blocks
  have hsum : (1 + rewX) * Fintype.card ι - spanB * R - (7 * rewX + omegaB)
        - 44 * η * Fintype.card ι
      = ∑ k : Option (Sym2 ι),
          (∑ _a : {l // Distinct839.Gram.matchLabel σ l = k}, (1 + rewX - 44 * η)
            - (if k = none then spanB * R + (7 * rewX + omegaB) else 0)) := by
    rw [Finset.sum_sub_distrib,
      Fintype.sum_fiberwise (Distinct839.Gram.matchLabel σ) fun _ => 1 + rewX - 44 * η,
      Finset.sum_ite_eq' Finset.univ none, if_pos (Finset.mem_univ _), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hsum]
  exact Finset.sum_le_sum fun k _ => hblock k

end Simple673.Gram

namespace Simple673

open Gram

/-- **The finite Gram theorem at clipping level 2** (`GramEnergyStatement` of `Spec.lean`), from
the lower bound `BetaBound` for the kernel near the origin and the transfer statement. The
constants are `C = 44` and `η₀ = 1/100`. The hypothesis that the positions are distinct is not
used. -/
theorem gramEnergy (hβ : BetaBound) (htr : TransferStatement) : GramEnergyStatement := by
  refine ⟨44, 1 / 100, by norm_num, by norm_num, ?_⟩
  intro ι _ _ y κ η R G hG _ hη0 hη1 hsymm hclose hform hR hspan hentry
  exact gramEnergy_explicit hβ htr hG ⟨hη0, hη1, hsymm, hclose, hentry⟩ hform hR hspan

end Simple673
