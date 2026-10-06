/-
Distinct839/Gram/Main.lean — the finite Gram theorem (`GramEnergyStatement`).

For positions `y`, labels with multiplicities `m_i ∈ {1, 2}`, a symmetric real matrix `κ` within
`η` of the kernel matrix `K(y_i - y_j)` which is bounded by `c/2` on `sep`-separated subsets,
and the positive semidefinite matrix `G = D^{1/2} κ D^{1/2}`:

    tr φ_c(G) ≥ ∑_i (m_i² + rew_i) - spanB · R - (6 rewY + omegaB) - C η |ι|,

with `C = 152` and for `η ≤ η₀ = 1/100`.

Proof: take a maximal matching of pairs at distance less than `sep` (`Matching.lean`); the
unmatched set is `sep`-separated. Pinch `G` onto the pairs and the unmatched set
(`Pinching.lean`). Each pair block gives its diagonal squares and both rewards
(`PairBlock.lean`); the unmatched block is not clipped and is handled by the transfer statement
(`Remainder.lean`).
-/
import Distinct839.Gram.Matching
import Distinct839.Gram.PairBlock
import Distinct839.Gram.Remainder

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Distinct839.Gram

/-- **The finite Gram theorem**, with explicit constants: for `η ≤ 1/100`,
`∑ (m_i² + rew_i) - spanB · R - (6 rewY + omegaB) - 152 η |ι| ≤ tr φ_c(G)`. -/
theorem gramEnergy_explicit (hβ : BetaBound) (htr : TransferStatement)
    {ι : Type} [Fintype ι] [DecidableEq ι] {y : ι → ℝ} {lab : ι → Fin 2} {κ : ι → ι → ℝ}
    {η R : ℝ} {G : Matrix ι ι ℂ} (hG : G.PosSemidef) (D : GramData y lab κ η G)
    (hform : ∀ S : Finset ι, (∀ i ∈ S, ∀ j ∈ S, i ≠ j → sep ≤ |y i - y j|) →
      ∀ x : ι → ℝ, ∑ i ∈ S, ∑ j ∈ S, x i * κ i j * x j ≤ clipC / 2 * ∑ i ∈ S, x i ^ 2)
    (hR : 0 ≤ R) (hspan : ∀ i j, y i - y j ≤ R) :
    ∑ i, (mulOf (lab i) ^ 2 + rew (lab i)) - spanB * R - (6 * rewY + omegaB)
        - 152 * η * Fintype.card ι
      ≤ ∑ k, phiC clipC (hG.1.eigenvalues k) := by
  have hη0 := D.eta_nonneg
  -- a maximal matching of close pairs; its fixed points are separated
  obtain ⟨σ, hσ, hσsep⟩ := exists_maximal_matching y sep
  -- pinching onto the pairs and the set of fixed points
  have hpinch := pinching_phiC (matchLabel σ) hG (c := clipC) (by norm_num [clipC])
  refine le_trans ?_ hpinch
  -- the estimate for each block
  have hblock : ∀ k : Option (Sym2 ι),
      ∑ a : {l // matchLabel σ l = k}, (mulOf (lab a) ^ 2 + rew (lab a) - 152 * η)
          - (if k = none then spanB * R + (6 * rewY + omegaB) else 0)
        ≤ ∑ t, phiC clipC ((blockOf_posSemidef (matchLabel σ) hG k).1.eigenvalues t) := by
    intro k
    rcases k with _ | z
    · -- the remainder block
      rw [if_pos rfl]
      exact remainder_block_ge htr D hG (matchLabel σ) none
        (fun i j hi hj hij =>
          hσsep i j (matchLabel_eq_none.1 hi) (matchLabel_eq_none.1 hj) hij)
        hform hR hspan
    · -- a pair block (or an empty block)
      rw [if_neg (Option.some_ne_none z), sub_zero]
      by_cases hne : Nonempty {l // matchLabel σ l = some z}
      · obtain ⟨⟨i, hi⟩⟩ := hne
        obtain ⟨hi1, hi2⟩ := matchLabel_eq_some.1 hi
        subst hi2
        have h := pair_block_ge hβ D hG (matchLabel σ) (some s(i, σ i))
          (i := i) (j := σ i) (fun h => hi1 h.symm) (hσ.close i hi1) hi
          (matchLabel_partner hσ.invol hi1) (fun l hl => eq_or_eq_of_matchLabel hl)
        refine le_trans (Finset.sum_le_sum fun a _ => ?_) h
        linarith
      · have : IsEmpty {l // matchLabel σ l = some z} := not_nonempty_iff.1 hne
        rw [Finset.univ_eq_empty]
        simp
  -- add up the blocks
  have hsum : ∑ i, (mulOf (lab i) ^ 2 + rew (lab i)) - spanB * R - (6 * rewY + omegaB)
        - 152 * η * Fintype.card ι
      = ∑ k : Option (Sym2 ι),
          (∑ a : {l // matchLabel σ l = k}, (mulOf (lab a) ^ 2 + rew (lab a) - 152 * η)
            - (if k = none then spanB * R + (6 * rewY + omegaB) else 0)) := by
    rw [Finset.sum_sub_distrib,
      Fintype.sum_fiberwise (matchLabel σ) fun i => mulOf (lab i) ^ 2 + rew (lab i) - 152 * η,
      Finset.sum_ite_eq' Finset.univ none, if_pos (Finset.mem_univ _), Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hsum]
  exact Finset.sum_le_sum fun k _ => hblock k

end Distinct839.Gram

namespace Distinct839

open Gram

/-- **The finite Gram theorem** (`GramEnergyStatement` of `Spec.lean`), from the lower bound
`BetaBound` for the kernel near the origin and the transfer statement. The constants are
`C = 152` and `η₀ = 1/100`. -/
theorem gramEnergy (hβ : BetaBound) (htr : TransferStatement) : GramEnergyStatement := by
  refine ⟨152, 1 / 100, by norm_num, by norm_num, ?_⟩
  intro ι _ _ y lab κ η R G hG _ hη0 hη1 hsymm hclose hform hR hspan hentry
  exact gramEnergy_explicit hβ htr hG ⟨hη0, hη1, hsymm, hclose, hentry⟩ hform hR hspan

end Distinct839
