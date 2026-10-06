/-
Line889/Assembly/Instance.lean — the seam for "simple or on the line" at a fixed height `T`.

The block-level seam of `Line889/Assembly/Block.lean` is applied to the concrete block data of
the zeros with ordinate in `I' = (T − √T, 2T + √T]` (`Zeta23.ZeroSide.blockData`). The good set
is that of `Simple673`,

    good = { simple on-line zeros of 𝒵(I') with ordinate in [T + √T, 2T − √T] }.

Its Gram matrix has the entries `gramKappa(γ, γ')` (all multiplicities are one), so the finite
Gram theorem (`GramEnergyStatement`) applies, given the two pieces of Gram data at height `T`
(`GramCloseAt`, `GramSepAt`; these are the two halves of `GramDataStatement`). The simple
on-line zeros outside the bulk are counted by `Nedge`. With `t = tLev`, `e₁ = 1 + x`,
`e₀ = e0C`, `b = spanB`:

* `gram_goodZ`: the finite Gram theorem for the good zeros,
  `(1 + x)·#good − (b·TL/(2π) + (6x + Ω) + Cη·#good) ≤ ∑_j φ₂(λ_j(Wᴴ W))`.
* `hatAz_seam_sl`:
  `2t·tr Â − ‖Â‖² ≤ (2t − e₀)·N(I') + (e₀ − e₁)·N_{s∨0}(I') + t²·Nedge + b·TL/(2π) + (6x + Ω)
     + Cη·#𝒵(I')`.
* `seam_sl`: the same for `Ĝ = Â + Ê` (tail perturbation) and the window `(T, 2T]`, with
  `N(I') = N + NII` and `N_{s∨0}(I') ≤ N_{s∨0} + NII`.

The good set and its lemmas do not depend on the window; they are those of
`Simple673/Assembly/Instance.lean` (`goodZ`, `mem_goodZ`, `goodZ_subset_onLine`, `goodZ_mult_eq`,
`card_edge_le`, `ypos_injective_goodZ`). The lemmas `gramKappa_comm`, `ypos_sub`,
`gramRe_blockData`, `gram_apply` and the count `Nedge` are those of `Distinct839/Assembly/`, and
the counts `NsL`, `simpleOrLineSum` those of `Further/Counting.lean`. The two fixed-height
statements `GramCloseAt`, `GramSepAt` mention the kernel `K`, the separation `sep` and the bound
`normS` of this development and are defined here.
-/
import Simple673.Assembly.Instance
import Line889.Spec2
import Line889.Assembly.Block

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Real

namespace Line889.Assembly

open Zeta23 Zeta23.ZeroSide Zeta23.Assembly
open Simple673.Assembly (goodZ mem_goodZ goodZ_subset_onLine goodZ_mult_eq card_edge_le
  ypos_injective_goodZ)
open Distinct839.Assembly (goodW gram_apply Nedge gramKappa_comm ypos_sub gramRe_blockData)
open Further (simpleOrLineSum NsL NsL_Iprime_le NsL_Iprime_eq_mk)

/-! ### The Gram data at a fixed height -/

/-- Closeness of the Gram entries to the kernel in the bulk, at height `T` with error `η`. -/
def GramCloseAt (P : Params) (T η : ℝ) : Prop :=
  ∀ γ γ' : ℝ, T + D0 T ≤ γ → γ ≤ 2 * T - D0 T → T + D0 T ≤ γ' → γ' ≤ 2 * T - D0 T →
    |gramKappa P T γ γ' - K (ypos P T γ - ypos P T γ')| ≤ η

/-- The separated bound at height `T`, with the constant `normS = 17/10 < 2`. -/
def GramSepAt (P : Params) (T : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (γ : ι → ℝ) (x : ι → ℝ),
    (∀ i j, i ≠ j → sep ≤ |ypos P T (γ i) - ypos P T (γ j)|) →
    ∑ i, ∑ j, x i * gramKappa P T (γ i) (γ j) * x j ≤ normS * ∑ i, x i ^ 2

/-- `GramDataStatement` is the conjunction of the two fixed-height statements, eventually. -/
lemma gramDataStatement_iff (lam : ℝ) :
    GramDataStatement lam ↔
      (∃ η : ℝ → ℝ, Filter.Tendsto η Filter.atTop (nhds 0) ∧
        ∀ᶠ T in Filter.atTop, GramCloseAt (Pfam lam T) T (η T)) ∧
      (∀ᶠ T in Filter.atTop, GramSepAt (Pfam lam T) T) := Iff.rfl

/-- The error of closeness is nonnegative as soon as the bulk is nonempty. -/
lemma GramCloseAt.nonneg {P : Params} {T η : ℝ} (h : GramCloseAt P T η) (hT : 4 ≤ T) : 0 ≤ η := by
  have hs : D0 T * D0 T = T := Real.mul_self_sqrt (by linarith)
  have hs0 : 0 ≤ D0 T := Real.sqrt_nonneg T
  have h2 : 2 * D0 T ≤ T := by nlinarith [sq_nonneg (D0 T - 2)]
  exact (abs_nonneg _).trans (h (T + D0 T) (T + D0 T) le_rfl (by linarith) le_rfl (by linarith))

section Inst

open Classical

/-! ### The finite Gram theorem for the good zeros -/

/-- **The clipped trace of the Gram matrix of the good zeros**, at clipping level `2`:
`(1 + x)·#good − (b·TL/(2π) + (6x + Ω) + Cη·#good) ≤ ∑_j φ₂(λ_j(Wᴴ W))`. The span of the
positions of the good zeros is at most `TL/(2π)`. The constants `C, η₀` are those of the finite
Gram theorem. -/
theorem gram_goodZ (hGE : GramEnergyStatement) :
    ∃ C η₀ : ℝ, 0 ≤ C ∧ 0 < η₀ ∧ ∀ (Z : ZeroConfig) (T : ℝ) (P : Params),
      0 ≤ T → 0 < P.L T → 0 < P.a T →
      ∀ η : ℝ, 0 ≤ η → η ≤ η₀ → GramCloseAt P T η → GramSepAt P T →
      (1 + rewX) * (#(goodZ Z T) : ℝ)
          - (spanB * (T * P.L T / (2 * π)) + (6 * rewX + omegaB) + C * η * (#(goodZ Z T) : ℝ))
        ≤ ∑ j, phiC clipC ((Matrix.posSemidef_conjTranspose_mul_self
            (goodW (blockData Z T P phiHatConj) (goodZ Z T)
              (P.a T * P.L T ^ 2))).1.eigenvalues j) := by
  obtain ⟨C, η₀, hC, hη₀, hGE'⟩ := hGE
  refine ⟨C, η₀, hC, hη₀, ?_⟩
  intro Z T P hT hL ha η hη0 hη hclose hsep
  have hconj : PhiHatConj T P := phiHatConj
  have hreal : PhiHatReal T P := phiHatReal
  have hnrm : 0 < P.a T * P.L T ^ 2 := by positivity
  have hgood := goodZ_subset_onLine (Z := Z) hconj
  have hm1 := goodZ_mult_eq (Z := Z) hconj
  have h0 := D0_nonneg T
  have hπ : (0 : ℝ) < 2 * π := by positivity
  -- the finite Gram theorem for the good zeros
  have hGram := hGE' (↥(goodZ Z T)) (fun z => ypos P T ((z : ZI Z T) : ℂ).im)
    (fun z z' => gramKappa P T ((z : ZI Z T) : ℂ).im ((z' : ZI Z T) : ℂ).im)
    η (T * P.L T / (2 * π))
    ((goodW (blockData Z T P hconj) (goodZ Z T) (P.a T * P.L T ^ 2))ᴴ
      * goodW (blockData Z T P hconj) (goodZ Z T) (P.a T * P.L T ^ 2))
    (Matrix.posSemidef_conjTranspose_mul_self _)
    (ypos_injective_goodZ hL) hη0 hη
    (fun z z' => gramKappa_comm P T _ _)
    (fun z z' => hclose _ _ (mem_goodZ.mp z.2).2.2.1 (mem_goodZ.mp z.2).2.2.2
      (mem_goodZ.mp z'.2).2.2.1 (mem_goodZ.mp z'.2).2.2.2)
    (fun S hS x => by
      have h := hsep (↥S) (fun s => (((s : goodZ Z T) : ZI Z T) : ℂ).im) (fun s => x s)
        (fun i j hij => hS i i.2 j j.2 (fun h => hij (Subtype.ext h)))
      rw [← Finset.sum_coe_sort S, ← Finset.sum_coe_sort S (fun i => x i ^ 2)]
      refine le_trans (le_of_eq ?_) h
      exact Finset.sum_congr rfl fun i _ => (Finset.sum_coe_sort S _).symm)
    (by positivity)
    (fun z z' => by
      have h1 := (mem_goodZ.mp z.2).2.2.2
      have h2 := (mem_goodZ.mp z'.2).2.2.1
      rw [ypos_sub, mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    (fun z z' => by
      rw [gram_apply _ hgood hnrm z z',
        gramRe_blockData hconj hreal _ _ (mem_goodZ.mp z.2).1 (mem_goodZ.mp z'.2).1,
        hm1 z z.2, hm1 z' z'.2]
      simp)
  rw [Fintype.card_coe] at hGram
  linarith

/-! ### The seam for `Â` -/

/-- **Seam for "simple or on the line" at height `T`, for `Â = P.hat T (Z.Az P T)`**:
`2t·tr Â − ‖Â‖² ≤ (2t − e₀)·N(I') + (e₀ − e₁)·N_{s∨0}(I') + t²·Nedge + b·TL/(2π) + (6x + Ω)
   + Cη·#𝒵(I')`,
with the counts of the window `I' = (T − √T, 2T + √T]`. -/
theorem hatAz_seam_sl (hGE : GramEnergyStatement) :
    ∃ C η₀ : ℝ, 0 ≤ C ∧ 0 < η₀ ∧ ∀ (Z : ZeroConfig) (T : ℝ) (P : Params),
      0 ≤ T → 0 < P.L T → 0 < P.a T → PoissonSq T P →
      ∀ η : ℝ, 0 ≤ η → η ≤ η₀ → GramCloseAt P T η → GramSepAt P T →
      2 * tLev * rtrace (P.hat T (Z.Az P T)) - frobSq (P.hat T (Z.Az P T))
        ≤ (2 * tLev - e0C) * (Z.NIprime T : ℝ)
          + (e0C - e1C) * (NsL Z (T - D0 T) (2 * T + D0 T) : ℝ)
          + tLev ^ 2 * (Nedge Z T : ℝ)
          + (spanB * (T * P.L T / (2 * π)) + (6 * rewX + omegaB)
              + C * η * ((Z.ZIprime T).ncard : ℝ)) := by
  obtain ⟨C, η₀, hC, hη₀, hG⟩ := gram_goodZ hGE
  refine ⟨C, η₀, hC, hη₀, ?_⟩
  intro Z T P hT hL ha hPois η hη0 hη hclose hsep
  have hconj : PhiHatConj T P := phiHatConj
  have hreal : PhiHatReal T P := phiHatReal
  have hnrm : 0 < P.a T * P.L T ^ 2 := by positivity
  have hgood := goodZ_subset_onLine (Z := Z) hconj
  have hm1 := goodZ_mult_eq (Z := Z) hconj
  have hE := hG Z T P hT hL ha η hη0 hη hclose hsep
  have hmain := seam_block_sl (blockData Z T P hconj)
    (mkPairReps Z T _ (evalVec_reflect hconj)) hgood hm1 hnrm
    (sum_normSq_v_le Z T P hconj hreal hPois) hE
  -- translate to the counts of `Z`
  have hA : P.hat T (Z.Az P T)
      = (blockData Z T P hconj).blockP (P.a T * P.L T ^ 2)
        + (blockData Z T P hconj).blockQ (P.a T * P.L T ^ 2) :=
    hat_Az_eq_hatP_add_hatQ Z T P hconj
  have hN : ((blockData Z T P hconj).Ncount : ℝ) = (Z.NIprime T : ℝ) := by
    rw [NIprime_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
  have hSL : (simpleOrLineSum (blockData Z T P hconj) : ℝ)
      = (NsL Z (T - D0 T) (2 * T + D0 T) : ℝ) := by
    rw [NsL_Iprime_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
  have hcard : (Fintype.card (ZI Z T) : ℝ) = ((Z.ZIprime T).ncard : ℝ) := by
    rw [← coe_ZI, Set.ncard_coe_finset, Fintype.card_coe]
  -- the simple on-line zeros outside the good set lie at the edges
  have hedge : (#{z ∈ (blockData Z T P hconj).onLine \ goodZ Z T |
      (blockData Z T P hconj).m z = 1} : ℝ) ≤ (Nedge Z T : ℝ) := by
    exact_mod_cast card_edge_le hconj
  have hgc : (#(goodZ Z T) : ℝ) ≤ ((Z.ZIprime T).ncard : ℝ) := by
    rw [← hcard]; exact_mod_cast Finset.card_le_univ _
  have hCη : C * η * (#(goodZ Z T) : ℝ) ≤ C * η * ((Z.ZIprime T).ncard : ℝ) :=
    mul_le_mul_of_nonneg_left hgc (mul_nonneg hC hη0)
  have ht2 : tLev ^ 2 * (#{z ∈ (blockData Z T P hconj).onLine \ goodZ Z T |
      (blockData Z T P hconj).m z = 1} : ℝ) ≤ tLev ^ 2 * (Nedge Z T : ℝ) :=
    mul_le_mul_of_nonneg_left hedge (sq_nonneg _)
  rw [hA]
  rw [hN, hSL] at hmain
  linarith

end Inst

/-! ### The seam for `Ĝ` on the window `(T, 2T]` -/

/-- **Seam for "simple or on the line" at height `T`.** With `Ĝ = P.hat T (Z.Gz P T)`,
`B = θ₀/(aL)` and the counts `N, N_{s∨0}, N_d` of the window `(T, 2T]`:

`2t·tr Ĝ − ‖Ĝ‖² − B(2t + 2‖Ĝ‖ + B)
   ≤ (2t − e₀)(N + NII) + (e₀ − e₁)(N_{s∨0} + NII) + t²·Nedge + b·TL/(2π) + (6x + Ω)
     + Cη(N_d + NII)`. -/
theorem seam_sl (hGE : GramEnergyStatement) :
    ∃ C η₀ : ℝ, 0 ≤ C ∧ 0 < η₀ ∧ ∀ (Z : ZeroConfig) (T : ℝ) (P : Params) (θ₀ : ℝ),
      0 ≤ T → 0 < P.L T → 0 < P.a T → PoissonSq T P → TailInputs Z P T θ₀ →
      ∀ η : ℝ, 0 ≤ η → η ≤ η₀ → GramCloseAt P T η → GramSepAt P T →
      2 * tLev * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T))
          - θ₀ / (P.a T * P.L T)
            * (2 * tLev + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
        ≤ (2 * tLev - e0C) * ((Z.N T (2 * T) : ℝ) + (NII Z T : ℝ))
          + (e0C - e1C) * ((NsL Z T (2 * T) : ℝ) + (NII Z T : ℝ))
          + tLev ^ 2 * (Nedge Z T : ℝ)
          + (spanB * (T * P.L T / (2 * π)) + (6 * rewX + omegaB)
              + C * η * ((Z.Nd T (2 * T) : ℝ) + (NII Z T : ℝ))) := by
  obtain ⟨C, η₀, hC, hη₀, hA⟩ := hatAz_seam_sl hGE
  refine ⟨C, η₀, hC, hη₀, ?_⟩
  intro Z T P θ₀ hT hL ha hPois hTl η hη0 hη hclose hsep
  obtain ⟨Bc, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := hA Z T P hT hL ha hPois η hη0 hη hclose hsep
  have hpert := ctr_sub_frobSq_perturb (2 * tLev) (by have := tLev_pos; linarith) hGAE hB₀
    (htrE.trans hBle) (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hSL : (NsL Z (T - D0 T) (2 * T + D0 T) : ℝ) ≤ (NsL Z T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NsL_Iprime_le Z hT
  have hZd : ((Z.ZIprime T).ncard : ℝ) ≤ (Z.Nd T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast card_ZIprime_le Z hT
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  rw [hNI] at hcore
  have h1 : (e0C - e1C) * (NsL Z (T - D0 T) (2 * T + D0 T) : ℝ)
      ≤ (e0C - e1C) * ((NsL Z T (2 * T) : ℝ) + (NII Z T : ℝ)) :=
    mul_le_mul_of_nonneg_left hSL e0C_sub_e1C_pos.le
  have h2 : C * η * ((Z.ZIprime T).ncard : ℝ)
      ≤ C * η * ((Z.Nd T (2 * T) : ℝ) + (NII Z T : ℝ)) :=
    mul_le_mul_of_nonneg_left hZd (mul_nonneg hC hη0)
  linarith

end Line889.Assembly
