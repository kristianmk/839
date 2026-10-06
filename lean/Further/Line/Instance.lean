/-
Further/Line/Instance.lean — the seam for the average at a fixed height `T`.

The block-level seam of `Further/Line/Block.lean` is applied to the concrete block data of the
zeros with ordinate in `I' = (T − √T, 2T + √T]`, with the good set of `Simple673`,

    good = { simple on-line zeros of 𝒵(I') with ordinate in [T + √T, 2T − √T] }.

* `gram_goodZ`: the finite Gram theorem (`Simple673.GramEnergyStatement`) for the good zeros,
  `(1 + x₁)·#good − (b·TL/(2π) + (6x₁ + Ω) + Cη·#good) ≤ ∑_j φ₂(λ_j(Wᴴ W))`.
  This is the first half of the proof of `Simple673.Assembly.hatAz_seam673`, stated separately.
* `hatAz_seam_avg`:
  `4·tr Â − ‖Â‖² ≤ N(I') + N_s(I') + N₀(I') − x₁·s₁(I') + (4 + x₁)·Nedge + b·TL/(2π) + (6x₁ + Ω)
     + Cη·#𝒵(I')`.
* `seam_avg`: the same for `Ĝ = Â + Ê` (tail perturbation) and the window `(T, 2T]`:
  `N(I') = N + NII`, `N_s(I') ≤ N_s + NII`, `N₀(I') ≤ N₀ + NII`, `s₁(I') ≥ N₀ˢ(T, 2T)`.
-/
import Simple673.Assembly.Instance
import Further.Line.Block

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Real

namespace Further.Line

open Zeta23 Zeta23.ZeroSide Zeta23.Assembly
open Simple673 (rewX clipC phiC spanB omegaB GramEnergyStatement gramKappa ypos)
open Simple673.Assembly (GramCloseAt GramSepAt goodZ mem_goodZ goodZ_subset_onLine goodZ_mult_eq
  card_edge_le ypos_injective_goodZ rewX_nonneg)
open Distinct839.Assembly (goodW gram_apply Nedge gramKappa_comm ypos_sub gramRe_blockData)

section Inst

open Classical

/-! ### The finite Gram theorem for the good zeros -/

/-- **The clipped trace of the Gram matrix of the good zeros.** The constants `C, η₀` are those
of the finite Gram theorem. -/
theorem gram_goodZ (hGE : GramEnergyStatement) :
    ∃ C η₀ : ℝ, 0 ≤ C ∧ 0 < η₀ ∧ ∀ (Z : ZeroConfig) (T : ℝ) (P : Params),
      0 ≤ T → 0 < P.L T → 0 < P.a T →
      ∀ η : ℝ, 0 ≤ η → η ≤ η₀ → GramCloseAt P T η → GramSepAt P T →
      (1 + rewX) * (#(goodZ Z T) : ℝ)
          - (spanB * (T * P.L T / (2 * π)) + (7 * rewX + omegaB) + C * η * (#(goodZ Z T) : ℝ))
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

/-- **Seam for the average at height `T`, for `Â = P.hat T (Z.Az P T)`.** -/
theorem hatAz_seam_avg (hGE : GramEnergyStatement) :
    ∃ C η₀ : ℝ, 0 ≤ C ∧ 0 < η₀ ∧ ∀ (Z : ZeroConfig) (T : ℝ) (P : Params),
      0 ≤ T → 0 < P.L T → 0 < P.a T → PoissonSq T P →
      ∀ η : ℝ, 0 ≤ η → η ≤ η₀ → GramCloseAt P T η → GramSepAt P T →
      4 * rtrace (P.hat T (Z.Az P T)) - frobSq (P.hat T (Z.Az P T))
        ≤ (Z.NIprime T : ℝ) + (Z.Ns (T - D0 T) (2 * T + D0 T) : ℝ) + (Z.NonIprime T : ℝ)
          - rewX * (Z.s1 T : ℝ) + (4 + rewX) * (Nedge Z T : ℝ)
          + (spanB * (T * P.L T / (2 * π)) + (7 * rewX + omegaB)
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
  have hmain := seam_block_avg (blockData Z T P hconj)
    (mkPairReps Z T _ (evalVec_reflect hconj)) hgood hm1 hnrm
    (sum_normSq_v_le Z T P hconj hreal hPois) hE
  -- translate to the counts of `Z`
  have hA : P.hat T (Z.Az P T)
      = (blockData Z T P hconj).blockP (P.a T * P.L T ^ 2)
        + (blockData Z T P hconj).blockQ (P.a T * P.L T ^ 2) :=
    hat_Az_eq_hatP_add_hatQ Z T P hconj
  have hN : ((blockData Z T P hconj).Ncount : ℝ) = (Z.NIprime T : ℝ) := by
    rw [NIprime_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
  have hs1 : ((blockData Z T P hconj).s₁ : ℝ) = (Z.s1 T : ℝ) := by
    rw [s1_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
  have hNon : ((blockData Z T P hconj).Non : ℝ) = (Z.NonIprime T : ℝ) := by
    rw [NonIprime_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
  have hNs : (simpleCard (blockData Z T P hconj) : ℝ)
      = (Z.Ns (T - D0 T) (2 * T + D0 T) : ℝ) := by
    rw [Ns_Iprime_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
  have hcard : (Fintype.card (ZI Z T) : ℝ) = ((Z.ZIprime T).ncard : ℝ) := by
    rw [← coe_ZI, Set.ncard_coe_finset, Fintype.card_coe]
  have hedge : (#{z ∈ (blockData Z T P hconj).onLine \ goodZ Z T |
      (blockData Z T P hconj).m z = 1} : ℝ) ≤ (Nedge Z T : ℝ) := by
    exact_mod_cast card_edge_le hconj
  have hgc : (#(goodZ Z T) : ℝ) ≤ ((Z.ZIprime T).ncard : ℝ) := by
    rw [← hcard]; exact_mod_cast Finset.card_le_univ _
  have hCη : C * η * (#(goodZ Z T) : ℝ) ≤ C * η * ((Z.ZIprime T).ncard : ℝ) :=
    mul_le_mul_of_nonneg_left hgc (mul_nonneg hC hη0)
  have hx := rewX_nonneg
  have he : (4 + rewX) * (#{z ∈ (blockData Z T P hconj).onLine \ goodZ Z T |
      (blockData Z T P hconj).m z = 1} : ℝ) ≤ (4 + rewX) * (Nedge Z T : ℝ) :=
    mul_le_mul_of_nonneg_left hedge (by linarith)
  rw [hA]
  rw [hN, hs1, hNon, hNs] at hmain
  linarith

end Inst

/-! ### The seam for `Ĝ` on the window `(T, 2T]` -/

/-- **Seam for the average at height `T`.** With `Ĝ = P.hat T (Z.Gz P T)`, `B = θ₀/(aL)` and the
counts `N, N_s, N₀, N₀ˢ, N_d` of the window `(T, 2T]`:

`4·tr Ĝ − ‖Ĝ‖² − B(4 + 2‖Ĝ‖ + B)
   ≤ (N + NII) + (N_s + NII) + (N₀ + NII) − x₁·N₀ˢ + (4 + x₁)·Nedge + b·TL/(2π) + (6x₁ + Ω)
     + Cη(N_d + NII)`. -/
theorem seam_avg (hGE : GramEnergyStatement) :
    ∃ C η₀ : ℝ, 0 ≤ C ∧ 0 < η₀ ∧ ∀ (Z : ZeroConfig) (T : ℝ) (P : Params) (θ₀ : ℝ),
      0 ≤ T → 0 < P.L T → 0 < P.a T → PoissonSq T P → TailInputs Z P T θ₀ →
      ∀ η : ℝ, 0 ≤ η → η ≤ η₀ → GramCloseAt P T η → GramSepAt P T →
      4 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T))
          - θ₀ / (P.a T * P.L T)
            * (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
        ≤ ((Z.N T (2 * T) : ℝ) + (NII Z T : ℝ)) + ((Z.Ns T (2 * T) : ℝ) + (NII Z T : ℝ))
          + ((Z.N0 T (2 * T) : ℝ) + (NII Z T : ℝ))
          - rewX * (Z.N0s T (2 * T) : ℝ) + (4 + rewX) * (Nedge Z T : ℝ)
          + (spanB * (T * P.L T / (2 * π)) + (7 * rewX + omegaB)
              + C * η * ((Z.Nd T (2 * T) : ℝ) + (NII Z T : ℝ))) := by
  obtain ⟨C, η₀, hC, hη₀, hA⟩ := hatAz_seam_avg hGE
  refine ⟨C, η₀, hC, hη₀, ?_⟩
  intro Z T P θ₀ hT hL ha hPois hTl η hη0 hη hclose hsep
  obtain ⟨Bc, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := hA Z T P hT hL ha hPois η hη0 hη hclose hsep
  have hpert := ctr_sub_frobSq_perturb 4 (by norm_num) hGAE hB₀
    (htrE.trans hBle) (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hNs : (Z.Ns (T - D0 T) (2 * T + D0 T) : ℝ) ≤ (Z.Ns T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast Ns_Iprime_le Z hT
  have hN0 : (Z.NonIprime T : ℝ) ≤ (Z.N0 T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast N0_Iprime_le Z hT
  have hs1 : (Z.N0s T (2 * T) : ℝ) ≤ (Z.s1 T : ℝ) := by
    exact_mod_cast N0s_le_s1 Z hT
  have hZd : ((Z.ZIprime T).ncard : ℝ) ≤ (Z.Nd T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast card_ZIprime_le Z hT
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  rw [hNI] at hcore
  have h1 : rewX * (Z.N0s T (2 * T) : ℝ) ≤ rewX * (Z.s1 T : ℝ) :=
    mul_le_mul_of_nonneg_left hs1 rewX_nonneg
  have h2 : C * η * ((Z.ZIprime T).ncard : ℝ)
      ≤ C * η * ((Z.Nd T (2 * T) : ℝ) + (NII Z T : ℝ)) :=
    mul_le_mul_of_nonneg_left hZd (mul_nonneg hC hη0)
  linarith

end Further.Line
