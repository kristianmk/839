/-
Distinct839/Assembly/Instance.lean — the seam at a fixed height `T`.

The block-level seam of `Block.lean` is applied to the concrete block data of the zeros with
ordinate in `I' = (T − √T, 2T + √T]` (`Zeta23.ZeroSide.blockData`). The good set is

    good = { on-line zeros of 𝒵(I') with multiplicity ≤ 2 and ordinate in [T + √T, 2T − √T] }.

Its weighted Gram matrix has the entries `√(m m')·gramKappa(γ, γ')`, so the finite Gram theorem
(`GramEnergyStatement`) applies, given the two pieces of Gram data at height `T`
(`GramCloseAt`, `GramSepAt`; these are the two halves of `GramDataStatement`). The on-line zeros
of multiplicity at most two outside the bulk are counted by `Nedge`. The results:

* `hatAz_seam839`: `2c·tr Â − ‖Â‖² ≤ ν·N(I') + μ·#𝒵(I') + c²·Nedge + b·TL/(2π) + (6y + Ω) + Cη·#𝒵(I')`;
* `seam839`: the same for `Ĝ = Â + Ê` (tail perturbation) and the window `(T, 2T]`.
-/
import Zeta23.Assembly.SeamMult
import Zeta23.ZeroSide.Final
import Distinct839.Spec2
import Distinct839.Assembly.Block
import Distinct839.Assembly.EdgeCount

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Real

namespace Distinct839.Assembly

open Zeta23 Zeta23.ZeroSide Zeta23.Assembly

/-! ### The Gram data at a fixed height -/

/-- Closeness of the Gram entries to the kernel in the bulk, at height `T` with error `η`. -/
def GramCloseAt (P : Params) (T η : ℝ) : Prop :=
  ∀ γ γ' : ℝ, T + D0 T ≤ γ → γ ≤ 2 * T - D0 T → T + D0 T ≤ γ' → γ' ≤ 2 * T - D0 T →
    |gramKappa P T γ γ' - K (ypos P T γ - ypos P T γ')| ≤ η

/-- The separated bound at height `T`. -/
def GramSepAt (P : Params) (T : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (γ : ι → ℝ) (x : ι → ℝ),
    (∀ i j, i ≠ j → sep ≤ |ypos P T (γ i) - ypos P T (γ j)|) →
    ∑ i, ∑ j, x i * gramKappa P T (γ i) (γ j) * x j ≤ clipC / 2 * ∑ i, x i ^ 2

/-- `GramDataStatement` is the conjunction of the two fixed-height statements, eventually. -/
lemma gramDataStatement_iff (lam : ℝ) :
    GramDataStatement lam ↔
      (∃ η : ℝ → ℝ, Filter.Tendsto η Filter.atTop (nhds 0) ∧
        ∀ᶠ T in Filter.atTop, GramCloseAt (Pfam lam T) T (η T)) ∧
      (∀ᶠ T in Filter.atTop, GramSepAt (Pfam lam T) T) := Iff.rfl

lemma gramKappa_comm (P : Params) (T γ γ' : ℝ) : gramKappa P T γ γ' = gramKappa P T γ' γ := by
  unfold gramKappa
  congr 1
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

lemma ypos_sub (P : Params) (T γ γ' : ℝ) :
    ypos P T γ - ypos P T γ' = (γ - γ') * P.L T / (2 * π) := by
  unfold ypos; ring

/-- The error of closeness is nonnegative as soon as the bulk is nonempty. -/
lemma GramCloseAt.nonneg {P : Params} {T η : ℝ} (h : GramCloseAt P T η) (hT : 4 ≤ T) : 0 ≤ η := by
  have hs : D0 T * D0 T = T := Real.mul_self_sqrt (by linarith)
  have hs0 : 0 ≤ D0 T := Real.sqrt_nonneg T
  have h2 : 2 * D0 T ≤ T := by nlinarith [sq_nonneg (D0 T - 2)]
  exact (abs_nonneg _).trans (h (T + D0 T) (T + D0 T) le_rfl (by linarith) le_rfl (by linarith))

section Inst

open Classical

variable (Z : ZeroConfig) (T : ℝ) (P : Params)

/-- The good zeros: on the line, multiplicity at most two, ordinate in the bulk
`[T + √T, 2T − √T]`. -/
def goodZ : Finset (ZI Z T) :=
  {z | (z : ℂ).re = 1 / 2 ∧ Z.mult z ≤ 2 ∧ T + D0 T ≤ (z : ℂ).im ∧ (z : ℂ).im ≤ 2 * T - D0 T}

variable {Z T}

lemma mem_goodZ {z : ZI Z T} :
    z ∈ goodZ Z T ↔ (z : ℂ).re = 1 / 2 ∧ Z.mult z ≤ 2 ∧ T + D0 T ≤ (z : ℂ).im ∧
      (z : ℂ).im ≤ 2 * T - D0 T := by
  simp [goodZ]

variable {P}

lemma goodZ_subset_onLine (hconj : PhiHatConj T P) :
    goodZ Z T ⊆ (blockData Z T P hconj).onLine := by
  intro z hz
  rw [ZeroBlockData.mem_onLine]
  exact (mkData_σ_eq_iff Z T _ _ z).mpr (mem_goodZ.mp hz).1

lemma goodZ_mult_le (hconj : PhiHatConj T P) :
    ∀ z ∈ goodZ Z T, (blockData Z T P hconj).m z ≤ 2 :=
  fun _ hz => (mem_goodZ.mp hz).2.1

/-- The vector of an on-line zero is the real vector `(φ̂(γ − τ_k))_k`. -/
lemma blockData_v_onLine (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (z : ZI Z T)
    (hz : (z : ℂ).re = 1 / 2) (k : Fin (P.d T)) :
    (blockData Z T P hconj).v z k = (P.phiHatR T ((z : ℂ).im - P.tau T k) : ℂ) := by
  simp only [blockData, mkData_v, evalVec]
  rw [gammaOf_of_re_eq_half hz, ← Complex.ofReal_sub, hreal]

/-- For on-line zeros the normalised inner product of the block data is `gramKappa`. -/
lemma gramRe_blockData (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (z z' : ZI Z T)
    (hz : (z : ℂ).re = 1 / 2) (hz' : (z' : ℂ).re = 1 / 2) :
    gramRe (blockData Z T P hconj) (P.a T * P.L T ^ 2) z z'
      = gramKappa P T (z : ℂ).im (z' : ℂ).im := by
  unfold gramRe gramKappa
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [blockData_v_onLine hconj hreal z hz k, blockData_v_onLine hconj hreal z' hz' k,
    Complex.ofReal_re, Complex.ofReal_re]

/-- The on-line zeros of multiplicity at most two outside the good set lie within `√T` of `T`
or of `2T`; their number is at most `Nedge`. -/
lemma card_edge_le (hconj : PhiHatConj T P) :
    #{z ∈ (blockData Z T P hconj).onLine \ goodZ Z T | (blockData Z T P hconj).m z ≤ 2}
      ≤ Nedge Z T := by
  set s : Finset (ZI Z T) :=
    {z ∈ (blockData Z T P hconj).onLine \ goodZ Z T | (blockData Z T P hconj).m z ≤ 2} with hs
  have hsub : ((s.map (Function.Embedding.subtype _) : Finset ℂ) : Set ℂ)
      ⊆ Z.window (T - D0 T) (T + D0 T) ∪ Z.window (2 * T - D0 T) (2 * T + D0 T) := by
    intro ρ hρ
    simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image,
      Finset.mem_coe] at hρ
    obtain ⟨z, hz, rfl⟩ := hρ
    rw [hs, Finset.mem_filter, Finset.mem_sdiff, ZeroBlockData.mem_onLine] at hz
    obtain ⟨⟨hon, hng⟩, hm⟩ := hz
    have hre : (z : ℂ).re = 1 / 2 := (mkData_σ_eq_iff Z T _ _ z).mp hon
    have hm' : Z.mult z ≤ 2 := hm
    obtain ⟨hcar, hlo, hhi⟩ := (mem_ZIprime_iff Z T).mp ((mem_ZI Z T).mp z.2)
    have hnb : ¬ (T + D0 T ≤ (z : ℂ).im ∧ (z : ℂ).im ≤ 2 * T - D0 T) :=
      fun h => hng (mem_goodZ.mpr ⟨hre, hm', h.1, h.2⟩)
    have h0 := D0_nonneg T
    by_cases h1 : (z : ℂ).im < T + D0 T
    · exact Or.inl ⟨hcar, hlo, h1.le⟩
    · refine Or.inr ⟨hcar, ?_, hhi⟩
      by_contra h2
      exact hnb ⟨not_lt.mp h1, not_lt.mp h2⟩
  have h1 := Set.ncard_le_ncard hsub ((Z.window_finite _ _).union (Z.window_finite _ _))
  rw [Set.ncard_coe_finset, Finset.card_map] at h1
  have h2 := Set.ncard_union_le (Z.window (T - D0 T) (T + D0 T))
    (Z.window (2 * T - D0 T) (2 * T + D0 T))
  have h3 := Z.Nd_le_N (T - D0 T) (T + D0 T)
  have h4 := Z.Nd_le_N (2 * T - D0 T) (2 * T + D0 T)
  unfold ZeroConfig.Nd at h3 h4
  unfold Nedge
  omega

/-- The positions `γ L/(2π)` of the good zeros are pairwise distinct. -/
lemma ypos_injective_goodZ (hL : 0 < P.L T) :
    Function.Injective (fun z : goodZ Z T => ypos P T ((z : ZI Z T) : ℂ).im) := by
  intro z z' h
  have him : ((z : ZI Z T) : ℂ).im = ((z' : ZI Z T) : ℂ).im := by
    simp only [ypos] at h
    have hpos : (0 : ℝ) < 2 * π := by positivity
    have h' := (div_left_inj' hpos.ne').mp h
    exact mul_right_cancel₀ hL.ne' h'
  have hre : ((z : ZI Z T) : ℂ).re = ((z' : ZI Z T) : ℂ).re := by
    rw [(mem_goodZ.mp z.2).1, (mem_goodZ.mp z'.2).1]
  exact Subtype.ext (Subtype.ext (Complex.ext hre him))

end Inst

/-! ### The seam for `Â` -/

/-- **Seam at height `T` for `Â = P.hat T (Z.Az P T)`.** The constants `C, η₀` are those of the
finite Gram theorem. -/
theorem hatAz_seam839 (hGE : GramEnergyStatement) :
    ∃ C η₀ : ℝ, 0 ≤ C ∧ 0 < η₀ ∧ ∀ (Z : ZeroConfig) (T : ℝ) (P : Params),
      0 ≤ T → 0 < P.L T → 0 < P.a T → PoissonSq T P →
      ∀ η : ℝ, 0 ≤ η → η ≤ η₀ → GramCloseAt P T η → GramSepAt P T →
      2 * clipC * rtrace (P.hat T (Z.Az P T)) - frobSq (P.hat T (Z.Az P T))
        ≤ nuC * (Z.NIprime T : ℝ) + muC * ((Z.ZIprime T).ncard : ℝ)
          + clipC ^ 2 * (Nedge Z T : ℝ)
          + (spanB * (T * P.L T / (2 * π)) + (6 * rewY + omegaB)
              + C * η * ((Z.ZIprime T).ncard : ℝ)) := by
  classical
  obtain ⟨C, η₀, hC, hη₀, hGE'⟩ := hGE
  refine ⟨C, η₀, hC, hη₀, ?_⟩
  intro Z T P hT hL ha hPois η hη0 hη hclose hsep
  have hconj : PhiHatConj T P := phiHatConj
  have hreal : PhiHatReal T P := phiHatReal
  have hnrm : 0 < P.a T * P.L T ^ 2 := by positivity
  have hgood := goodZ_subset_onLine (Z := Z) hconj
  have hm2 := goodZ_mult_le (Z := Z) hconj
  have h0 := D0_nonneg T
  have hπ : (0 : ℝ) < 2 * π := by positivity
  -- the finite Gram theorem for the good zeros
  have hGram := hGE' (↥(goodZ Z T)) (fun z => ypos P T ((z : ZI Z T) : ℂ).im)
    (fun z => labOf (Z.mult ((z : ZI Z T) : ℂ)))
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
        mulOf_labOf (Z.one_le_mult _ (mem_carrier_of_mem_ZI Z T (z : ZI Z T).2))
          (mem_goodZ.mp z.2).2.1,
        mulOf_labOf (Z.one_le_mult _ (mem_carrier_of_mem_ZI Z T (z' : ZI Z T).2))
          (mem_goodZ.mp z'.2).2.1]
      rfl)
  -- rewrite its left side as a sum over the good set
  have hsum : ∑ z : goodZ Z T, (mulOf (labOf (Z.mult ((z : ZI Z T) : ℂ))) ^ 2
        + rew (labOf (Z.mult ((z : ZI Z T) : ℂ))))
      = ∑ z ∈ goodZ Z T, (((blockData Z T P hconj).m z : ℝ) ^ 2
        + rew (labOf ((blockData Z T P hconj).m z))) := by
    rw [← Finset.sum_coe_sort (goodZ Z T)]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [mulOf_labOf (Z.one_le_mult _ (mem_carrier_of_mem_ZI Z T (z : ZI Z T).2))
      (mem_goodZ.mp z.2).2.1]
    rfl
  rw [hsum, Fintype.card_coe] at hGram
  have hE : ∑ z ∈ goodZ Z T, (((blockData Z T P hconj).m z : ℝ) ^ 2
        + rew (labOf ((blockData Z T P hconj).m z)))
      - (spanB * (T * P.L T / (2 * π)) + (6 * rewY + omegaB) + C * η * (#(goodZ Z T) : ℝ))
      ≤ ∑ j, phiC clipC ((Matrix.posSemidef_conjTranspose_mul_self
          (goodW (blockData Z T P hconj) (goodZ Z T) (P.a T * P.L T ^ 2))).1.eigenvalues j) := by
    linarith
  have hmain := seam_block_count (blockData Z T P hconj)
    (mkPairReps Z T _ (evalVec_reflect hconj)) hgood hm2 hnrm
    (sum_normSq_v_le Z T P hconj hreal hPois) hE
  -- translate to the counts of `Z`
  have hA : P.hat T (Z.Az P T)
      = (blockData Z T P hconj).blockP (P.a T * P.L T ^ 2)
        + (blockData Z T P hconj).blockQ (P.a T * P.L T ^ 2) :=
    hat_Az_eq_hatP_add_hatQ Z T P hconj
  have hN : ((blockData Z T P hconj).Ncount : ℝ) = (Z.NIprime T : ℝ) := by
    rw [NIprime_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
  have hcard : (Fintype.card (ZI Z T) : ℝ) = ((Z.ZIprime T).ncard : ℝ) := by
    rw [← coe_ZI, Set.ncard_coe_finset, Fintype.card_coe]
  have hedge : (#{z ∈ (blockData Z T P hconj).onLine \ goodZ Z T |
      (blockData Z T P hconj).m z ≤ 2} : ℝ) ≤ (Nedge Z T : ℝ) := by
    exact_mod_cast card_edge_le hconj
  have hgc : (#(goodZ Z T) : ℝ) ≤ ((Z.ZIprime T).ncard : ℝ) := by
    rw [← hcard]; exact_mod_cast Finset.card_le_univ _
  have hCη : C * η * (#(goodZ Z T) : ℝ) ≤ C * η * ((Z.ZIprime T).ncard : ℝ) :=
    mul_le_mul_of_nonneg_left hgc (mul_nonneg hC hη0)
  have hc2 : clipC ^ 2 * (#{z ∈ (blockData Z T P hconj).onLine \ goodZ Z T |
      (blockData Z T P hconj).m z ≤ 2} : ℝ) ≤ clipC ^ 2 * (Nedge Z T : ℝ) :=
    mul_le_mul_of_nonneg_left hedge (sq_nonneg _)
  rw [hA]
  rw [hN, hcard] at hmain
  linarith

/-! ### The seam for `Ĝ` on the window `(T, 2T]` -/

/-- **Seam at height `T`.** With `Ĝ = P.hat T (Z.Gz P T)`, `B = θ₀/(aL)`, `N = N(T, 2T)`,
`N_d = N_d(T, 2T)`:

`2c·tr Ĝ − ‖Ĝ‖² − B(2c + 2‖Ĝ‖ + B)
   ≤ ν(N + NII) + μ(N_d + NII) + c²·Nedge + b·TL/(2π) + (6y + Ω) + Cη(N_d + NII)`. -/
theorem seam839 (hGE : GramEnergyStatement) :
    ∃ C η₀ : ℝ, 0 ≤ C ∧ 0 < η₀ ∧ ∀ (Z : ZeroConfig) (T : ℝ) (P : Params) (θ₀ : ℝ),
      0 ≤ T → 0 < P.L T → 0 < P.a T → PoissonSq T P → TailInputs Z P T θ₀ →
      ∀ η : ℝ, 0 ≤ η → η ≤ η₀ → GramCloseAt P T η → GramSepAt P T →
      2 * clipC * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T))
          - θ₀ / (P.a T * P.L T)
            * (2 * clipC + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
        ≤ nuC * ((Z.N T (2 * T) : ℝ) + (NII Z T : ℝ))
          + muC * ((Z.Nd T (2 * T) : ℝ) + (NII Z T : ℝ))
          + clipC ^ 2 * (Nedge Z T : ℝ)
          + (spanB * (T * P.L T / (2 * π)) + (6 * rewY + omegaB)
              + C * η * ((Z.Nd T (2 * T) : ℝ) + (NII Z T : ℝ))) := by
  obtain ⟨C, η₀, hC, hη₀, hA⟩ := hatAz_seam839 hGE
  refine ⟨C, η₀, hC, hη₀, ?_⟩
  intro Z T P θ₀ hT hL ha hPois hTl η hη0 hη hclose hsep
  obtain ⟨Bc, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := hA Z T P hT hL ha hPois η hη0 hη hclose hsep
  have hpert := ctr_sub_frobSq_perturb (2 * clipC) (by have := clipC_pos; linarith) hGAE hB₀
    (htrE.trans hBle) (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hZd : ((Z.ZIprime T).ncard : ℝ) ≤ (Z.Nd T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast card_ZIprime_le Z hT
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  rw [hNI] at hcore
  have h1 : muC * ((Z.ZIprime T).ncard : ℝ) ≤ muC * ((Z.Nd T (2 * T) : ℝ) + (NII Z T : ℝ)) :=
    mul_le_mul_of_nonneg_left hZd muC_pos.le
  have h2 : C * η * ((Z.ZIprime T).ncard : ℝ)
      ≤ C * η * ((Z.Nd T (2 * T) : ℝ) + (NII Z T : ℝ)) :=
    mul_le_mul_of_nonneg_left hZd (mul_nonneg hC hη0)
  linarith

end Distinct839.Assembly
