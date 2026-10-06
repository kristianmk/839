/-
Distinct839/Assembly/Block.lean — the block-level seam.

Setting: the abstract zero-side data `ZeroBlockData ι d` of `Zeta23/ZeroSide.lean` (distinct
points `z : ι` with multiplicities `m z ≥ 1`, vectors `v z`, the reflection `σ`), a normalisation
`nrm = a L² > 0`, and a set `good` of on-line indices. The matrix `Â = blockP + blockQ` is split as

    Â = P_good + Q',   P_good = W Wᴴ,   Q' = (on-line part outside `good`) + blockQ,

where `W = goodW` has the columns `√m_z · v_z / √nrm`, `z ∈ good`. Then

* `posIndex Q' ≤ p + #(onLine \ good)`                                   (`posIndex_restQ_le`);
* the threshold inequality gives a bound in terms of the Gram matrix `Wᴴ W` (`seam_block`);
* the entries of `Wᴴ W` are `√(m_z m_z') · κ(z, z')` with `κ = gramRe` real (`gram_apply`);
* the counting step (`seam_count`): with `ν = 2c − 3 − y + x`, `μ = 2 − 2x + y`,
  `∑_{good} (2c m − m² − rew) + c²(p + #(onLine \ good)) ≤ ν·N + μ·#ι + c²·e`,
  `e` the number of on-line indices outside `good` of multiplicity at most two.

The combination is `seam_block_count`.
-/
import Zeta23.ZeroSide.Mult
import Distinct839.Assembly.Threshold
import Distinct839.Assembly.Constants

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Distinct839.Assembly

open Zeta23 Zeta23.ZeroSide Zeta23.ZeroSide.RankTraceMult

section Block

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d) (good : Finset ι)

/-! ### The decomposition `Â = P_good + Q'` -/

/-- The part of `A` carried by the good indices: `∑_{z ∈ good} m_z v_z v_zᵀ`. -/
def goodPart : Matrix d d ℂ := ∑ z ∈ good, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)

/-- The on-line part of `A` outside `good`. -/
def restPart : Matrix d d ℂ :=
  ∑ z ∈ D.onLine \ good, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)

/-- Multiplicities of the good indices, as reals. -/
def goodM : good → ℝ := fun z => (D.m z : ℝ)

/-- Normalised vectors `v_z / √nrm` of the good indices. -/
def goodV (nrm : ℝ) : good → d → ℂ := fun z k => D.v z k / (Real.sqrt nrm : ℂ)

/-- The `d × good` matrix with columns `√m_z · v_z / √nrm`. -/
def goodW (nrm : ℝ) : Matrix d good ℂ := Wmat (goodM D good) (goodV D good nrm)

/-- `Q' = nrm⁻¹ • restPart + blockQ`. -/
def restQ (nrm : ℝ) : Matrix d d ℂ := ((nrm⁻¹ : ℝ) : ℂ) • restPart D good + D.blockQ nrm

/-- Normalised real inner product of two vectors: `nrm⁻¹ ∑_k Re(v_z k)·Re(v_z' k)`. -/
def gramRe (nrm : ℝ) (z z' : ι) : ℝ := nrm⁻¹ * ∑ k, (D.v z k).re * (D.v z' k).re

lemma goodM_nonneg (z : good) : 0 ≤ goodM D good z := Nat.cast_nonneg _

variable {good}

lemma onPart_eq (hgood : good ⊆ D.onLine) : D.onPart = goodPart D good + restPart D good := by
  unfold goodPart restPart ZeroBlockData.onPart
  rw [add_comm, Finset.sum_sdiff hgood]

/-- The vectors of on-line indices are real. -/
lemma conj_v_of_good (hgood : good ⊆ D.onLine) (z : good) (k : d) :
    starRingEnd ℂ (D.v z k) = D.v z k := by
  have h := congrFun (D.star_v_of_onLine ((D.mem_onLine).mp (hgood z.2))) k
  rwa [Pi.star_apply, RCLike.star_def] at h

lemma v_eq_re_of_good (hgood : good ⊆ D.onLine) (z : good) (k : d) :
    D.v z k = ((D.v z k).re : ℂ) :=
  (Complex.conj_eq_iff_re.mp (conj_v_of_good D hgood z k)).symm

/-- `nrm⁻¹ • goodPart = W Wᴴ`. -/
theorem smul_goodPart_eq (hgood : good ⊆ D.onLine) {nrm : ℝ} (hnrm : 0 < nrm) :
    ((nrm⁻¹ : ℝ) : ℂ) • goodPart D good = goodW D good nrm * (goodW D good nrm)ᴴ := by
  ext a b
  rw [show goodW D good nrm * (goodW D good nrm)ᴴ
      = Pmat (𝕜 := ℂ) (goodM D good) (goodV D good nrm) from rfl,
    Pmat_apply (fun z => goodM_nonneg D good z)]
  simp only [goodPart, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_coe_sort good]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [goodM, goodV]
  rw [map_div₀, conj_v_of_good D hgood z b, Complex.conj_ofReal]
  have hsq : ((Real.sqrt nrm : ℂ)) ^ 2 = (nrm : ℂ) := by
    rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt hnrm.le]
  have hc0 : (Real.sqrt nrm : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hnrm).ne'
  have hcc : (nrm : ℂ) ≠ 0 := by exact_mod_cast hnrm.ne'
  rw [div_mul_div_comm, ← sq, hsq]
  push_cast
  field_simp

/-- `Â = blockP + blockQ = W Wᴴ + Q'`. -/
theorem blockP_add_blockQ_eq (hgood : good ⊆ D.onLine) {nrm : ℝ} (hnrm : 0 < nrm) :
    D.blockP nrm + D.blockQ nrm
      = goodW D good nrm * (goodW D good nrm)ᴴ + restQ D good nrm := by
  rw [← smul_goodPart_eq D hgood hnrm]
  unfold ZeroBlockData.blockP restQ
  rw [onPart_eq D hgood, smul_add, add_assoc]

variable (good)

lemma restPart_posSemidef : (restPart D good).PosSemidef := by
  unfold restPart
  refine posSemidef_sum _ fun z hz => ?_
  have hz' : z ∈ D.onLine := (Finset.mem_sdiff.mp hz).1
  have := ZeroBlockData.posSemidef_smul_vecMulVec (D.star_v_of_onLine ((D.mem_onLine).mp hz'))
    (Nat.cast_nonneg (D.m z))
  simpa using this

lemma rank_restPart_le : (restPart D good).rank ≤ #(D.onLine \ good) := by
  unfold restPart
  refine (rank_sum_le _ _ (fun _ => 1) fun z _ => rank_smul_vecMulVec_le _ _ _).trans ?_
  simp

lemma smul_restPart_posSemidef {nrm : ℝ} (hnrm : 0 < nrm) :
    (((nrm⁻¹ : ℝ) : ℂ) • restPart D good).PosSemidef :=
  (restPart_posSemidef D good).smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hnrm.le))

/-- `Q'` is Hermitian. -/
theorem restQ_isHermitian {nrm : ℝ} (hnrm : 0 < nrm) : (restQ D good nrm).IsHermitian :=
  (smul_restPart_posSemidef D good hnrm).isHermitian.add (D.blockQ_isHermitian nrm)

/-- `n₊(Q') ≤ p + #(onLine \ good)`: the pairs give at most `p` positive directions, and the
on-line part outside `good` is positive semidefinite of rank at most the number of its terms. -/
theorem posIndex_restQ_le (Pr : D.PairReps) {nrm : ℝ} (hnrm : 0 < nrm) :
    posIndex (restQ_isHermitian D good hnrm) ≤ Pr.p + #(D.onLine \ good) := by
  have hR := smul_restPart_posSemidef D good hnrm
  have h1 := posIndex_add_le hR.isHermitian (D.blockQ_isHermitian nrm)
  have h2 : posIndex hR.isHermitian ≤ #(D.onLine \ good) := by
    rw [posIndex_eq_rank_of_posSemidef hR,
      rank_smul_of_ne_zero _ (by exact_mod_cast (inv_ne_zero hnrm.ne'))]
    exact rank_restPart_le D good
  have h3 := D.posIndex_blockQ_le Pr hnrm
  exact h1.trans (by omega)

variable {good}

/-- `‖v_z/√nrm‖² ≤ 1` for good indices, from the truncated Poisson bound. -/
lemma xsq_goodV_le (hgood : good ⊆ D.onLine) {nrm : ℝ} (hnrm : 0 < nrm)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ nrm) (z : good) :
    xsq (goodV D good nrm) z ≤ 1 := by
  unfold xsq goodV
  have hs : ∀ k, ‖D.v z k / (Real.sqrt nrm : ℂ)‖ ^ 2 = ‖D.v z k‖ ^ 2 / nrm := by
    intro k
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hnrm),
      div_pow, Real.sq_sqrt hnrm.le]
  simp_rw [hs]
  rw [← Finset.sum_div, div_le_one hnrm]
  exact hPois z (hgood z.2)

/-- `tr(W Wᴴ) ≤ ∑_{z ∈ good} m_z`. -/
lemma rtrace_goodW_le (hgood : good ⊆ D.onLine) {nrm : ℝ} (hnrm : 0 < nrm)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ nrm) :
    rtrace (goodW D good nrm * (goodW D good nrm)ᴴ) ≤ ∑ z ∈ good, (D.m z : ℝ) := by
  rw [show goodW D good nrm * (goodW D good nrm)ᴴ
      = Pmat (𝕜 := ℂ) (goodM D good) (goodV D good nrm) from rfl,
    rtrace_Pmat (fun z => goodM_nonneg D good z), ← Finset.sum_coe_sort good]
  refine Finset.sum_le_sum fun z _ => ?_
  have h1 := xsq_goodV_le D hgood hnrm hPois z
  have h0 := goodM_nonneg D good z
  calc goodM D good z * xsq (goodV D good nrm) z ≤ goodM D good z * 1 :=
        mul_le_mul_of_nonneg_left h1 h0
    _ = (D.m z : ℝ) := by rw [mul_one]; rfl

/-! ### The seam at the block level, in terms of the Gram matrix -/

/-- **Block seam.** With `G = Wᴴ W` the weighted Gram matrix of the good indices,
`2c·tr Â − ‖Â‖_F² ≤ 2c·∑_{good} m_z − ∑_j φ_c(λ_j(G)) + c²·(p + #(onLine \ good))`. -/
theorem seam_block (Pr : D.PairReps) (hgood : good ⊆ D.onLine) {nrm : ℝ} (hnrm : 0 < nrm)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ nrm) {c : ℝ} (hc : 0 < c) :
    2 * c * rtrace (D.blockP nrm + D.blockQ nrm) - frobSq (D.blockP nrm + D.blockQ nrm)
      ≤ 2 * c * ∑ z ∈ good, (D.m z : ℝ)
        - (∑ j, phiC c
            ((Matrix.posSemidef_conjTranspose_mul_self (goodW D good nrm)).1.eigenvalues j))
        + c ^ 2 * ((Pr.p + #(D.onLine \ good) : ℕ) : ℝ) := by
  rw [blockP_add_blockQ_eq D hgood hnrm]
  have h := threshold_gram (goodW D good nrm) (restQ_isHermitian D good hnrm)
    (posIndex_restQ_le D good Pr hnrm) hc
  have htr := rtrace_goodW_le D hgood hnrm hPois
  have : 2 * c * rtrace (goodW D good nrm * (goodW D good nrm)ᴴ)
      ≤ 2 * c * ∑ z ∈ good, (D.m z : ℝ) := mul_le_mul_of_nonneg_left htr (by linarith)
  linarith

/-- **Entries of the Gram matrix**: `(Wᴴ W)_{z z'} = √(m_z m_z') · κ(z, z')`, with the real
normalised inner product `κ = gramRe`. -/
theorem gram_apply (hgood : good ⊆ D.onLine) {nrm : ℝ} (hnrm : 0 < nrm) (z z' : good) :
    ((goodW D good nrm)ᴴ * goodW D good nrm) z z'
      = ((Real.sqrt ((D.m z : ℝ) * (D.m z' : ℝ)) * gramRe D nrm z z' : ℝ) : ℂ) := by
  have hs : ((Real.sqrt nrm : ℝ) : ℂ) * ((Real.sqrt nrm : ℝ) : ℂ) = (nrm : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hnrm.le]
  have hc0 : ((Real.sqrt nrm : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hnrm).ne'
  have hcc : (nrm : ℂ) ≠ 0 := by exact_mod_cast hnrm.ne'
  rw [Matrix.mul_apply, Real.sqrt_mul (Nat.cast_nonneg _)]
  simp only [gramRe]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.conjTranspose_apply, goodW, Wmat, goodM, goodV, RCLike.star_def, map_mul,
    map_div₀, Complex.conj_ofReal, RCLike.conj_ofReal, conj_v_of_good D hgood z a]
  rw [← v_eq_re_of_good D hgood z a, ← v_eq_re_of_good D hgood z' a]
  simp only [RCLike.ofReal_eq_complex_ofReal]
  field_simp
  rw [sq, hs]
  ring

/-! ### The counting step -/

/-- **Counting.** `∑_{good} (2c m − m² − rew) + c²(p + #(onLine \ good)) ≤ ν·N + μ·#ι + c²·e`,
where `e` counts the on-line indices outside `good` of multiplicity at most two. -/
theorem seam_count (Pr : D.PairReps) (hgood : good ⊆ D.onLine) (hm2 : ∀ z ∈ good, D.m z ≤ 2) :
    ∑ z ∈ good, (2 * clipC * (D.m z : ℝ) - ((D.m z : ℝ) ^ 2 + rew (labOf (D.m z))))
        + clipC ^ 2 * ((Pr.p + #(D.onLine \ good) : ℕ) : ℝ)
      ≤ nuC * (D.Ncount : ℝ) + muC * (Fintype.card ι : ℝ)
        + clipC ^ 2 * (#{z ∈ D.onLine \ good | D.m z ≤ 2} : ℝ) := by
  have hν := nuC_pos
  have hμ := muC_pos
  set f : ι → ℝ := fun z => nuC * (D.m z : ℝ) + muC with hf
  have hm1 : ∀ z, (1 : ℝ) ≤ D.m z := fun z => by exact_mod_cast D.one_le_m z
  -- the right side as a sum over all indices
  have htot : nuC * (D.Ncount : ℝ) + muC * (Fintype.card ι : ℝ) = ∑ z, f z := by
    simp only [hf, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ZeroBlockData.Ncount, Nat.cast_sum]
    ring
  -- off-line pairs
  have hpair : clipC ^ 2 * (Pr.p : ℝ) ≤ ∑ z ∈ Pr.R, (f z + f (D.σ z)) := by
    have : ∀ z ∈ Pr.R, clipC ^ 2 ≤ f z + f (D.σ z) := fun z _ => by
      have h1 := le_mul_of_one_le_right hν.le (hm1 z)
      have h2 := le_mul_of_one_le_right hν.le (hm1 (D.σ z))
      have := coeff_pair
      simp only [hf]
      linarith
    calc clipC ^ 2 * (Pr.p : ℝ) = ∑ _z ∈ Pr.R, clipC ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]; rfl
      _ ≤ ∑ z ∈ Pr.R, (f z + f (D.σ z)) := Finset.sum_le_sum this
  -- good indices
  have hgoodsum : ∑ z ∈ good, (2 * clipC * (D.m z : ℝ) - ((D.m z : ℝ) ^ 2 + rew (labOf (D.m z))))
      = ∑ z ∈ good, f z := by
    refine Finset.sum_congr rfl fun z hz => ?_
    have h1 := D.one_le_m z
    have h2 := hm2 z hz
    have h : D.m z = 1 ∨ D.m z = 2 := by omega
    simp only [hf]
    rcases h with h | h
    · rw [h, labOf_one, rew_zero]
      have := coeff_simple
      push_cast
      linarith
    · rw [h, labOf_two, rew_one]
      have := coeff_double
      push_cast
      linarith
  -- on-line indices outside `good`
  have hrest : clipC ^ 2 * (#(D.onLine \ good) : ℝ)
      - clipC ^ 2 * (#{z ∈ D.onLine \ good | D.m z ≤ 2} : ℝ) ≤ ∑ z ∈ D.onLine \ good, f z := by
    have hterm : ∀ z ∈ D.onLine \ good,
        clipC ^ 2 - clipC ^ 2 * (if D.m z ≤ 2 then (1 : ℝ) else 0) ≤ f z := fun z _ => by
      by_cases h : D.m z ≤ 2
      · rw [if_pos h]
        have h1 : (0 : ℝ) ≤ nuC * (D.m z : ℝ) := mul_nonneg hν.le (Nat.cast_nonneg _)
        simp only [hf]
        linarith
      · rw [if_neg h]
        have h3 : (3 : ℝ) ≤ D.m z := by exact_mod_cast (by omega : 3 ≤ D.m z)
        have h4 := mul_le_mul_of_nonneg_left h3 hν.le
        have := coeff_triple
        simp only [hf]
        linarith
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
      Finset.sum_boole] at hsum
    linarith
  have hsplit : ∑ z, f z = (∑ z ∈ good, f z + ∑ z ∈ D.onLine \ good, f z)
      + ∑ z ∈ Pr.R, (f z + f (D.σ z)) := by
    rw [D.sum_split Pr f, add_comm (∑ z ∈ good, f z), Finset.sum_sdiff hgood]
  rw [htot, hsplit, hgoodsum]
  push_cast
  linarith

/-- **Block seam with counting.** If the clipped trace of the Gram matrix `G = Wᴴ W` of the good
indices satisfies `∑_{good} (m² + rew) − E ≤ ∑_j φ_c(λ_j(G))`, then
`2c·tr Â − ‖Â‖_F² ≤ ν·N + μ·#ι + c²·e + E`. -/
theorem seam_block_count (Pr : D.PairReps) (hgood : good ⊆ D.onLine)
    (hm2 : ∀ z ∈ good, D.m z ≤ 2) {nrm : ℝ} (hnrm : 0 < nrm)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ nrm) {E : ℝ}
    (hE : ∑ z ∈ good, ((D.m z : ℝ) ^ 2 + rew (labOf (D.m z))) - E
      ≤ ∑ j, phiC clipC
          ((Matrix.posSemidef_conjTranspose_mul_self (goodW D good nrm)).1.eigenvalues j)) :
    2 * clipC * rtrace (D.blockP nrm + D.blockQ nrm) - frobSq (D.blockP nrm + D.blockQ nrm)
      ≤ nuC * (D.Ncount : ℝ) + muC * (Fintype.card ι : ℝ)
        + clipC ^ 2 * (#{z ∈ D.onLine \ good | D.m z ≤ 2} : ℝ) + E := by
  have hc : 0 < clipC := by unfold clipC; norm_num
  have h1 := seam_block D Pr hgood hnrm hPois hc
  have h2 := seam_count D Pr hgood hm2
  have h3 : ∑ z ∈ good, (2 * clipC * (D.m z : ℝ) - ((D.m z : ℝ) ^ 2 + rew (labOf (D.m z))))
      = 2 * clipC * ∑ z ∈ good, (D.m z : ℝ)
        - ∑ z ∈ good, ((D.m z : ℝ) ^ 2 + rew (labOf (D.m z))) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  linarith

end Block

end Distinct839.Assembly
