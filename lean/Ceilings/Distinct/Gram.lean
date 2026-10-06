/-
Ceilings/Distinct/Gram.lean — certificates in the sense of the Gram bound are pair-energy
certificates.

In the paper a certificate is a triple `(x₁, x₂, b)` for which the finite Gram theorem holds: for
a labelled configuration with positive semidefinite weighted Gram matrix
`G = (√(m_i m_j) K(y_i - y_j))`, bounded by `c/2` on separated subsets,

    `∑ (m_i² + x_{d_i}) - b R - C₃ ≤ tr φ_c(G)`,      `φ_c(t) = t² - (t - c)₊²`.

This is `Distinct839.GramEnergyStatement` with the error `η = 0` and constants `(x₁, x₂, b, C₃)`
in place of the paper's; `GramCert x₁ x₂ b` states it, and `gramCert_of_statement` shows that the
statement proved in `Distinct839` gives `GramCert rewX rewY spanB`.

Since `φ_c(t) ≤ t²`, the trace of `φ_c(G)` is at most the sum of the squares of the eigenvalues,
which is the sum of the squares of the entries (`sum_phiC_le_energy`):

    `tr φ_c(G) ≤ ∑ m_i² + ∑_{i ≠ j} m_i m_j K(y_j - y_i)²`.

Hence a Gram certificate is a pair-energy certificate for all pairs, as soon as the two
hypotheses of the Gram bound hold for every separated chain (`GramCert.toPairCertAll_of`). They
do: the kernel matrix is positive semidefinite because `K` is the cosine transform of the
positive window, and it is bounded by `L ≤ c/2` on separated sets by the majorant of
`Distinct839/Majorant/`. This is proved in `Ceilings/Distinct/GramBridge.lean`.
-/
import Ceilings.Distinct.Defs
import Distinct839.Gram.Basic
import Distinct839.Kernel.Basic
import Distinct839.Spec

open Matrix Finset
open scoped ComplexOrder BigOperators

noncomputable section

namespace Ceilings

open Distinct839 (K sep mulOf phiC clipC)

/-- The clipped square is at most the square. -/
theorem phiC_le_sq (c t : ℝ) : phiC c t ≤ t ^ 2 := by
  unfold Distinct839.phiC
  nlinarith [sq_nonneg (max (t - c) 0)]

/-- For a Hermitian matrix with real entries `B`, `tr φ_c(G) ≤ ∑ B_ij²`. -/
theorem sum_phiC_le_sum_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ}
    (hG : G.IsHermitian) {B : ι → ι → ℝ} (hB : ∀ i j, G i j = (B i j : ℂ)) (c : ℝ) :
    ∑ k, phiC c (hG.eigenvalues k) ≤ ∑ i, ∑ j, B i j ^ 2 := by
  rw [← Distinct839.Gram.frobSq_of_real hB, RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues hG]
  exact sum_le_sum fun k _ => phiC_le_sq c _

/-- **The trace of `φ_c` of the weighted kernel matrix is at most the diagonal plus the pair
energy.** -/
theorem sum_phiC_le_energy {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι → ℝ)
    (lab : ι → Fin 2) {G : Matrix ι ι ℂ} (hG : G.IsHermitian)
    (hentry : ∀ i j, G i j
      = ((Real.sqrt (mulOf (lab i) * mulOf (lab j)) * K (y i - y j) : ℝ) : ℂ)) (c : ℝ) :
    ∑ k, phiC c (hG.eigenvalues k)
      ≤ ∑ i, mulOf (lab i) ^ 2
        + ∑ i, ∑ j, if i ≠ j then mulOf (lab i) * mulOf (lab j) * K (y j - y i) ^ 2 else 0 := by
  refine (sum_phiC_le_sum_sq hG hentry c).trans (le_of_eq ?_)
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  have hsq : ∀ j, (Real.sqrt (mulOf (lab i) * mulOf (lab j)) * K (y i - y j)) ^ 2
      = mulOf (lab i) * mulOf (lab j) * K (y j - y i) ^ 2 := by
    intro j
    have hK : K (y i - y j) = K (y j - y i) := by
      rw [← Distinct839.K_neg (y j - y i)]
      congr 1
      ring
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (mulOf_nonneg _) (mulOf_nonneg _)), hK]
  have hsplit : ∀ j, (Real.sqrt (mulOf (lab i) * mulOf (lab j)) * K (y i - y j)) ^ 2
      = (if i = j then mulOf (lab i) ^ 2 else 0)
        + (if i ≠ j then mulOf (lab i) * mulOf (lab j) * K (y j - y i) ^ 2 else 0) := by
    intro j
    rw [hsq]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, if_neg (not_not.mpr rfl), sub_self, Distinct839.K_zero]
      ring
    · rw [if_neg h, if_pos h, zero_add]
  rw [sum_congr rfl fun j _ => hsplit j, sum_add_distrib, sum_ite_eq, if_pos (mem_univ i)]

/-- **Certificate in the sense of the Gram bound**: the statement of
`Distinct839.GramEnergyStatement` with `η = 0` (so that the matrix `κ` is the kernel matrix) and
the constants `(x₁, x₂, b)` and some `C₃`. -/
def GramCert (x₁ x₂ b : ℝ) : Prop :=
  ∃ C₃ : ℝ, ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (y : ι → ℝ) (lab : ι → Fin 2) (R : ℝ)
      (G : Matrix ι ι ℂ) (hG : G.PosSemidef),
      Function.Injective y →
      (∀ S : Finset ι, (∀ i ∈ S, ∀ j ∈ S, i ≠ j → sep ≤ |y i - y j|) →
        ∀ x : ι → ℝ, ∑ i ∈ S, ∑ j ∈ S, x i * K (y i - y j) * x j
          ≤ clipC / 2 * ∑ i ∈ S, x i ^ 2) →
      0 ≤ R → (∀ i j, y i - y j ≤ R) →
      (∀ i j, G i j = ((Real.sqrt (mulOf (lab i) * mulOf (lab j)) * K (y i - y j) : ℝ) : ℂ)) →
      ∑ i, (mulOf (lab i) ^ 2 + (if lab i = 0 then x₁ else x₂)) - b * R - C₃
        ≤ ∑ k, phiC clipC (hG.1.eigenvalues k)

/-- The finite Gram theorem of `Distinct839` says that the triple of the paper is a certificate
in the sense of the Gram bound. -/
theorem gramCert_of_statement (h : Distinct839.GramEnergyStatement) :
    GramCert Distinct839.rewX Distinct839.rewY Distinct839.spanB := by
  obtain ⟨C, η₀, _, hη₀, hC⟩ := h
  refine ⟨6 * Distinct839.rewY + Distinct839.omegaB,
    fun ι _ _ y lab R G hG hinj hform hR hspan hentry => ?_⟩
  have key := hC ι y lab (fun i j => K (y i - y j)) 0 R G hG hinj le_rfl hη₀.le
    (fun i j => by
      rw [← Distinct839.K_neg (y j - y i)]
      congr 1
      ring)
    (fun i j => by simp) hform hR hspan hentry
  simpa [Distinct839.rew] using key

/-- **A Gram certificate is a pair-energy certificate**, given the two hypotheses of the Gram
bound for separated chains: the weighted kernel matrix is positive semidefinite (`hpsd`) and the
kernel matrix is bounded by `c/2` on separated sets (`hform`). Both are proved in
`Ceilings/Distinct/GramBridge.lean`. -/
theorem GramCert.toPairCertAll_of
    (hpsd : ∀ (ℓ : ℕ) (y : Fin ℓ → ℝ) (lab : Fin ℓ → Fin 2),
      (Matrix.of fun i j : Fin ℓ =>
        ((Real.sqrt (mulOf (lab i) * mulOf (lab j)) * K (y i - y j) : ℝ) : ℂ)).PosSemidef)
    (hform : ∀ (ℓ : ℕ) (y : Fin ℓ → ℝ), (∀ i j, i < j → sep ≤ y j - y i) →
      ∀ (S : Finset (Fin ℓ)) (x : Fin ℓ → ℝ),
        ∑ i ∈ S, ∑ j ∈ S, x i * K (y i - y j) * x j ≤ clipC / 2 * ∑ i ∈ S, x i ^ 2)
    {x₁ x₂ b : ℝ} (h : GramCert x₁ x₂ b) : PairCertAll x₁ x₂ b := by
  obtain ⟨C₃, hC⟩ := h
  refine ⟨C₃, fun ℓ y lab R hsep hR0 hR => ?_⟩
  have hsep0 : (0 : ℝ) < sep := by norm_num [Distinct839.sep]
  have hmono : StrictMono y := fun i j hij => by linarith [hsep i j hij]
  have key := hC (Fin ℓ) y lab R _ (hpsd ℓ y lab) hmono.injective
    (fun S _ x => hform ℓ y hsep S x) hR0 (fun i j => hR j i) (fun _ _ => rfl)
  have hle := sum_phiC_le_energy y lab (hpsd ℓ y lab).1 (fun _ _ => rfl) clipC
  rw [sum_add_distrib] at key
  linarith

end Ceilings
