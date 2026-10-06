/-
Distinct839/Gram/Remainder.lean — the separated remainder block of the Gram theorem.

On a `sep`-separated set `S` the hypothesis `xᵀ κ_S x ≤ (c/2)|x|²` gives `G_S ≤ c` (as the
multiplicities are at most `2`), so no eigenvalue of the block is clipped and

    ∑ φ_c(eigenvalues of G_S) = ‖G_S‖_F² = ∑_{i,j ∈ S} m_i m_j κ_ij².

The diagonal gives `∑ m_i² κ_ii² ≥ ∑ (m_i² - 8η)`. For the off-diagonal part the set is sorted
by position and `TransferStatement` is applied with `e_ij = κ_ij²` and `ε = 3η`.
-/
import Distinct839.Gram.Basic
import Distinct839.Gram.Pinching

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Distinct839.Gram

/-! ### Eigenvalue bound from a bound for the real quadratic form -/

/-- A Hermitian complex matrix with real entries `B` whose real quadratic form is bounded by
`c |x|²` has all eigenvalues at most `c`. -/
theorem eigenvalues_le_of_real_form {τ : Type*} [Fintype τ] [DecidableEq τ] {A : Matrix τ τ ℂ}
    (hA : A.IsHermitian) {B : τ → τ → ℝ} (hAB : ∀ a b, A a b = (B a b : ℂ)) {c : ℝ}
    (hform : ∀ x : τ → ℝ, ∑ a, ∑ b, x a * B a b * x b ≤ c * ∑ a, x a ^ 2) (k : τ) :
    hA.eigenvalues k ≤ c := by
  have h1 : ‖hA.eigenvectorBasis k‖ = 1 := hA.eigenvectorBasis.orthonormal.1 k
  have h2 := EuclideanSpace.norm_eq (hA.eigenvectorBasis k)
  rw [h1] at h2
  have heig := hA.eigenvalues_eq k
  set v : τ → ℂ := ⇑(hA.eigenvectorBasis k) with hv
  -- the eigenvector has norm one
  have h3 : ∑ a, ‖v a‖ ^ 2 = 1 := Real.sqrt_eq_one.1 h2.symm
  have hnorm : ∑ a, (v a).re ^ 2 + ∑ a, (v a).im ^ 2 = 1 := by
    have h6 : ∀ a, (v a).re ^ 2 + (v a).im ^ 2 = ‖v a‖ ^ 2 := fun a => by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun a _ => h6 a, h3]
  -- the Rayleigh quotient in real and imaginary parts
  have heq : hA.eigenvalues k
      = ∑ a, ∑ b, (v a).re * B a b * (v b).re + ∑ a, ∑ b, (v a).im * B a b * (v b).im := by
    rw [heig]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, hAB, Finset.mul_sum,
      map_sum, RCLike.re_to_complex]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_im]
    ring
  have hre := hform fun a => (v a).re
  have him := hform fun a => (v a).im
  calc hA.eigenvalues k
      = ∑ a, ∑ b, (v a).re * B a b * (v b).re + ∑ a, ∑ b, (v a).im * B a b * (v b).im := heq
    _ ≤ c * ∑ a, (v a).re ^ 2 + c * ∑ a, (v a).im ^ 2 := add_le_add hre him
    _ = c := by rw [← mul_add, hnorm, mul_one]

/-! ### Sorting a finite set of reals and the transfer statement on a finite type -/

/-- A finite family of distinct reals can be enumerated increasingly. -/
lemma exists_sorting {τ : Type*} [Fintype τ] (z : τ → ℝ) (hz : Function.Injective z) :
    ∃ e : Fin (Fintype.card τ) ≃ τ, StrictMono fun i => z (e i) := by
  classical
  let _ : LinearOrder τ := LinearOrder.lift' z hz
  refine ⟨(Fintype.orderIsoFinOfCardEq τ rfl).toEquiv, fun i j hij => ?_⟩
  have h : (Fintype.orderIsoFinOfCardEq τ rfl) i < (Fintype.orderIsoFinOfCardEq τ rfl) j :=
    (Fintype.orderIsoFinOfCardEq τ rfl).strictMono hij
  exact h

/-- `TransferStatement` for a `sep`-separated family indexed by an arbitrary finite type
(the statement itself is for increasing chains indexed by `Fin ℓ`). -/
theorem transfer_fintype (htr : TransferStatement) {τ : Type*} [Fintype τ] [DecidableEq τ]
    (z : τ → ℝ) (lab : τ → Fin 2) (e : τ → τ → ℝ) (ε R : ℝ)
    (hsep : ∀ a b, a ≠ b → sep ≤ |z a - z b|) (hR : 0 ≤ R) (hspan : ∀ a b, z a - z b ≤ R)
    (hε : 0 ≤ ε) (he0 : ∀ a b, a ≠ b → 0 ≤ e a b)
    (he : ∀ a b, a ≠ b → K (z b - z a) ^ 2 - ε ≤ e a b) :
    ∑ a, rew (lab a) - spanB * R - (6 * rewY + omegaB) - 48 * ε * Fintype.card τ
      ≤ ∑ a, ∑ b, if a ≠ b then mulOf (lab a) * mulOf (lab b) * e a b else 0 := by
  have hsep0 : (0 : ℝ) < sep := by norm_num [sep]
  have hz : Function.Injective z := by
    intro a b hab
    by_contra hne
    have := hsep a b hne
    rw [hab, sub_self, abs_zero] at this
    linarith
  obtain ⟨s, hs⟩ := exists_sorting z hz
  have h := htr (Fintype.card τ) (fun i => z (s i)) (fun i => lab (s i))
    (fun i j => e (s i) (s j)) ε R
    (fun i j hij => by
      have h1 : z (s i) < z (s j) := hs hij
      have h2 := hsep (s j) (s i) (fun h => hij.ne' (s.injective h))
      rwa [abs_of_pos (by linarith)] at h2)
    hR (fun i j => hspan _ _) hε
    (fun i j hij => he0 _ _ (fun h => hij (s.injective h)))
    (fun i j hij => he _ _ (fun h => hij (s.injective h)))
  have e1 : ∑ i, rew (lab (s i)) = ∑ a, rew (lab a) :=
    Equiv.sum_comp s fun a => rew (lab a)
  have e2 : (∑ i, ∑ j, if i ≠ j then mulOf (lab (s i)) * mulOf (lab (s j)) * e (s i) (s j)
        else 0)
      = ∑ a, ∑ b, if a ≠ b then mulOf (lab a) * mulOf (lab b) * e a b else 0 := by
    rw [← Equiv.sum_comp s fun a =>
      ∑ b, if a ≠ b then mulOf (lab a) * mulOf (lab b) * e a b else 0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp s fun b =>
      if s i ≠ b then mulOf (lab (s i)) * mulOf (lab b) * e (s i) b else 0]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_pos hij, if_pos fun h => hij (s.injective h)]
  rw [e1, e2] at h
  exact h

/-! ### The remainder block -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β] [DecidableEq β]
  {y : ι → ℝ} {lab : ι → Fin 2} {κ : ι → ι → ℝ} {η : ℝ} {G : Matrix ι ι ℂ}

omit [DecidableEq ι] [Fintype β] in
/-- On a separated block the weighted matrix is bounded by `c`: the quadratic form of the
entries `√(m_a m_b) κ_ab` is at most `c |x|²`. -/
lemma block_form_le (f : ι → β) (k : β)
    (hsep : ∀ i j, f i = k → f j = k → i ≠ j → sep ≤ |y i - y j|)
    (hform : ∀ S : Finset ι, (∀ i ∈ S, ∀ j ∈ S, i ≠ j → sep ≤ |y i - y j|) →
      ∀ x : ι → ℝ, ∑ i ∈ S, ∑ j ∈ S, x i * κ i j * x j ≤ clipC / 2 * ∑ i ∈ S, x i ^ 2)
    (x : {l // f l = k} → ℝ) :
    ∑ a : {l // f l = k}, ∑ b : {l // f l = k}, x a * GramData.B lab κ a b * x b
      ≤ clipC * ∑ a, x a ^ 2 := by
  set S : Finset ι := Finset.univ.filter fun i => f i = k with hS
  have hmem : ∀ i, i ∈ S ↔ f i = k := fun i => by simp [hS]
  set x' : ι → ℝ := fun i => if h : f i = k then Real.sqrt (mulOf (lab i)) * x ⟨i, h⟩ else 0
    with hx'
  have hx'a : ∀ a : {l // f l = k}, x' a = Real.sqrt (mulOf (lab a)) * x a := fun a => by
    simp only [hx']; rw [dif_pos a.2]
  have h := hform S (fun i hi j hj hij => hsep i j ((hmem i).1 hi) ((hmem j).1 hj) hij) x'
  have hS1 : ∀ F : ι → ℝ, ∑ i ∈ S, F i = ∑ a : {l // f l = k}, F a := fun F =>
    Finset.sum_subtype S hmem F
  rw [hS1 fun i => ∑ j ∈ S, x' i * κ i j * x' j, hS1 fun i => x' i ^ 2] at h
  have hL : ∑ a : {l // f l = k}, ∑ j ∈ S, x' a * κ a j * x' j
      = ∑ a : {l // f l = k}, ∑ b : {l // f l = k}, x a * GramData.B lab κ a b * x b := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hS1 fun j => x' a * κ a j * x' j]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hx'a a, hx'a b]
    unfold GramData.B
    rw [Real.sqrt_mul (mulOf_pos _).le]
    ring
  have hRt : ∑ a : {l // f l = k}, x' a ^ 2 ≤ 2 * ∑ a, x a ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [hx'a a, mul_pow, Real.sq_sqrt (mulOf_pos _).le]
    exact mul_le_mul_of_nonneg_right (mulOf_le_two _) (sq_nonneg _)
  rw [hL] at h
  have hc : (0 : ℝ) ≤ clipC / 2 := by norm_num [clipC]
  have := mul_le_mul_of_nonneg_left hRt hc
  linarith

/-- **Remainder block.** If the block `k` of the partition `f` is `sep`-separated, the clipped
trace of the block of `G` is at least
`∑ (m_i² + rew_i - 152η) - spanB · R - (6 rewY + omegaB)`, the sum being over the block. -/
theorem remainder_block_ge (htr : TransferStatement) (D : GramData y lab κ η G)
    (hG : G.PosSemidef) (f : ι → β) (k : β)
    (hsep : ∀ i j, f i = k → f j = k → i ≠ j → sep ≤ |y i - y j|)
    (hform : ∀ S : Finset ι, (∀ i ∈ S, ∀ j ∈ S, i ≠ j → sep ≤ |y i - y j|) →
      ∀ x : ι → ℝ, ∑ i ∈ S, ∑ j ∈ S, x i * κ i j * x j ≤ clipC / 2 * ∑ i ∈ S, x i ^ 2)
    {R : ℝ} (hR : 0 ≤ R) (hspan : ∀ i j, y i - y j ≤ R) :
    ∑ a : {l // f l = k}, (mulOf (lab a) ^ 2 + rew (lab a) - 152 * η)
        - (spanB * R + (6 * rewY + omegaB))
      ≤ ∑ t, phiC clipC ((blockOf_posSemidef f hG k).1.eigenvalues t) := by
  set hA := (blockOf_posSemidef f hG k).1 with hhA
  have hη0 := D.eta_nonneg
  have hAB : ∀ a b : {l // f l = k},
      blockOf f G k a b = ((GramData.B lab κ a b : ℝ) : ℂ) := fun a b => D.entry a b
  -- no eigenvalue is clipped
  have heig : ∀ t, hA.eigenvalues t ≤ clipC :=
    eigenvalues_le_of_real_form hA hAB (block_form_le f k hsep hform)
  have hphi : ∑ t, phiC clipC (hA.eigenvalues t)
      = ∑ a : {l // f l = k}, ∑ b : {l // f l = k},
          mulOf (lab a) * mulOf (lab b) * κ a b ^ 2 := by
    rw [Finset.sum_congr rfl fun t _ => phiC_of_le (heig t),
      ← frobSq_hermitian_eq_sum_sq_eigenvalues hA, frobSq_of_real hAB]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => GramData.B_sq lab κ a b
  -- split into diagonal and off-diagonal parts
  have hsplit : ∀ a : {l // f l = k},
      ∑ b : {l // f l = k}, mulOf (lab a) * mulOf (lab b) * κ a b ^ 2
        = mulOf (lab a) ^ 2 * κ a a ^ 2
          + ∑ b : {l // f l = k},
              if a ≠ b then mulOf (lab a) * mulOf (lab b) * κ a b ^ 2 else 0 := fun a => by
    have h1 : ∀ b : {l // f l = k}, mulOf (lab a) * mulOf (lab b) * κ a b ^ 2
        = (if a = b then mulOf (lab a) * mulOf (lab b) * κ a b ^ 2 else 0)
          + (if a ≠ b then mulOf (lab a) * mulOf (lab b) * κ a b ^ 2 else 0) := fun b => by
      by_cases hab : a = b <;> simp [hab]
    rw [Finset.sum_congr rfl fun b _ => h1 b, Finset.sum_add_distrib, Finset.sum_ite_eq,
      if_pos (Finset.mem_univ a)]
    ring
  -- the off-diagonal part, by the transfer statement
  have hoff := transfer_fintype htr (fun a : {l // f l = k} => y a) (fun a => lab a)
    (fun a b => κ a b ^ 2) (3 * η) R
    (fun a b hab => hsep a b a.2 b.2 fun h => hab (Subtype.ext h)) hR
    (fun a b => hspan a b) (by linarith) (fun a b _ => sq_nonneg _)
    (fun a b _ => by
      have := D.offdiag_sq_ge b.1 a.1
      rw [D.symm b.1 a.1] at this
      exact this)
  -- the diagonal part
  have hdiag : ∑ a : {l // f l = k}, (mulOf (lab a) ^ 2 - 8 * η)
      ≤ ∑ a : {l // f l = k}, mulOf (lab a) ^ 2 * κ a a ^ 2 :=
    Finset.sum_le_sum fun a _ => D.diag_sq_ge a
  rw [hphi, Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_add_distrib]
  have hcount : ∑ a : {l // f l = k}, (mulOf (lab a) ^ 2 + rew (lab a) - 152 * η)
      = ∑ a : {l // f l = k}, (mulOf (lab a) ^ 2 - 8 * η) + ∑ a : {l // f l = k}, rew (lab a)
        - 48 * (3 * η) * Fintype.card {l // f l = k} := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hcount]
  linarith

end Distinct839.Gram
