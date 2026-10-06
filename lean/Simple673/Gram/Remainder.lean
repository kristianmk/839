/-
Simple673/Gram/Remainder.lean — the separated remainder block of the Gram theorem at clipping
level 2.

On a `sep`-separated set `S` the hypothesis `xᵀ κ_S x ≤ normS |x|²` with `normS = 19/10 ≤ 2`
gives `G_S ≤ c = 2`, so no eigenvalue of the block is clipped and

    ∑ φ_c(eigenvalues of G_S) = ‖G_S‖_F² = ∑_{i,j ∈ S} κ_ij².

This is where the bound on separated sets has to be below `2`. The diagonal gives
`∑ κ_ii² ≥ (1 - 2η)|S|`. For the off-diagonal part the set is sorted by position and
`TransferStatement` is applied with `e_ij = κ_ij²` and `ε = 3η`.

The eigenvalue bound from a bound for the real quadratic form and the sorting of a finite set of
reals do not depend on the window; they are `Distinct839.Gram.eigenvalues_le_of_real_form` and
`Distinct839.Gram.exists_sorting`.
-/
import Simple673.Gram.Basic
import Distinct839.Gram.Pinching
import Distinct839.Gram.Remainder

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Simple673.Gram

/-! ### The transfer statement on a finite type -/

/-- `TransferStatement` for a `sep`-separated family indexed by an arbitrary finite type
(the statement itself is for increasing chains indexed by `Fin ℓ`). -/
theorem transfer_fintype (htr : TransferStatement) {τ : Type*} [Fintype τ] [DecidableEq τ]
    (z : τ → ℝ) (e : τ → τ → ℝ) (ε R : ℝ)
    (hsep : ∀ a b, a ≠ b → sep ≤ |z a - z b|) (hR : 0 ≤ R) (hspan : ∀ a b, z a - z b ≤ R)
    (hε : 0 ≤ ε) (he0 : ∀ a b, a ≠ b → 0 ≤ e a b)
    (he : ∀ a b, a ≠ b → K (z b - z a) ^ 2 - ε ≤ e a b) :
    rewX * Fintype.card τ - spanB * R - (7 * rewX + omegaB) - 14 * ε * Fintype.card τ
      ≤ ∑ a, ∑ b, if a ≠ b then e a b else 0 := by
  have hsep0 : (0 : ℝ) < sep := by unfold sep; norm_num
  have hz : Function.Injective z := by
    intro a b hab
    by_contra hne
    have := hsep a b hne
    rw [hab, sub_self, abs_zero] at this
    linarith
  obtain ⟨s, hs⟩ := Distinct839.Gram.exists_sorting z hz
  have h := htr (Fintype.card τ) (fun i => z (s i)) (fun i j => e (s i) (s j)) ε R
    (fun i j hij => by
      have h1 : z (s i) < z (s j) := hs hij
      have h2 := hsep (s j) (s i) (fun h => hij.ne' (s.injective h))
      rwa [abs_of_pos (by linarith)] at h2)
    hR (fun i j => hspan _ _) hε
    (fun i j hij => he0 _ _ (fun h => hij (s.injective h)))
    (fun i j hij => he _ _ (fun h => hij (s.injective h)))
  have e2 : (∑ i, ∑ j, if i ≠ j then e (s i) (s j) else 0)
      = ∑ a, ∑ b, if a ≠ b then e a b else 0 := by
    rw [← Equiv.sum_comp s fun a => ∑ b, if a ≠ b then e a b else 0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp s fun b => if s i ≠ b then e (s i) b else 0]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_pos hij, if_pos fun h => hij (s.injective h)]
  rw [e2] at h
  exact h

/-! ### The remainder block -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β] [DecidableEq β]
  {y : ι → ℝ} {κ : ι → ι → ℝ} {η : ℝ} {G : Matrix ι ι ℂ}

omit [DecidableEq ι] [Fintype β] in
/-- On a separated block the matrix is bounded by `normS`: the quadratic form of the entries
`κ_ab` is at most `normS |x|²`. -/
lemma block_form_le (f : ι → β) (k : β)
    (hsep : ∀ i j, f i = k → f j = k → i ≠ j → sep ≤ |y i - y j|)
    (hform : ∀ S : Finset ι, (∀ i ∈ S, ∀ j ∈ S, i ≠ j → sep ≤ |y i - y j|) →
      ∀ x : ι → ℝ, ∑ i ∈ S, ∑ j ∈ S, x i * κ i j * x j ≤ normS * ∑ i ∈ S, x i ^ 2)
    (x : {l // f l = k} → ℝ) :
    ∑ a : {l // f l = k}, ∑ b : {l // f l = k}, x a * κ a b * x b
      ≤ normS * ∑ a, x a ^ 2 := by
  set S : Finset ι := Finset.univ.filter fun i => f i = k with hS
  have hmem : ∀ i, i ∈ S ↔ f i = k := fun i => by simp [hS]
  set x' : ι → ℝ := fun i => if h : f i = k then x ⟨i, h⟩ else 0 with hx'
  have hx'a : ∀ a : {l // f l = k}, x' a = x a := fun a => by
    simp only [hx']; rw [dif_pos a.2]
  have h := hform S (fun i hi j hj hij => hsep i j ((hmem i).1 hi) ((hmem j).1 hj) hij) x'
  have hS1 : ∀ F : ι → ℝ, ∑ i ∈ S, F i = ∑ a : {l // f l = k}, F a := fun F =>
    Finset.sum_subtype S hmem F
  rw [hS1 fun i => ∑ j ∈ S, x' i * κ i j * x' j, hS1 fun i => x' i ^ 2] at h
  have hL : ∑ a : {l // f l = k}, ∑ j ∈ S, x' a * κ a j * x' j
      = ∑ a : {l // f l = k}, ∑ b : {l // f l = k}, x a * κ a b * x b := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hS1 fun j => x' a * κ a j * x' j]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hx'a a, hx'a b]
  have hRt : ∑ a : {l // f l = k}, x' a ^ 2 = ∑ a, x a ^ 2 :=
    Finset.sum_congr rfl fun a _ => by rw [hx'a a]
  rw [hL, hRt] at h
  exact h

/-- The bound on separated sets is below the clipping level: `normS ≤ c`. -/
lemma normS_le_clipC : normS ≤ clipC := by unfold normS clipC; norm_num

/-- **Remainder block.** If the block `k` of the partition `f` is `sep`-separated, the clipped
trace of the block of `G` is at least
`∑ (1 + x₁ - 44η) - spanB · R - (7 x₁ + omegaB)`, the sum being over the block. -/
theorem remainder_block_ge (htr : TransferStatement) (D : GramData y κ η G)
    (hG : G.PosSemidef) (f : ι → β) (k : β)
    (hsep : ∀ i j, f i = k → f j = k → i ≠ j → sep ≤ |y i - y j|)
    (hform : ∀ S : Finset ι, (∀ i ∈ S, ∀ j ∈ S, i ≠ j → sep ≤ |y i - y j|) →
      ∀ x : ι → ℝ, ∑ i ∈ S, ∑ j ∈ S, x i * κ i j * x j ≤ normS * ∑ i ∈ S, x i ^ 2)
    {R : ℝ} (hR : 0 ≤ R) (hspan : ∀ i j, y i - y j ≤ R) :
    ∑ _a : {l // f l = k}, (1 + rewX - 44 * η) - (spanB * R + (7 * rewX + omegaB))
      ≤ ∑ t, phiC clipC ((Distinct839.Gram.blockOf_posSemidef f hG k).1.eigenvalues t) := by
  set hA := (Distinct839.Gram.blockOf_posSemidef f hG k).1 with hhA
  have hη0 := D.eta_nonneg
  have hAB : ∀ a b : {l // f l = k},
      Distinct839.Gram.blockOf f G k a b = ((κ a b : ℝ) : ℂ) := fun a b => D.entry a b
  -- no eigenvalue is clipped
  have heig : ∀ t, hA.eigenvalues t ≤ clipC := fun t =>
    (Distinct839.Gram.eigenvalues_le_of_real_form hA
      (B := fun a b : {l // f l = k} => κ a b) hAB
      (block_form_le f k hsep hform) t).trans normS_le_clipC
  have hphi : ∑ t, phiC clipC (hA.eigenvalues t)
      = ∑ a : {l // f l = k}, ∑ b : {l // f l = k}, κ a b ^ 2 := by
    rw [Finset.sum_congr rfl fun t _ => Distinct839.Gram.phiC_of_le (heig t),
      ← frobSq_hermitian_eq_sum_sq_eigenvalues hA,
      Distinct839.Gram.frobSq_of_real (B := fun a b : {l // f l = k} => κ a b) hAB]
  -- split into diagonal and off-diagonal parts
  have hsplit : ∀ a : {l // f l = k},
      ∑ b : {l // f l = k}, κ a b ^ 2
        = κ a a ^ 2 + ∑ b : {l // f l = k}, if a ≠ b then κ a b ^ 2 else 0 := fun a => by
    have h1 : ∀ b : {l // f l = k}, κ a b ^ 2
        = (if a = b then κ a b ^ 2 else 0) + (if a ≠ b then κ a b ^ 2 else 0) := fun b => by
      by_cases hab : a = b <;> simp [hab]
    rw [Finset.sum_congr rfl fun b _ => h1 b, Finset.sum_add_distrib, Finset.sum_ite_eq,
      if_pos (Finset.mem_univ a)]
  -- the off-diagonal part, by the transfer statement
  have hoff := transfer_fintype htr (fun a : {l // f l = k} => y a)
    (fun a b => κ a b ^ 2) (3 * η) R
    (fun a b hab => hsep a b a.2 b.2 fun h => hab (Subtype.ext h)) hR
    (fun a b => hspan a b) (by linarith) (fun a b _ => sq_nonneg _)
    (fun a b _ => by
      have := D.offdiag_sq_ge b.1 a.1
      rw [D.symm b.1 a.1] at this
      exact this)
  -- the diagonal part
  have hdiag : ∑ _a : {l // f l = k}, (1 - 2 * η)
      ≤ ∑ a : {l // f l = k}, κ a a ^ 2 :=
    Finset.sum_le_sum fun a _ => D.diag_sq_ge a
  rw [hphi, Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_add_distrib]
  have hcount : ∑ _a : {l // f l = k}, (1 + rewX - 44 * η)
      = ∑ _a : {l // f l = k}, (1 - 2 * η) + rewX * Fintype.card {l // f l = k}
        - 14 * (3 * η) * Fintype.card {l // f l = k} := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hcount]
  linarith

end Simple673.Gram
