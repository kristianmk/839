/-
Further/Counting.lean — the new counts for an abstract zero configuration.

Three counts of a zero configuration `Z` on a window `(T₁, T₂]` enter the two theorems:

* `Z.Ns`  — the simple zeros (defined in `Zeta23/Defs.lean`);
* `Z.N0`  — the zeros on the critical line, with multiplicity (`Zeta23/Defs.lean`);
* `NsL Z` — the zeros that are simple or on the line, with multiplicity (defined here).

This file proves, for each of them, interval additivity, the bound by `Z.N`, and the comparison of
the count over `I' = (T − √T, 2T + √T]` with the count over `(T, 2T]` (the difference is at most
`NII`, the number of zeros in `I' \ (T, 2T]`).

For the abstract block data `ZeroBlockData ι d` the corresponding counts are `simpleCard D` (the
number of indices of multiplicity one), `D.Non` (the sum of the multiplicities of the on-line
indices, `Zeta23/ZeroSide.lean`) and `simpleOrLineSum D` (the sum of the multiplicities of the
indices that are simple or on the line). For the block data of the zeros with ordinate in `I'`
they are the counts of `Z` over `I'` (`Ns_Iprime_eq_mk`, `NsL_Iprime_eq_mk`; for `D.Non` this is
the library's `NonIprime_eq_mk`).

The last section identifies the three counts of the zeros of the Riemann zeta function with
`Nsimple`, `N0mult` and `NsimpleOrLine`.
-/
import Zeta23.Assembly
import Zeta23.ZeroSide
import Zeta23.Statement.SeamClosed
import Further.Defs

noncomputable section
set_option linter.unusedSectionVars false

open Finset Set
open scoped BigOperators

namespace Further

open Zeta23 Zeta23.Assembly Zeta23.ZeroSide

/-! ### The count of zeros that are simple or on the line -/

/-- `N_{s∨0}(T₁,T₂)` for an abstract zero configuration: the points of the window that are simple
or on the line, counted with multiplicity. -/
def NsL (Z : ZeroConfig) (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ Z.window T₁ T₂ ∩ (Z.simple ∪ ZeroConfig.onLine), Z.mult ρ

section Windows

variable (Z : ZeroConfig)

/-! ### Interval additivity -/

/-- Interval additivity of a sum of multiplicities over the part of a window in a set `S`. -/
lemma finsum_window_inter_add (S : Set ℂ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    ∑ᶠ ρ ∈ Z.window a c ∩ S, Z.mult ρ
      = ∑ᶠ ρ ∈ Z.window a b ∩ S, Z.mult ρ + ∑ᶠ ρ ∈ Z.window b c ∩ S, Z.mult ρ := by
  rw [window_union Z hab hbc, Set.union_inter_distrib_right,
    finsum_mem_union ((window_disjoint Z a b c).mono inter_subset_left inter_subset_left)
      ((Z.window_finite a b).subset inter_subset_left)
      ((Z.window_finite b c).subset inter_subset_left)]

/-- Interval additivity of `N₀` (on the line, with multiplicity). -/
theorem N0_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) : Z.N0 a c = Z.N0 a b + Z.N0 b c :=
  finsum_window_inter_add Z _ hab hbc

/-- Interval additivity of `N_{s∨0}`. -/
theorem NsL_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) : NsL Z a c = NsL Z a b + NsL Z b c :=
  finsum_window_inter_add Z _ hab hbc

/-- Interval additivity of `N_s` (simple zeros). -/
theorem Ns_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) : Z.Ns a c = Z.Ns a b + Z.Ns b c := by
  unfold ZeroConfig.Ns
  rw [window_union Z hab hbc, Set.union_inter_distrib_right,
    Set.ncard_union_eq ((window_disjoint Z a b c).mono inter_subset_left inter_subset_left)
      ((Z.window_finite a b).subset inter_subset_left)
      ((Z.window_finite b c).subset inter_subset_left)]

/-! ### Bounds by the count with multiplicity -/

lemma Ns_le_N (a b : ℝ) : Z.Ns a b ≤ Z.N a b :=
  (Z.trivial_chain a b).2.2.2.2.1.trans (Z.trivial_chain a b).2.2.2.2.2

lemma N0_le_N (a b : ℝ) : Z.N0 a b ≤ Z.N a b := (Z.trivial_chain a b).2.2.1

lemma NsL_le_N (a b : ℝ) : NsL Z a b ≤ Z.N a b :=
  Z.finsum_mult_mono a b inter_subset_left subset_rfl

/-! ### The window `I'` against the window `(T, 2T]` -/

variable {T : ℝ}

/-- `N_s(I') ≤ N_s(T, 2T) + N(I' \ I)`. -/
theorem Ns_Iprime_le (hT : 0 ≤ T) :
    Z.Ns (T - D0 T) (2 * T + D0 T) ≤ Z.Ns T (2 * T) + NII Z T := by
  have h0 := D0_nonneg T
  rw [Ns_add Z (b := T) (by linarith) (by linarith),
    Ns_add Z (a := T) (b := 2 * T) (by linarith) (by linarith)]
  unfold NII
  have h1 := Ns_le_N Z (T - D0 T) T
  have h2 := Ns_le_N Z (2 * T) (2 * T + D0 T)
  omega

/-- `N₀(I') ≤ N₀(T, 2T) + N(I' \ I)`. -/
theorem N0_Iprime_le (hT : 0 ≤ T) :
    Z.N0 (T - D0 T) (2 * T + D0 T) ≤ Z.N0 T (2 * T) + NII Z T := by
  have h0 := D0_nonneg T
  rw [N0_add Z (b := T) (by linarith) (by linarith),
    N0_add Z (a := T) (b := 2 * T) (by linarith) (by linarith)]
  unfold NII
  have h1 := N0_le_N Z (T - D0 T) T
  have h2 := N0_le_N Z (2 * T) (2 * T + D0 T)
  omega

/-- `N_{s∨0}(I') ≤ N_{s∨0}(T, 2T) + N(I' \ I)`. -/
theorem NsL_Iprime_le (hT : 0 ≤ T) :
    NsL Z (T - D0 T) (2 * T + D0 T) ≤ NsL Z T (2 * T) + NII Z T := by
  have h0 := D0_nonneg T
  rw [NsL_add Z (b := T) (by linarith) (by linarith),
    NsL_add Z (a := T) (b := 2 * T) (by linarith) (by linarith)]
  unfold NII
  have h1 := NsL_le_N Z (T - D0 T) T
  have h2 := NsL_le_N Z (2 * T) (2 * T + D0 T)
  omega

/-- `N₀ˢ(T, 2T) ≤ s₁(I')`: the simple zeros on the line in `(T, 2T]` are among those in `I'`. -/
theorem N0s_le_s1 (hT : 0 ≤ T) : Z.N0s T (2 * T) ≤ Z.s1 T := by
  have hs1 : Z.s1 T = Z.N0s (T - D0 T) (2 * T + D0 T) := rfl
  have h0 := D0_nonneg T
  have h1 : Z.N0s (T - D0 T) (2 * T + D0 T)
      = Z.N0s (T - D0 T) T + (Z.N0s T (2 * T) + Z.N0s (2 * T) (2 * T + D0 T)) := by
    rw [N0s_add Z (a := T - D0 T) (b := T) (c := 2 * T + D0 T) (by linarith) (by linarith),
      N0s_add Z (a := T) (b := 2 * T) (c := 2 * T + D0 T) (by linarith) (by linarith)]
  omega

end Windows

/-! ### The same counts for the abstract block data -/

section BlockCounts

variable {ι d : Type*}

/-- The number of indices of multiplicity one (on the line or not). -/
def simpleCard [Fintype ι] (D : ZeroBlockData ι d) : ℕ := #{z | D.m z = 1}

/-- The sum of the multiplicities over the indices that are simple or on the line (fixed by the
reflection). -/
def simpleOrLineSum [Fintype ι] [DecidableEq ι] (D : ZeroBlockData ι d) : ℕ :=
  ∑ z with D.m z = 1 ∨ D.σ z = z, D.m z

end BlockCounts

/-! ### The counts over `I'` as sums over the index type of the block data -/

section Index

open Classical

variable (Z : ZeroConfig) (T : ℝ)

/-- The part of `𝒵(I')` in a set `S`, as the image of a filter of the index type. -/
lemma ZIprime_inter_eq (S : Set ℂ) (q : ZI Z T → Prop) [DecidablePred q]
    (h : ∀ z : ZI Z T, q z ↔ (z : ℂ) ∈ S) :
    Z.ZIprime T ∩ S
      = ↑((Finset.univ.filter q).map (Function.Embedding.subtype (· ∈ ZI Z T))) := by
  ext ρ
  simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image, Finset.mem_coe,
    Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨ρ, (mem_ZI Z T).mpr h1⟩, (h _).mpr h2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(mem_ZI Z T).mp z.2, (h z).mp hz⟩

/-- Number of points of `𝒵(I')` in a set `S`. -/
lemma ncard_ZIprime_inter (S : Set ℂ) (q : ZI Z T → Prop) [DecidablePred q]
    (h : ∀ z : ZI Z T, q z ↔ (z : ℂ) ∈ S) :
    (Z.ZIprime T ∩ S).ncard = #(Finset.univ.filter q) := by
  rw [ZIprime_inter_eq Z T S q h, Set.ncard_coe_finset, Finset.card_map]

/-- Sum over the points of `𝒵(I')` in a set `S`. -/
lemma finsum_ZIprime_inter (S : Set ℂ) (q : ZI Z T → Prop) [DecidablePred q]
    (h : ∀ z : ZI Z T, q z ↔ (z : ℂ) ∈ S) (f : ℂ → ℕ) :
    ∑ᶠ ρ ∈ Z.ZIprime T ∩ S, f ρ = ∑ z ∈ Finset.univ.filter q, f z := by
  rw [ZIprime_inter_eq Z T S q h, finsum_mem_coe_finset, Finset.sum_map]
  rfl

variable {d : Type*} [Fintype d] [DecidableEq d] (v : ZI Z T → d → ℂ)
  (hv : ∀ z : ZI Z T, v ⟨reflect z, reflect_mem_ZI Z T z.2⟩ = star (v z))

/-- `N_s(I')` is the number of indices of multiplicity one. -/
theorem Ns_Iprime_eq_mk :
    Z.Ns (T - D0 T) (2 * T + D0 T) = simpleCard (mkData Z T v hv) :=
  ncard_ZIprime_inter Z T Z.simple (fun z => (mkData Z T v hv).m z = 1) fun _ => Iff.rfl

/-- `N_{s∨0}(I')` is the sum of the multiplicities over the indices that are simple or fixed by
the reflection. -/
theorem NsL_Iprime_eq_mk :
    NsL Z (T - D0 T) (2 * T + D0 T) = simpleOrLineSum (mkData Z T v hv) :=
  finsum_ZIprime_inter Z T (Z.simple ∪ ZeroConfig.onLine)
    (fun z => (mkData Z T v hv).m z = 1 ∨ (mkData Z T v hv).σ z = z)
    (fun z => by
      rw [mkData_σ_eq_iff]
      exact Iff.rfl) Z.mult

end Index

/-! ### The zeros of the Riemann zeta function -/

section Zeta

variable (T₁ T₂ : ℝ)

@[simp] lemma zetaZeroConfig_Ns : zetaZeroConfig.Ns T₁ T₂ = Nsimple T₁ T₂ :=
  zetaZeros_Ns _ _ _

@[simp] lemma zetaZeroConfig_N0 : zetaZeroConfig.N0 T₁ T₂ = N0mult T₁ T₂ :=
  zetaZeros_N0 _ _ _

@[simp] lemma zetaZeroConfig_NsL : NsL zetaZeroConfig T₁ T₂ = NsimpleOrLine T₁ T₂ := by
  simp [NsL, NsimpleOrLine, zetaZeroConfig, zetaZeros_window, ZeroConfig.onLine]

end Zeta

end Further
