/-
Distinct839/ZeroKernel/Leak.lean — the truncated Poisson sum against the full one.

The Poisson identity `∑_{k ∈ ℤ} φ̂(γ - τ_k) φ̂(γ' - τ_k) = L Φ(γ - γ')` (upstream
`AdmWindow.hasSum_vHatR_mul`) concerns all grid points `τ_k = T + k h`, `h = 2π/L`; the Gram entry
only contains `0 ≤ k < d`. For ordinates `γ, γ'` at distance at least `R ≥ h` from both ends of
the grid, an omitted grid point `τ_k` has `|γ - τ_k| ≥ max(R, m h)`, where `m ≥ 1` counts the grid
steps beyond the end. With the decay `|φ̂(x)| x² ≤ c/w` of the window class each omitted term is
at most `(c/w)² / (R h m)²`, and

  `|L Φ(γ - γ') - ∑_{0 ≤ k < d} φ̂(γ - τ_k) φ̂(γ' - τ_k)| ≤ 2 Z (c/w)² / (R h)²`,

`Z = ∑_{k ∈ ℤ} 1/k²` (`abs_poisson_sub_sum_le`).
-/
import Distinct839.ZeroKernel.Window

open scoped BigOperators
open Real Filter Topology MeasureTheory Zeta23

noncomputable section

namespace Distinct839.ZeroKernel

/-! ## The constant `∑_{k ∈ ℤ} 1/k²` -/

/-- `∑_{k ∈ ℤ} 1/k²` (the term `k = 0` is `0` by the convention `1/0 = 0`). Its value `π²/3`
is not needed. -/
def zetaTwoZ : ℝ := ∑' k : ℤ, 1 / (k : ℝ) ^ 2

lemma summable_one_div_int_sq : Summable (fun k : ℤ => 1 / (k : ℝ) ^ 2) :=
  Real.summable_one_div_int_pow.mpr (by norm_num)

lemma zetaTwoZ_nonneg : 0 ≤ zetaTwoZ :=
  tsum_nonneg fun k => by positivity

lemma hasSum_one_div_int_sq : HasSum (fun k : ℤ => 1 / (k : ℝ) ^ 2) zetaTwoZ :=
  summable_one_div_int_sq.hasSum

/-- The shifted series has the same sum. -/
lemma hasSum_one_div_int_sq_shift (d : ℕ) :
    HasSum (fun k : ℤ => 1 / ((k : ℝ) - d + 1) ^ 2) zetaTwoZ := by
  have e : (fun k : ℤ => 1 / ((k : ℝ) - d + 1) ^ 2)
      = (fun k : ℤ => 1 / (k : ℝ) ^ 2) ∘ (Equiv.addRight ((1 : ℤ) - (d : ℤ))) := by
    funext k
    have hc : ((k + ((1 : ℤ) - (d : ℤ)) : ℤ) : ℝ) = (k : ℝ) - d + 1 := by
      push_cast
      ring
    simp only [Function.comp_apply, Equiv.coe_addRight]
    rw [hc]
  rw [e]
  exact (Equiv.hasSum_iff _).mpr hasSum_one_div_int_sq

/-! ## Truncation of a sum over `ℤ` to `0 ≤ k < d` -/

/-- If `f` is summable over `ℤ` with sum `S` and is dominated outside `0 ≤ k < d` by a
nonnegative summable `g` with sum `G`, the partial sum over `0 ≤ k < d` is within `G` of `S`. -/
theorem abs_hasSum_sub_sum_range_le {f g : ℤ → ℝ} {S G : ℝ} {d : ℕ}
    (hsum : HasSum f S) (hg : HasSum g G) (hg0 : ∀ k, 0 ≤ g k)
    (hfg : ∀ k : ℤ, k < 0 ∨ (d : ℤ) ≤ k → |f k| ≤ g k) :
    |S - ∑ k : Fin d, f (((k : ℕ) : ℤ))| ≤ G := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Finset ℤ, s = (Finset.range d).map Nat.castEmbedding := ⟨_, rfl⟩
  have hmem : ∀ k : ℤ, k ∉ s → k < 0 ∨ (d : ℤ) ≤ k := by
    intro k hk
    by_contra hcon
    rw [not_or, not_lt, not_le] at hcon
    apply hk
    rw [hs, Finset.mem_map]
    refine ⟨k.toNat, Finset.mem_range.mpr (by omega), ?_⟩
    simp [Int.toNat_of_nonneg hcon.1]
  have hfin : ∑ k : Fin d, f (((k : ℕ) : ℤ)) = ∑ k ∈ s, f k := by
    rw [hs, Finset.sum_map]
    exact Fin.sum_univ_eq_sum_range (fun n : ℕ => f (n : ℤ)) d
  -- the kept part and the omitted part as sums over all of `ℤ`
  have hin : HasSum (fun k : ℤ => if k ∈ s then f k else 0) (∑ k ∈ s, f k) := by
    have h1 : HasSum (fun k : ℤ => if k ∈ s then f k else 0)
        (∑ k ∈ s, (if k ∈ s then f k else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun k hk => if_neg hk)
    have h2 : ∑ k ∈ s, (if k ∈ s then f k else 0) = ∑ k ∈ s, f k :=
      Finset.sum_congr rfl fun k hk => if_pos hk
    rwa [h2] at h1
  have hout : HasSum (fun k : ℤ => if k ∈ s then 0 else f k) (S - ∑ k ∈ s, f k) := by
    have h1 : HasSum (fun k : ℤ => f k - (if k ∈ s then f k else 0)) (S - ∑ k ∈ s, f k) :=
      hsum.sub hin
    have h2 : (fun k : ℤ => f k - (if k ∈ s then f k else 0))
        = fun k : ℤ => if k ∈ s then 0 else f k := by
      funext k
      by_cases hk : k ∈ s <;> simp [hk]
    rwa [h2] at h1
  have hbound : ‖S - ∑ k ∈ s, f k‖ ≤ G := by
    refine hout.norm_le_of_bounded hg fun k => ?_
    by_cases hk : k ∈ s
    · rw [if_pos hk, norm_zero]
      exact hg0 k
    · rw [if_neg hk, Real.norm_eq_abs]
      exact hfg k (hmem k hk)
  rw [Real.norm_eq_abs] at hbound
  rw [hfin]
  exact hbound

/-! ## The two-point lattice sum -/

/-- Truncation of a two-point lattice sum. `F` decays like `C / x²` in the form
`|F x| ≤ C / (A B)` whenever `|x| ≥ A, B > 0`; the lattice is `T + k h`, `k ∈ ℤ`, and the kept
range is `0 ≤ k < d`. If `γ, γ'` are at distance `≥ R ≥ h` from both ends of the kept range, the
omitted part of the sum is at most `2 Z (C / (R h))²`. -/
theorem abs_hasSum_sub_sum_le {F : ℝ → ℝ} {S T h R C γ γ' : ℝ} {d : ℕ}
    (hsum : HasSum (fun k : ℤ => F (γ - (T + (k : ℝ) * h)) * F (γ' - (T + (k : ℝ) * h))) S)
    (hF : ∀ x A B : ℝ, 0 < A → 0 < B → A ≤ |x| → B ≤ |x| → |F x| ≤ C / (A * B))
    (hC : 0 ≤ C) (hh : 0 < h) (hR : h ≤ R)
    (hγ : T + R ≤ γ) (hγd : γ ≤ T + (d : ℝ) * h - R)
    (hγ' : T + R ≤ γ') (hγ'd : γ' ≤ T + (d : ℝ) * h - R) :
    |S - ∑ k : Fin d,
        F (γ - (T + (((k : ℕ) : ℤ) : ℝ) * h)) * F (γ' - (T + (((k : ℕ) : ℤ) : ℝ) * h))|
      ≤ 2 * zetaTwoZ * (C / (R * h)) ^ 2 := by
  have hRpos : 0 < R := lt_of_lt_of_le hh hR
  -- the omitted terms, one at a time
  have key : ∀ k : ℤ, k < 0 ∨ (d : ℤ) ≤ k →
      |F (γ - (T + (k : ℝ) * h)) * F (γ' - (T + (k : ℝ) * h))|
        ≤ (C / (R * h)) ^ 2 * (1 / (k : ℝ) ^ 2 + 1 / ((k : ℝ) - d + 1) ^ 2) := by
    intro k hk
    -- `m` is the number of grid steps beyond the end of the kept range
    obtain ⟨m, hm1, hmk, hx, hx'⟩ : ∃ m : ℝ, 1 ≤ m ∧
        1 / m ^ 2 ≤ 1 / (k : ℝ) ^ 2 + 1 / ((k : ℝ) - d + 1) ^ 2 ∧
        (R ≤ |γ - (T + (k : ℝ) * h)| ∧ m * h ≤ |γ - (T + (k : ℝ) * h)|) ∧
        (R ≤ |γ' - (T + (k : ℝ) * h)| ∧ m * h ≤ |γ' - (T + (k : ℝ) * h)|) := by
      rcases hk with hk | hk
      · -- below the range: `m = -k`
        have hk1 : (k : ℝ) ≤ -1 := by
          have : (k : ℝ) ≤ ((-1 : ℤ) : ℝ) := Int.cast_le.mpr (by omega)
          simpa using this
        have hmh : 0 ≤ -(k : ℝ) * h := mul_nonneg (by linarith) hh.le
        refine ⟨-(k : ℝ), by linarith, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · have h0 : 0 ≤ 1 / ((k : ℝ) - d + 1) ^ 2 := by positivity
          rw [neg_sq]
          linarith
        · exact le_trans (by linarith) (le_abs_self _)
        · exact le_trans (by linarith) (le_abs_self _)
        · exact le_trans (by linarith) (le_abs_self _)
        · exact le_trans (by linarith) (le_abs_self _)
      · -- above the range: `m = k - d + 1`
        have hk1 : (d : ℝ) ≤ (k : ℝ) := by
          have : ((d : ℤ) : ℝ) ≤ (k : ℝ) := Int.cast_le.mpr hk
          simpa using this
        have hmh : 0 ≤ ((k : ℝ) - d) * h := mul_nonneg (by linarith) hh.le
        have hexp : ((k : ℝ) - d + 1) * h = ((k : ℝ) - d) * h + h := by ring
        have hkd : (k : ℝ) * h = ((k : ℝ) - d) * h + (d : ℝ) * h := by ring
        refine ⟨(k : ℝ) - d + 1, by linarith, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · have h0 : 0 ≤ 1 / (k : ℝ) ^ 2 := by positivity
          linarith
        · exact le_trans (by linarith) (neg_le_abs _)
        · exact le_trans (by linarith) (neg_le_abs _)
        · exact le_trans (by linarith) (neg_le_abs _)
        · exact le_trans (by linarith) (neg_le_abs _)
    have hm0 : 0 < m := by linarith
    have hmh : 0 < m * h := mul_pos hm0 hh
    have h1 := hF _ R (m * h) hRpos hmh hx.1 hx.2
    have h2 := hF _ R (m * h) hRpos hmh hx'.1 hx'.2
    have hq : 0 ≤ C / (R * (m * h)) := div_nonneg hC (mul_pos hRpos hmh).le
    calc |F (γ - (T + (k : ℝ) * h)) * F (γ' - (T + (k : ℝ) * h))|
        = |F (γ - (T + (k : ℝ) * h))| * |F (γ' - (T + (k : ℝ) * h))| := abs_mul _ _
      _ ≤ C / (R * (m * h)) * (C / (R * (m * h))) := mul_le_mul h1 h2 (abs_nonneg _) hq
      _ = (C / (R * h)) ^ 2 * (1 / m ^ 2) := by ring
      _ ≤ (C / (R * h)) ^ 2 * (1 / (k : ℝ) ^ 2 + 1 / ((k : ℝ) - d + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left hmk (sq_nonneg _)
  have hg : HasSum (fun k : ℤ => (C / (R * h)) ^ 2 * (1 / (k : ℝ) ^ 2 + 1 / ((k : ℝ) - d + 1) ^ 2))
      ((C / (R * h)) ^ 2 * (zetaTwoZ + zetaTwoZ)) :=
    (hasSum_one_div_int_sq.add (hasSum_one_div_int_sq_shift d)).mul_left _
  have hmain := abs_hasSum_sub_sum_range_le (d := d) hsum hg (fun k => by positivity) key
  calc |S - ∑ k : Fin d,
          F (γ - (T + (((k : ℕ) : ℤ) : ℝ) * h)) * F (γ' - (T + (((k : ℕ) : ℤ) : ℝ) * h))|
      ≤ (C / (R * h)) ^ 2 * (zetaTwoZ + zetaTwoZ) := hmain
    _ = 2 * zetaTwoZ * (C / (R * h)) ^ 2 := by ring

/-! ## The window class -/

/-- Decay of `v̂` away from the origin, in the form used above. -/
lemma abs_vHatR_le_of_far {v : ℝ → ℝ} {L w c : ℝ} (hW : AdmWindow v L w c) (x A B : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hxA : A ≤ |x|) (hxB : B ≤ |x|) :
    |AdmWindow.vHatR v x| ≤ c / w / (A * B) := by
  have h := hW.abs_vHatR_mul_sq_le x
  have hAB : A * B ≤ x ^ 2 := by
    calc A * B ≤ |x| * |x| := mul_le_mul hxA hxB hB.le (abs_nonneg x)
      _ = x ^ 2 := by rw [← sq, sq_abs]
  rw [le_div_iff₀ (mul_pos hA hB)]
  calc |AdmWindow.vHatR v x| * (A * B) ≤ |AdmWindow.vHatR v x| * x ^ 2 :=
        mul_le_mul_of_nonneg_left hAB (abs_nonneg _)
    _ ≤ c / w := h

/-- **Truncated Poisson sum.** For a window of the class and ordinates `γ, γ'` at distance at
least `R ≥ 2π/L` from both ends `T` and `T + d · 2π/L` of the grid range, the sum over
`0 ≤ k < d` differs from the full Poisson sum `L Φ(γ - γ')` by at most
`2 Z ((c/w) / (R · 2π/L))²`. -/
theorem abs_poisson_sub_sum_le {v : ℝ → ℝ} {L w c : ℝ} (hW : AdmWindow v L w c) (T : ℝ) (d : ℕ)
    {R γ γ' : ℝ} (hR : 2 * π / L ≤ R)
    (hγ : T + R ≤ γ) (hγd : γ ≤ T + (d : ℝ) * (2 * π / L) - R)
    (hγ' : T + R ≤ γ') (hγ'd : γ' ≤ T + (d : ℝ) * (2 * π / L) - R) :
    |L * AdmWindow.VPhiR v (γ - γ')
        - ∑ k : Fin d, AdmWindow.vHatR v (γ - (T + (((k : ℕ) : ℤ) : ℝ) * (2 * π / L)))
            * AdmWindow.vHatR v (γ' - (T + (((k : ℕ) : ℤ) : ℝ) * (2 * π / L)))|
      ≤ 2 * zetaTwoZ * (c / w / (R * (2 * π / L))) ^ 2 := by
  have hL : 0 < L := hW.L_pos
  have hh : 0 < 2 * π / L := by positivity
  have hC : 0 ≤ c / w := div_nonneg hW.c_nonneg hW.w_pos.le
  exact abs_hasSum_sub_sum_le (F := AdmWindow.vHatR v) (h := 2 * π / L) (C := c / w) (T := T)
    (d := d) (hW.hasSum_vHatR_mul T γ γ') (abs_vHatR_le_of_far hW) hC hh hR hγ hγd hγ' hγ'd

end Distinct839.ZeroKernel
