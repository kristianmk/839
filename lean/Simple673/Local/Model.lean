/-
Simple673/Local/Model.lean — the real-valued quantities that the checker bounds.

Everything is in grid units: a gap `g_r` is `u_r / H`, `H = 16384`, and the local inequality for
the labeling coded by `m` (bit `i` of `m` is the label of site `i`) is multiplied by
`2 · 10⁶ · V`, `V = 2²⁸`. It reads `rhsOf m ≤ rhsR u m` (`Good`). The labelings belong to the
general format of the checker; the data are label-blind, so the `256` inequalities are one and
the same, and `Simple673/Local/Bridge.lean` uses the one for `m = 0`. This file defines the boxes,
proves the pressure bound (`good_of_pressure`: the inequality holds once `∑ u` is large), the
small facts about the frozen data that the checker relies on, and the bounds that hold for the
pair distances and the potentials on a box.
-/
import Simple673.Local.Potential
import Simple673.Local.Kernel

open Finset

namespace Simple673
namespace Local

/-! ## Labels -/

theorem bit_lt_two (m i : ℕ) : bit m i < 2 := Nat.mod_lt _ (by norm_num)

theorem bit_cases (m i : ℕ) : bit m i = 0 ∨ bit m i = 1 := by
  have := bit_lt_two m i; omega

@[simp] theorem bit_zero (i : ℕ) : bit 0 i = 0 := by simp [bit]

/-! ## Facts about the frozen data -/

theorem h_mono : ∀ i < 8, hT 0 i ≤ hT 1 i := by decide +kernel

theorem w_mono : ∀ i < 8, ∀ j < 8, wT 0 i j ≤ wT 1 i j ∧ wT 0 i j ≤ wT 2 i j := by
  decide +kernel

theorem sum_h1 : sumTo (fun i => hT 1 i) 8 = cH2 := by decide +kernel

theorem sum_h0 : sumTo (fun i => hT 0 i) 8 = cH1 := by decide +kernel

/-- `α R / H ≥ x₁ + 0.001294`, in the integer units of the checker:
`(8722 + 1294) · 16384 = 164102144 ≤ 627 · 262143 = 164363661`. -/
theorem pressure_const : (cH2 + cBudget) * cV ≤ cR * cP := by decide +kernel

theorem hT_le (a i : ℕ) (hi : i < 8) : hT a i ≤ hT 1 i := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact h_mono i hi
  · have : hT a i = hT 1 i := by simp [hT, ha.ne']
    rw [this]

/-- The reward of a site as a real number: `h_{i,0} + d_i (h_{i,1} - h_{i,0})`. -/
theorem hT_bit (m i : ℕ) :
    (hT (bit m i) i : ℝ) = hT 0 i + (bit m i : ℝ) * ((hT 1 i : ℝ) - hT 0 i) := by
  rcases bit_cases m i with h | h <;> rw [h] <;> push_cast <;> ring

/-! ## The scaled inequality -/

/-- The grid distance between the sites `i ≤ j`: `u_i + ⋯ + u_{j-1}`. -/
noncomputable def dist (u : ℕ → ℝ) (i j : ℕ) : ℝ := ∑ k ∈ range (j - i), u (i + k)

/-- `2 · 10⁶ · V` times the right side of the local inequality for the labeling `m`. -/
noncomputable def rhsR (u : ℕ → ℝ) (m : ℕ) : ℝ :=
  2 * (cP : ℝ) * ∑ r ∈ range 7, u r
  + 2 * ∑ j ∈ range 8, ∑ i ∈ range j, (wT (bit m i + bit m j) i j : ℝ) * kap (dist u i j)
  + 2 * ∑ r ∈ range 7, betN r (bit m r + bit m (r + 1)) (u r)

/-- The scaled local inequality at the grid point `u`, for every labeling. -/
def Good (u : ℕ → ℝ) : Prop := ∀ m < 256, (rhsOf m : ℝ) ≤ rhsR u m

/-- The point `u` lies in the box `lo hi` (first seven coordinates). -/
def InBox (lo hi : Array ℕ) (u : ℕ → ℝ) : Prop := ∀ r < 7, (g lo r : ℝ) ≤ u r ∧ u r ≤ g hi r

/-- The local inequality holds on the part of the box `lo hi` with `∑ u ≤ R`. -/
def BoxOK (lo hi : Array ℕ) : Prop :=
  ∀ u, InBox lo hi u → ∑ r ∈ range 7, u r ≤ cR → Good u

/-! ## Pressure -/

theorem rhsOf_le (m : ℕ) : (rhsOf m : ℝ) ≤ 2 * cV * cH2 := by
  have h : sumTo (fun i => hT (bit m i) i) 8 ≤ cH2 := by
    rw [← sum_h1, sumTo_eq, sumTo_eq]
    exact sum_le_sum fun i hi => hT_le _ i (mem_range.1 hi)
  unfold rhsOf
  push_cast
  have h' : (sumTo (fun i => hT (bit m i) i) 8 : ℝ) ≤ cH2 := by exact_mod_cast h
  have hV : (0 : ℝ) ≤ cV := Nat.cast_nonneg _
  nlinarith

theorem sum_nb : ∑ r ∈ range 7, (nb r : ℝ) = cBudget := by
  have := nb_sum
  simp only [sum_range_succ, sum_range_zero, zero_add]
  exact_mod_cast this

/-- The weighted kernel terms are nonnegative. -/
theorem kernel_sum_nonneg (u : ℕ → ℝ) (m : ℕ) :
    0 ≤ ∑ j ∈ range 8, ∑ i ∈ range j, (wT (bit m i + bit m j) i j : ℝ) * kap (dist u i j) :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (kap_nonneg _)

/-- The potentials add up to at least `-0.001294` (scaled). -/
theorem pot_sum_ge (u : ℕ → ℝ) (m : ℕ) :
    -((cBudget : ℝ) * cV) ≤ ∑ r ∈ range 7, betN r (bit m r + bit m (r + 1)) (u r) := by
  rw [← sum_nb, sum_mul, ← sum_neg_distrib]
  refine sum_le_sum fun r hr => ?_
  have h1 := bit_lt_two m r
  have h2 := bit_lt_two m (r + 1)
  exact betN_lower (mem_range.1 hr) (by omega) (u r)

/-- Pressure alone proves the inequality when `α ∑ g ≥ x₁ + 0.001294`. -/
theorem good_of_pressure (u : ℕ → ℝ)
    (h : ((cH2 + cBudget) * cV : ℝ) ≤ cP * ∑ r ∈ range 7, u r) : Good u := by
  intro m _
  have h1 := rhsOf_le m
  have h2 := kernel_sum_nonneg u m
  have h3 := pot_sum_ge u m
  unfold rhsR
  nlinarith

/-- In particular the inequality holds when `∑ u ≥ R`. -/
theorem good_of_sum_ge (u : ℕ → ℝ) (h : (cR : ℝ) ≤ ∑ r ∈ range 7, u r) : Good u := by
  apply good_of_pressure
  have h1 : (((cH2 + cBudget) * cV : ℕ) : ℝ) ≤ ((cR * cP : ℕ) : ℝ) := by
    exact_mod_cast pressure_const
  push_cast at h1
  have hP : (0 : ℝ) ≤ cP := Nat.cast_nonneg _
  nlinarith

/-! ## Boxes -/

theorem sumTo_g_cast (lo : Array ℕ) : ((sumTo (g lo) 7 : ℕ) : ℝ) = ∑ r ∈ range 7, (g lo r : ℝ) := by
  rw [sumTo_eq]; push_cast; rfl

theorem total_le (lo : Array ℕ) (u : ℕ → ℝ) (hu : ∀ r < 7, (g lo r : ℝ) ≤ u r) :
    ((sumTo (g lo) 7 : ℕ) : ℝ) ≤ ∑ r ∈ range 7, u r := by
  rw [sumTo_g_cast]
  exact sum_le_sum fun r hr => hu r (mem_range.1 hr)

/-- `(a - b : ℕ) ≥ a - b` in the reals. -/
theorem cast_tsub_ge (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h]
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    simp only [Nat.cast_zero]; linarith

/-- A coordinate exceeds its lower end by at most `∑ u - ∑ lo`. -/
theorem coord_le (lo : Array ℕ) (u : ℕ → ℝ) (hu : ∀ r < 7, (g lo r : ℝ) ≤ u r) (r : ℕ)
    (hr : r < 7) : u r - g lo r ≤ ∑ s ∈ range 7, u s - ((sumTo (g lo) 7 : ℕ) : ℝ) := by
  rw [sumTo_g_cast, ← sum_sub_distrib]
  exact single_le_sum (f := fun s => u s - (g lo s : ℝ))
    (fun s hs => sub_nonneg.2 (hu s (mem_range.1 hs))) (mem_range.2 hr)

/-- The distance between `i ≤ j ≤ 7` exceeds its lower end by at most `∑ u - ∑ lo`. -/
theorem dist_sub_le (lo : Array ℕ) (u : ℕ → ℝ) (hu : ∀ r < 7, (g lo r : ℝ) ≤ u r) (i j : ℕ)
    (hj : j ≤ 7) :
    dist u i j - ∑ k ∈ range (j - i), (g lo (i + k) : ℝ)
      ≤ ∑ s ∈ range 7, u s - ((sumTo (g lo) 7 : ℕ) : ℝ) := by
  rw [sumTo_g_cast, ← sum_sub_distrib, dist, ← sum_sub_distrib,
    ← sum_Ico_eq_sum_range (fun s => u s - (g lo s : ℝ))]
  refine sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun s hs _ => ?_)
  · rw [mem_Ico] at hx; rw [mem_range]; omega
  · exact sub_nonneg.2 (hu s (mem_range.1 hs))

/-- Upper ends cut at `∑ u ≤ R`: the clamped box contains every point of the box with
`∑ u ≤ R`. -/
theorem inBox_clamp (lo hi : Array ℕ) (u : ℕ → ℝ) (hu : InBox lo hi u)
    (hsum : ∑ r ∈ range 7, u r ≤ cR) : InBox lo (clamp lo hi (sumTo (g lo) 7)) u := by
  intro r hr
  refine ⟨(hu r hr).1, ?_⟩
  unfold clamp
  rw [g, getD_ofFn _ _ _ hr]
  simp only
  have h1 := coord_le lo u (fun s hs => (hu s hs).1) r hr
  have h2 := cast_tsub_ge (cR + g lo r) (sumTo (g lo) 7)
  push_cast at h2
  rw [Nat.cast_min, le_min_iff]
  exact ⟨(hu r hr).2, by linarith⟩

/-! ## Bounds on a box -/

theorem edAt_edges (sp : Array (Array ℕ)) (lo hi : Array ℕ) (total i j : ℕ) (hij : i < j)
    (hj : j < 8) : edAt (edges sp lo hi total) i j = mkEdge sp lo hi total i j := by
  unfold edAt edges
  rw [getD_ofFn _ _ _ (by omega)]
  have h1 : (i * 8 + j) / 8 = i := by omega
  have h2 : (i * 8 + j) % 8 = j := by omega
  simp only [h1, h2, if_pos hij]

/-- On a box (with `∑ u ≤ R`), the distance of the pair `i < j` lies in one of the cells
`l, …, max l (h - 1)` of its edge, where `l = ∑ lo` over the gaps between the two sites and
`h = min (∑ hi) (R - (total - l))`. -/
theorem dist_cell (lo hi : Array ℕ) (u : ℕ → ℝ) (hu : InBox lo hi u)
    (hsum : ∑ r ∈ range 7, u r ≤ cR) (i j : ℕ) (hij : i < j) (hj : j < 8) :
    ∃ k : ℕ, sumTo (fun k => g lo (i + k)) (j - i) ≤ k ∧
      k ≤ max (sumTo (fun k => g lo (i + k)) (j - i))
        (min (sumTo (fun k => g hi (i + k)) (j - i))
          (cR + sumTo (fun k => g lo (i + k)) (j - i) - sumTo (g lo) 7) - 1) ∧
      (k : ℝ) ≤ dist u i j ∧ dist u i j ≤ k + 1 := by
  have hcell : ∀ k, k < j - i → i + k < 7 := fun k hk => by omega
  -- lower end
  have hl : ((sumTo (fun k => g lo (i + k)) (j - i) : ℕ) : ℝ) ≤ dist u i j := by
    rw [sumTo_eq, dist]; push_cast
    exact sum_le_sum fun k hk => (hu (i + k) (hcell k (mem_range.1 hk))).1
  -- upper ends
  have hh1 : dist u i j ≤ ((sumTo (fun k => g hi (i + k)) (j - i) : ℕ) : ℝ) := by
    rw [sumTo_eq, dist]; push_cast
    exact sum_le_sum fun k hk => (hu (i + k) (hcell k (mem_range.1 hk))).2
  have hh2 : dist u i j ≤ ((cR + sumTo (fun k => g lo (i + k)) (j - i)
      - sumTo (g lo) 7 : ℕ) : ℝ) := by
    have h3 := dist_sub_le lo u (fun r hr => (hu r hr).1) i j (by omega)
    have h4 := cast_tsub_ge (cR + sumTo (fun k => g lo (i + k)) (j - i)) (sumTo (g lo) 7)
    rw [sumTo_eq] at h4 ⊢
    push_cast at h4 h3 ⊢
    linarith
  generalize sumTo (fun k => g lo (i + k)) (j - i) = l at hl hh2 ⊢
  generalize sumTo (fun k => g hi (i + k)) (j - i) = h1 at hh1 ⊢
  have hh : dist u i j ≤ ((min h1 (cR + l - sumTo (g lo) 7) : ℕ) : ℝ) := by
    rw [Nat.cast_min]; exact le_min hh1 hh2
  exact exists_cell l _ _ hl hh

/-- On a box (with `∑ u ≤ R`), the kernel bound of an edge and its affine support are below the
scaled kernel square at the distance of the pair. -/
theorem edge_bounds (tab : Array ℕ) (htab : TabOK tab) (lo hi : Array ℕ) (u : ℕ → ℝ)
    (hu : InBox lo hi u) (hsum : ∑ r ∈ range 7, u r ≤ cR) (i j : ℕ) (hij : i < j) (hj : j < 8) :
    ((mkEdge (sparse tab) lo hi (sumTo (g lo) 7) i j).kv : ℝ) ≤ kap (dist u i j) ∧
    (((kaff tab (mkEdge (sparse tab) lo hi (sumTo (g lo) 7) i j)).s.toInt : ℤ) : ℝ)
        * dist u i j
      + (((kaff tab (mkEdge (sparse tab) lo hi (sumTo (g lo) 7) i j)).o.toInt : ℤ) : ℝ)
      ≤ 2 * kap (dist u i j) := by
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := dist_cell lo hi u hu hsum i j hij hj
  simp only [mkEdge]
  exact ⟨(Nat.cast_le.2 (rmin_le tab _ _ k hk1 hk2)).trans (htab k _ hk3 hk4),
    kaff_spec tab htab ⟨_, _, _⟩ k hk1 hk2 _ hk3 hk4⟩

end Local
end Simple673
