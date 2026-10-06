/-
Simple673/Local/Node.lean — the lower bounds computed on one box are sound.

On a box `lo hi` (already clamped to `∑ u ≤ R`) the checker computes

* `baseOf`: a lower bound for the labeling `0` from range minima (`stage1`);
* `penalty`: the label shortcut of the general format. Raising the labels of a set of sites
  costs at least `∑_i min(0, ∑_{e ∋ i} η_e - 2V(h_{i,2} - h_{i,1}))` (`shortcut`);
* `valOf`: the exact minimum over the box of an affine lower bound for one labeling
  (`stage2`).

The proofs are those of `Distinct839/Local/Node.lean` and hold for any tables with the
monotonicity `h_mono`, `w_mono`. For the label-blind data of this development the penalty is
`0` and all labelings give the same inequality; the final statement uses the labeling `0`.
-/
import Simple673.Local.Model

open Finset

namespace Simple673
namespace Local

/-! ## Array reads -/

theorem bmAt_bmArr (lo hi : Array ℕ) (r t : ℕ) (hr : r < 7) (ht : t < 3) :
    bmAt (bmArr lo hi) r t = if t = 0 then pmin (bv r 0) (g lo r) (g hi r)
      else pmin (fun x => (bv r t x).sub (bv r 0 x)) (g lo r) (g hi r) := by
  unfold bmAt bmArr
  rw [getD_ofFn _ _ _ (by omega)]
  have h1 : (r * 3 + t) / 3 = r := by omega
  have h2 : (r * 3 + t) % 3 = t := by omega
  simp only [h1, h2]

theorem incAt_incArr (ed : Array Edge) (bm : Array SInt) (i j : ℕ) (hij : i < j) (hj : j < 8) :
    incAt (incArr ed bm) i j = incOf ed bm i j := by
  unfold incAt incArr
  rw [getD_ofFn _ _ _ (by omega)]
  have h1 : (i * 8 + j) / 8 = i := by omega
  have h2 : (i * 8 + j) % 8 = j := by omega
  simp only [h1, h2, if_pos hij]

theorem affArr_getD (tab : Array ℕ) (ed : Array Edge) (i j : ℕ) (hij : i < j) (hj : j < 8) :
    (affArr tab ed).getD (i * 8 + j) ⟨SInt.zero, SInt.zero⟩ = kaff tab (edAt ed i j) := by
  unfold affArr
  rw [getD_ofFn _ _ _ (by omega)]
  have h1 : (i * 8 + j) / 8 = i := by omega
  have h2 : (i * 8 + j) % 8 = j := by omega
  simp only [h1, h2, if_pos hij]

theorem w3At_wk (af : Array Aff) (t i j : ℕ) (ht : t < 3) (hij : i < j) (hj : j < 8) :
    w3At (wkArr af) t i j = (af.getD (i * 8 + j) ⟨SInt.zero, SInt.zero⟩).s.smul (wT t i j) := by
  unfold w3At wkArr
  rw [getD_ofFn _ _ _ (by omega)]
  have h1 : (t * 64 + i * 8 + j) % 64 = i * 8 + j := by omega
  simp only [h1]
  rfl

theorem w3At_wo (af : Array Aff) (t i j : ℕ) (ht : t < 3) (hij : i < j) (hj : j < 8) :
    w3At (woArr af) t i j = (af.getD (i * 8 + j) ⟨SInt.zero, SInt.zero⟩).o.smul (wT t i j) := by
  unfold w3At woArr
  rw [getD_ofFn _ _ _ (by omega)]
  have h1 : (t * 64 + i * 8 + j) % 64 = i * 8 + j := by omega
  simp only [h1]
  rfl

theorem paAt_paArr (lo hi : Array ℕ) (r t : ℕ) (hr : r < 7) (ht : t < 3) :
    paAt (paArr lo hi) r t = paff r t (g lo r) (g hi r) := by
  unfold paAt paArr
  rw [getD_ofFn _ _ _ (by omega)]
  have h1 : (r * 3 + t) / 3 = r := by omega
  have h2 : (r * 3 + t) % 3 = t := by omega
  simp only [h1, h2]

/-! ## Valid edge data -/

/-- The kernel bounds of the edge data `ed` are valid at the point `u`. -/
def EdOK (ed : Array Edge) (u : ℕ → ℝ) : Prop :=
  ∀ i j, i < j → j < 8 → ((edAt ed i j).kv : ℝ) ≤ kap (dist u i j)

/-- The affine kernel supports computed from the edge data `ed` are valid at the point `u`. -/
def AffOK (tab : Array ℕ) (ed : Array Edge) (u : ℕ → ℝ) : Prop :=
  ∀ i j, i < j → j < 8 →
    (((kaff tab (edAt ed i j)).s.toInt : ℤ) : ℝ) * dist u i j
      + (((kaff tab (edAt ed i j)).o.toInt : ℤ) : ℝ) ≤ 2 * kap (dist u i j)

/-- The edge data computed by the checker are valid on the box (with `∑ u ≤ R`). -/
theorem edges_ok (tab : Array ℕ) (htab : TabOK tab) (lo hi : Array ℕ) (u : ℕ → ℝ)
    (hu : InBox lo hi u) (hsum : ∑ r ∈ range 7, u r ≤ cR) :
    EdOK (edges (sparse tab) lo hi (sumTo (g lo) 7)) u ∧
      AffOK tab (edges (sparse tab) lo hi (sumTo (g lo) 7)) u := by
  refine ⟨fun i j hij hj => ?_, fun i j hij hj => ?_⟩
  · rw [edAt_edges _ _ _ _ i j hij hj]
    exact (edge_bounds tab htab lo hi u hu hsum i j hij hj).1
  · rw [edAt_edges _ _ _ _ i j hij hj]
    exact (edge_bounds tab htab lo hi u hu hsum i j hij hj).2

/-! ## Potentials on a box -/

theorem bm0_box (lo hi : Array ℕ) (u : ℕ → ℝ) (hu : InBox lo hi u) (r : ℕ) (hr : r < 7) :
    (((bmAt (bmArr lo hi) r 0).toInt : ℤ) : ℝ) ≤ betN r 0 (u r) := by
  rw [bmAt_bmArr lo hi r 0 hr (by norm_num), if_pos rfl]
  exact bm0_spec hr _ _ _ (hu r hr).1 (hu r hr).2

theorem bmD_box (lo hi : Array ℕ) (u : ℕ → ℝ) (hu : InBox lo hi u) (r : ℕ) (hr : r < 7) (t : ℕ)
    (ht1 : 0 < t) (ht : t < 3) :
    (((bmAt (bmArr lo hi) r t).toInt : ℤ) : ℝ) ≤ betN r t (u r) - betN r 0 (u r) := by
  rw [bmAt_bmArr lo hi r t hr ht, if_neg (by omega)]
  exact bmD_spec hr ht _ _ _ (hu r hr).1 (hu r hr).2

theorem paff_box (lo hi : Array ℕ) (u : ℕ → ℝ) (hu : InBox lo hi u) (r t : ℕ) (hr : r < 7)
    (ht : t < 3) :
    (((paAt (paArr lo hi) r t).s.toInt : ℤ) : ℝ) * u r
        + (((paAt (paArr lo hi) r t).o.toInt : ℤ) : ℝ)
      ≤ 2 * betN r t (u r) := by
  rw [paAt_paArr lo hi r t hr ht]
  exact paff_spec hr ht _ _ _ (hu r hr).1 (hu r hr).2

/-! ## Sums over the pairs of eight sites -/

/-- The potentials, written as a sum over the adjacent pairs. -/
theorem sum_adj (F : ℕ → ℕ → ℝ) :
    ∑ j ∈ range 8, ∑ i ∈ range j, (if j = i + 1 then F i j else 0)
      = ∑ r ∈ range 7, F r (r + 1) := by
  simp only [sum_range_succ, sum_range_zero]
  norm_num

/-- Each pair contributes to the degree of both its sites. -/
theorem sum_deg (η : ℕ → ℕ → ℝ) (d : ℕ → ℝ) :
    ∑ j ∈ range 8, ∑ i ∈ range j, η i j * (d i + d j)
      = ∑ i ∈ range 8, d i *
          ∑ j ∈ range 8, (if i < j then η i j else if j < i then η j i else 0) := by
  simp only [sum_range_succ, sum_range_zero]
  norm_num
  ring

/-- A pair distance is the sum of the gaps between its sites. -/
theorem sum_dist (S : ℕ → ℕ → ℝ) (u : ℕ → ℝ) :
    ∑ r ∈ range 7, (∑ i ∈ range (r + 1), ∑ k ∈ range (7 - r), S i (r + 1 + k)) * u r
      = ∑ j ∈ range 8, ∑ i ∈ range j, S i j * dist u i j := by
  simp only [dist, sum_range_succ, sum_range_zero]
  norm_num
  ring

/-! ## The label shortcut -/

/-- The cost of the labeling `m` over the labeling `0`, pair by pair. -/
theorem rhsR_sub (u : ℕ → ℝ) (m : ℕ) :
    rhsR u m - rhsR u 0 = ∑ j ∈ range 8, ∑ i ∈ range j,
      (2 * ((wT (bit m i + bit m j) i j : ℝ) - wT 0 i j) * kap (dist u i j)
        + (if j = i + 1 then 2 * (betN i (bit m i + bit m j) (u i) - betN i 0 (u i)) else 0)) := by
  have h := sum_adj (fun i j => 2 * (betN i (bit m i + bit m j) (u i) - betN i 0 (u i)))
  have e1 : ∑ j ∈ range 8, ∑ i ∈ range j,
        2 * ((wT (bit m i + bit m j) i j : ℝ) - wT 0 i j) * kap (dist u i j)
      = 2 * ∑ j ∈ range 8, ∑ i ∈ range j, (wT (bit m i + bit m j) i j : ℝ) * kap (dist u i j)
        - 2 * ∑ j ∈ range 8, ∑ i ∈ range j, (wT 0 i j : ℝ) * kap (dist u i j) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  have e2 : ∑ r ∈ range 7, 2 * (betN r (bit m r + bit m (r + 1)) (u r) - betN r 0 (u r))
      = 2 * ∑ r ∈ range 7, betN r (bit m r + bit m (r + 1)) (u r)
        - 2 * ∑ r ∈ range 7, betN r 0 (u r) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun r _ => by ring
  simp only [sum_add_distrib, h]
  rw [e1, e2]
  unfold rhsR
  simp only [bit_zero, add_zero]
  ring

/-- The reward of the labeling `m` over the labeling `0`. -/
theorem rhsOf_sub (m : ℕ) :
    (rhsOf m : ℝ) - rhsOf 0
      = ∑ i ∈ range 8, (bit m i : ℝ) * (2 * cV * ((hT 1 i : ℝ) - hT 0 i)) := by
  unfold rhsOf
  rw [sumTo_eq, sumTo_eq]
  push_cast
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [hT_bit m i, bit_zero]
  ring

/-- The penalty is at most the extra cost of any labeling over its degree terms. -/
theorem pen_le (inc : Array SInt) (m : ℕ) :
    (((penalty inc).toInt : ℤ) : ℝ) ≤ ∑ i ∈ range 8, (bit m i : ℝ) *
      (∑ j ∈ range 8, (if i < j then (((incAt inc i j).toInt : ℤ) : ℝ)
          else if j < i then (((incAt inc j i).toInt : ℤ) : ℝ) else 0)
        - 2 * cV * ((hT 1 i : ℝ) - hT 0 i)) := by
  unfold penalty
  rw [toInt_ssumTo, Int.cast_sum]
  refine sum_le_sum fun i hi => ?_
  dsimp only
  have hh := h_mono i (mem_range.1 hi)
  rw [SInt.toInt_min, SInt.toInt_sub, toInt_ssumTo, SInt.toInt_ofNat, SInt.toInt_zero]
  simp only [apply_ite SInt.toInt, SInt.toInt_zero]
  push_cast [Nat.cast_sub hh]
  rcases bit_cases m i with h | h <;> rw [h]
  · exact (min_le_left _ _).trans (le_of_eq (by simp))
  · exact (min_le_right _ _).trans (le_of_eq (by push_cast; ring))

/-- One pair: the cost of its labels is at least `η_e (d_i + d_j)`. -/
theorem edge_claim (ed : Array Edge) (lo hi : Array ℕ) (u : ℕ → ℝ) (hed : EdOK ed u)
    (hu : InBox lo hi u) (m i j : ℕ) (hij : i < j) (hj : j < 8) :
    (((incOf ed (bmArr lo hi) i j).toInt : ℤ) : ℝ)
        * ((bit m i : ℝ) + bit m j)
      ≤ 2 * ((wT (bit m i + bit m j) i j : ℝ) - wT 0 i j) * kap (dist u i j)
        + (if j = i + 1 then 2 * (betN i (bit m i + bit m j) (u i) - betN i 0 (u i)) else 0) := by
  have hkv := hed i j hij hj
  obtain ⟨hw1, hw2⟩ := w_mono i (by omega) j hj
  unfold incOf
  dsimp only
  generalize (edAt ed i j).kv = kv at hkv ⊢
  generalize kap (dist u i j) = K at hkv ⊢
  have m1 : ((wT 1 i j : ℝ) - wT 0 i j) * kv ≤ ((wT 1 i j : ℝ) - wT 0 i j) * K :=
    mul_le_mul_of_nonneg_left hkv (by have : (wT 0 i j : ℝ) ≤ wT 1 i j := by exact_mod_cast hw1
                                      linarith)
  have m2 : ((wT 2 i j : ℝ) - wT 0 i j) * kv ≤ ((wT 2 i j : ℝ) - wT 0 i j) * K :=
    mul_le_mul_of_nonneg_left hkv (by have : (wT 0 i j : ℝ) ≤ wT 2 i j := by exact_mod_cast hw2
                                      linarith)
  by_cases hadj : j = i + 1
  · rw [if_pos hadj, if_pos hadj]
    have b1 := bmD_box lo hi u hu i (by omega) 1 (by norm_num) (by norm_num)
    have b2 := bmD_box lo hi u hu i (by omega) 2 (by norm_num) (by norm_num)
    generalize bmAt (bmArr lo hi) i 1 = B1 at b1 ⊢
    generalize bmAt (bmArr lo hi) i 2 = B2 at b2 ⊢
    have hA := SInt.toInt_min_le_left
      ((SInt.ofNat (2 * (wT 1 i j - wT 0 i j) * kv)).add (B1.smul 2))
      ((SInt.ofNat ((wT 2 i j - wT 0 i j) * kv)).add B2)
    have hB := SInt.toInt_min_le_right
      ((SInt.ofNat (2 * (wT 1 i j - wT 0 i j) * kv)).add (B1.smul 2))
      ((SInt.ofNat ((wT 2 i j - wT 0 i j) * kv)).add B2)
    generalize (SInt.min ((SInt.ofNat (2 * (wT 1 i j - wT 0 i j) * kv)).add (B1.smul 2))
      ((SInt.ofNat ((wT 2 i j - wT 0 i j) * kv)).add B2)).toInt = η at hA hB ⊢
    simp only [SInt.toInt_add, SInt.toInt_ofNat, SInt.toInt_smul] at hA hB
    have hA' : (η : ℝ) ≤ 2 * ((wT 1 i j : ℝ) - wT 0 i j) * kv + 2 * ((B1.toInt : ℤ) : ℝ) := by
      have := (Int.cast_le (R := ℝ)).2 hA
      push_cast [Nat.cast_sub hw1] at this
      linarith
    have hB' : (η : ℝ) ≤ ((wT 2 i j : ℝ) - wT 0 i j) * kv + ((B2.toInt : ℤ) : ℝ) := by
      have := (Int.cast_le (R := ℝ)).2 hB
      push_cast [Nat.cast_sub hw2] at this
      linarith
    subst hadj
    rcases bit_cases m i with h1 | h1 <;> rcases bit_cases m (i + 1) with h2 | h2 <;>
      simp only [h1, h2, Nat.cast_zero, Nat.cast_one, Nat.reduceAdd, add_zero, zero_add,
        sub_self, mul_zero, zero_mul, le_refl] <;> linarith
  · rw [if_neg hadj, if_neg hadj]
    have hA := SInt.toInt_min_le_left (SInt.ofNat (2 * (wT 1 i j - wT 0 i j) * kv))
      (SInt.ofNat ((wT 2 i j - wT 0 i j) * kv))
    have hB := SInt.toInt_min_le_right (SInt.ofNat (2 * (wT 1 i j - wT 0 i j) * kv))
      (SInt.ofNat ((wT 2 i j - wT 0 i j) * kv))
    generalize (SInt.min (SInt.ofNat (2 * (wT 1 i j - wT 0 i j) * kv))
      (SInt.ofNat ((wT 2 i j - wT 0 i j) * kv))).toInt = η at hA hB ⊢
    simp only [SInt.toInt_ofNat] at hA hB
    have hA' : (η : ℝ) ≤ 2 * ((wT 1 i j : ℝ) - wT 0 i j) * kv := by
      have := (Int.cast_le (R := ℝ)).2 hA
      push_cast [Nat.cast_sub hw1] at this
      linarith
    have hB' : (η : ℝ) ≤ ((wT 2 i j : ℝ) - wT 0 i j) * kv := by
      have := (Int.cast_le (R := ℝ)).2 hB
      push_cast [Nat.cast_sub hw2] at this
      linarith
    rcases bit_cases m i with h1 | h1 <;> rcases bit_cases m j with h2 | h2 <;>
      simp only [h1, h2, Nat.cast_zero, Nat.cast_one, Nat.reduceAdd, add_zero, zero_add,
        sub_self, mul_zero, zero_mul, le_refl] <;> linarith

/-- The label shortcut: for every labeling `m`, the slack of `m` is at least the slack of the
labeling `0` plus the penalty. -/
theorem shortcut (ed : Array Edge) (lo hi : Array ℕ) (u : ℕ → ℝ) (hed : EdOK ed u)
    (hu : InBox lo hi u) (m : ℕ) :
    rhsR u 0 - rhsOf 0 + (((penalty (incArr ed (bmArr lo hi))).toInt : ℤ) : ℝ)
      ≤ rhsR u m - rhsOf m := by
  have h1 := rhsR_sub u m
  have h2 := rhsOf_sub m
  have h3 := pen_le (incArr ed (bmArr lo hi)) m
  have h4 : ∑ j ∈ range 8, ∑ i ∈ range j,
      (((incAt (incArr ed (bmArr lo hi)) i j).toInt : ℤ) : ℝ) * ((bit m i : ℝ) + bit m j)
      ≤ ∑ j ∈ range 8, ∑ i ∈ range j,
      (2 * ((wT (bit m i + bit m j) i j : ℝ) - wT 0 i j) * kap (dist u i j)
        + (if j = i + 1 then 2 * (betN i (bit m i + bit m j) (u i) - betN i 0 (u i))
          else 0)) := by
    refine sum_le_sum fun j hj => sum_le_sum fun i him => ?_
    rw [incAt_incArr _ _ i j (mem_range.1 him) (mem_range.1 hj)]
    exact edge_claim ed lo hi u hed hu m i j (mem_range.1 him) (mem_range.1 hj)
  rw [sum_deg (fun i j => (((incAt (incArr ed (bmArr lo hi)) i j).toInt : ℤ) : ℝ))
    (fun i => (bit m i : ℝ))] at h4
  have h5 : ∑ i ∈ range 8, (bit m i : ℝ) *
      (∑ j ∈ range 8, (if i < j then (((incAt (incArr ed (bmArr lo hi)) i j).toInt : ℤ) : ℝ)
          else if j < i then (((incAt (incArr ed (bmArr lo hi)) j i).toInt : ℤ) : ℝ) else 0)
        - 2 * cV * ((hT 1 i : ℝ) - hT 0 i))
      = ∑ i ∈ range 8, (bit m i : ℝ) *
      (∑ j ∈ range 8, (if i < j then (((incAt (incArr ed (bmArr lo hi)) i j).toInt : ℤ) : ℝ)
          else if j < i then (((incAt (incArr ed (bmArr lo hi)) j i).toInt : ℤ) : ℝ) else 0))
        - ∑ i ∈ range 8, (bit m i : ℝ) * (2 * cV * ((hT 1 i : ℝ) - hT 0 i)) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  linarith

/-! ## The two lower bounds -/

/-- The bound from range minima for the labeling `0`. -/
theorem stage1 (ed : Array Edge) (lo hi : Array ℕ) (u : ℕ → ℝ) (hed : EdOK ed u)
    (hu : InBox lo hi u) :
    2 * (((baseOf (sumTo (g lo) 7) ed (bmArr lo hi)).toInt : ℤ) : ℝ) ≤ rhsR u 0 := by
  have h1 := total_le lo u (fun r hr => (hu r hr).1)
  have h2 : ∑ j ∈ range 8, ∑ i ∈ range j, (wT 0 i j : ℝ) * ((edAt ed i j).kv : ℝ)
      ≤ ∑ j ∈ range 8, ∑ i ∈ range j, (wT 0 i j : ℝ) * kap (dist u i j) :=
    sum_le_sum fun j hj => sum_le_sum fun i him =>
      mul_le_mul_of_nonneg_left (hed i j (mem_range.1 him) (mem_range.1 hj)) (Nat.cast_nonneg _)
  have h3 : ∑ r ∈ range 7, (((bmAt (bmArr lo hi) r 0).toInt : ℤ) : ℝ)
      ≤ ∑ r ∈ range 7, betN r 0 (u r) :=
    sum_le_sum fun r hr => bm0_box lo hi u hu r (mem_range.1 hr)
  have hP : (0 : ℝ) ≤ cP := Nat.cast_nonneg _
  have h4 := mul_le_mul_of_nonneg_left h1 hP
  unfold baseOf
  generalize sumTo (g lo) 7 = total at h4 ⊢
  rw [SInt.toInt_add, SInt.toInt_ofNat, toInt_ssumTo]
  simp only [sumTo_eq]
  push_cast
  unfold rhsR
  simp only [bit_zero, add_zero]
  linarith

/-- The value of one coordinate term of `valOf` is at most the linear coefficient times the
coordinate. -/
theorem corner_le (lin : SInt) (a b : ℕ) (x : ℝ) (ha : (a : ℝ) ≤ x) (hb : x ≤ b) :
    ((((if lin.n ≤ lin.p then lin.smul a else lin.smul b).toInt : ℤ)) : ℝ)
      ≤ ((lin.toInt : ℤ) : ℝ) * x := by
  split_ifs with h
  · rw [SInt.toInt_smul]; push_cast
    have : (0 : ℝ) ≤ ((lin.toInt : ℤ) : ℝ) := by
      have : 0 ≤ lin.toInt := by simp only [SInt.toInt]; omega
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_left ha this
  · rw [SInt.toInt_smul]; push_cast
    have : ((lin.toInt : ℤ) : ℝ) ≤ 0 := by
      have : lin.toInt ≤ 0 := by simp only [SInt.toInt]; omega
      exact_mod_cast this
    exact mul_le_mul_of_nonpos_left hb this

/-- The affine bound: `valOf` is below the right side for the labeling `m`. -/
theorem stage2 (tab : Array ℕ) (ed : Array Edge) (lo hi : Array ℕ) (u : ℕ → ℝ)
    (haff : AffOK tab ed u) (hu : InBox lo hi u) (m : ℕ) :
    (((valOf lo hi (wkArr (affArr tab ed)) (woArr (affArr tab ed)) (paArr lo hi) m).toInt
        : ℤ) : ℝ) ≤ rhsR u m := by
  set af := affArr tab ed with haf
  set S : ℕ → ℕ → ℝ := fun i j => (((w3At (wkArr af) (bit m i + bit m j) i j).toInt : ℤ) : ℝ)
    with hS
  set O : ℕ → ℕ → ℝ := fun i j => (((w3At (woArr af) (bit m i + bit m j) i j).toInt : ℤ) : ℝ)
    with hO
  set Ps : ℕ → ℝ := fun r => (((paAt (paArr lo hi) r (bit m r + bit m (r + 1))).s.toInt : ℤ) : ℝ)
    with hPs
  set Po : ℕ → ℝ := fun r => (((paAt (paArr lo hi) r (bit m r + bit m (r + 1))).o.toInt : ℤ) : ℝ)
    with hPo
  -- the value is the intercept plus the corner terms
  have hval : (((valOf lo hi (wkArr af) (woArr af) (paArr lo hi) m).toInt : ℤ) : ℝ)
      ≤ ∑ r ∈ range 7, Po r + ∑ j ∈ range 8, ∑ i ∈ range j, O i j
        + ∑ r ∈ range 7, (2 * (cP : ℝ) + Ps r
          + ∑ i ∈ range (r + 1), ∑ k ∈ range (7 - r), S i (r + 1 + k)) * u r := by
    unfold valOf
    simp only [SInt.toInt_add, toInt_ssumTo, Int.cast_add, Int.cast_sum]
    refine add_le_add le_rfl (sum_le_sum fun r hr => ?_)
    refine (corner_le _ _ _ _ (hu r (mem_range.1 hr)).1 (hu r (mem_range.1 hr)).2).trans
      (le_of_eq ?_)
    simp only [SInt.toInt_add, SInt.toInt_ofNat, toInt_ssumTo, Int.cast_add, Int.cast_sum]
    push_cast
    rfl
  have hsplit : ∑ r ∈ range 7, (2 * (cP : ℝ) + Ps r
        + ∑ i ∈ range (r + 1), ∑ k ∈ range (7 - r), S i (r + 1 + k)) * u r
      = 2 * (cP : ℝ) * ∑ r ∈ range 7, u r + ∑ r ∈ range 7, Ps r * u r
        + ∑ j ∈ range 8, ∑ i ∈ range j, S i j * dist u i j := by
    rw [← sum_dist S u, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun r _ => by ring
  rw [hsplit] at hval
  -- the potentials
  have hpot : ∑ r ∈ range 7, (Ps r * u r + Po r)
      ≤ 2 * ∑ r ∈ range 7, betN r (bit m r + bit m (r + 1)) (u r) := by
    rw [mul_sum]
    refine sum_le_sum fun r hr => ?_
    have h1 := bit_lt_two m r
    have h2 := bit_lt_two m (r + 1)
    exact paff_box lo hi u hu r _ (mem_range.1 hr) (by omega)
  -- the kernel terms
  have hker : ∑ j ∈ range 8, ∑ i ∈ range j, (S i j * dist u i j + O i j)
      ≤ 2 * ∑ j ∈ range 8, ∑ i ∈ range j,
          (wT (bit m i + bit m j) i j : ℝ) * kap (dist u i j) := by
    rw [mul_sum]
    refine sum_le_sum fun j hj => ?_
    rw [mul_sum]
    refine sum_le_sum fun i him => ?_
    have hij := mem_range.1 him
    have hj' := mem_range.1 hj
    have h1 := bit_lt_two m i
    have h2 := bit_lt_two m j
    simp only [hS, hO]
    rw [w3At_wk af _ i j (by omega) hij hj', w3At_wo af _ i j (by omega) hij hj',
      haf, affArr_getD tab ed i j hij hj', SInt.toInt_smul, SInt.toInt_smul]
    have hb := haff i j hij hj'
    have hW : (0 : ℝ) ≤ (wT (bit m i + bit m j) i j : ℝ) := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hb hW
    push_cast
    linear_combination this
  unfold rhsR
  simp only [sum_add_distrib] at hpot hker
  linarith

end Local
end Simple673
