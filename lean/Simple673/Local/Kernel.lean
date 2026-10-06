/-
Simple673/Local/Kernel.lean — the kernel table in the checker: range minima and affine
supports.

`kap d = V · K(d/H)²` is the scaled kernel square at the grid distance `d`. A table is `TabOK`
if `tab[k] ≤ kap d` on the cell `k ≤ d ≤ k + 1` (reads beyond the end give `0`). We prove:

* `rmin_le`: the sparse-table query is a lower bound for the entries in its range;
* `kap_ge_rmin`: hence a lower bound for `kap` on `[l, h]`;
* `kaff_spec`: the affine function computed by `kaff` is below `2 kap` over the cells of an edge.
-/
import Simple673.Defs
import Simple673.Local.Basic

open Finset

namespace Simple673
namespace Local

/-- The scaled kernel square `V · K(d/H)²` at the grid distance `d`. -/
noncomputable def kap (d : ℝ) : ℝ := (scaleV : ℝ) * K (d / gridH) ^ 2

theorem kap_nonneg (d : ℝ) : 0 ≤ kap d := by unfold kap; positivity

/-- `tab[k]` is a lower bound for `kap` on the cell `[k, k + 1]`. -/
def TabOK (tab : Array ℕ) : Prop :=
  ∀ (k : ℕ) (d : ℝ), (k : ℝ) ≤ d → d ≤ k + 1 → ((tab.getD k 0 : ℕ) : ℝ) ≤ kap d

/-- The hypothesis of the soundness theorem, in grid units. -/
theorem tabOK_of_sound (tab : Array ℕ)
    (hsound : ∀ (k : ℕ) (h : k < tab.size) (t : ℝ), (k : ℝ) / gridH ≤ t →
      t ≤ ((k : ℝ) + 1) / gridH → (tab[k] : ℝ) / scaleV ≤ K t ^ 2) : TabOK tab := by
  intro k d h1 h2
  by_cases hk : k < tab.size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some]
    have hH : (0 : ℝ) < (gridH : ℝ) := by norm_num [gridH]
    have hV : (0 : ℝ) < (scaleV : ℝ) := by norm_num [scaleV]
    have h := hsound k hk (d / gridH) (div_le_div_of_nonneg_right h1 hH.le)
      (div_le_div_of_nonneg_right h2 hH.le)
    rw [div_le_iff₀ hV] at h
    unfold kap
    linarith
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none]
    simpa using kap_nonneg d

/-! ## Range minima -/

/-- `lev` is a lower bound for the minima of the windows of length `2^k`. -/
def LevOK (tab : Array ℕ) (k : ℕ) (lev : Array ℕ) : Prop :=
  ∀ l d, d < 2 ^ k → lev.getD l 0 ≤ tab.getD (l + d) 0

theorem levOK_zero (tab : Array ℕ) : LevOK tab 0 tab := by
  intro l d hd
  have : d = 0 := by simpa using hd
  subst this; exact le_rfl

theorem levOK_empty (tab : Array ℕ) (k : ℕ) : LevOK tab k #[] := by
  intro l d _; simp

theorem nextLevel_getD_le (prev : Array ℕ) (s i : ℕ) :
    (nextLevel prev s).getD i 0 ≤ min (prev.getD i 0) (prev.getD (i + s) 0) := by
  unfold nextLevel
  by_cases h : i < prev.size
  · rw [getD_ofFn _ _ _ h]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simpa using h),
      Option.getD_none]
    exact Nat.zero_le _

theorem levOK_next (tab : Array ℕ) (k : ℕ) (lev : Array ℕ) (h : LevOK tab k lev) :
    LevOK tab (k + 1) (nextLevel lev (2 ^ k)) := by
  intro l d hd
  have h1 := nextLevel_getD_le lev (2 ^ k) l
  rw [pow_succ] at hd
  by_cases hc : d < 2 ^ k
  · exact (h1.trans (min_le_left _ _)).trans (h l d hc)
  · have h2 := h (l + 2 ^ k) (d - 2 ^ k) (by omega)
    have e : l + 2 ^ k + (d - 2 ^ k) = l + d := by omega
    rw [e] at h2
    exact (h1.trans (min_le_right _ _)).trans h2

theorem sparseAux_ok (tab : Array ℕ) :
    ∀ n k cur acc, LevOK tab k cur → acc.size = k → (∀ j, LevOK tab j (acc.getD j #[])) →
      ∀ j, LevOK tab j ((sparseAux n k cur acc).getD j #[]) := by
  intro n
  induction n with
  | zero => intro k cur acc _ _ h; exact h
  | succ n ih =>
    intro k cur acc hcur hsize hacc
    rw [sparseAux]
    refine ih (k + 1) _ _ (levOK_next tab k cur hcur) (by simp [hsize]) ?_
    intro j
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_push]
    by_cases hj : j = acc.size
    · rw [if_pos hj, Option.getD_some, hj, hsize]; exact hcur
    · rw [if_neg hj, ← Array.getD_eq_getD_getElem?]; exact hacc j

theorem sparse_ok (tab : Array ℕ) (j : ℕ) : LevOK tab j ((sparse tab).getD j #[]) :=
  sparseAux_ok tab 18 0 tab #[] (levOK_zero tab) rfl (fun j => by simpa using levOK_empty tab j) j

/-- The range-minimum query is a lower bound for every entry in its range. -/
theorem rmin_le (tab : Array ℕ) (l r c : ℕ) (h1 : l ≤ c) (h2 : c ≤ r) :
    rmin (sparse tab) l r ≤ tab.getD c 0 := by
  have hn : r + 1 - l ≠ 0 := by omega
  have hp1 := Nat.log2_self_le hn
  have hp2 := Nat.lt_log2_self (n := r + 1 - l)
  have hlev : ∀ i d, d < 2 ^ (r + 1 - l).log2 →
      ((sparse tab).getD (r + 1 - l).log2 #[]).getD i 0 ≤ tab.getD (i + d) 0 :=
    sparse_ok tab _
  show min (((sparse tab).getD (r + 1 - l).log2 #[]).getD l 0)
      (((sparse tab).getD (r + 1 - l).log2 #[]).getD (r + 1 - 2 ^ (r + 1 - l).log2) 0) ≤ _
  generalize (sparse tab).getD (r + 1 - l).log2 #[] = lev at hlev ⊢
  generalize (r + 1 - l).log2 = k at hp1 hp2 hlev ⊢
  rw [pow_succ] at hp2
  generalize 2 ^ k = p at hp1 hp2 hlev ⊢
  by_cases hc : c - l < p
  · have h3 := hlev l (c - l) hc
    rw [show l + (c - l) = c by omega] at h3
    exact (min_le_left _ _).trans h3
  · have h3 := hlev (r + 1 - p) (c - (r + 1 - p)) (by omega)
    rw [show r + 1 - p + (c - (r + 1 - p)) = c by omega] at h3
    exact (min_le_right _ _).trans h3

/-- A real number in `[l, h]` lies in one of the cells `l, …, max l (h - 1)`. -/
theorem exists_cell (l h : ℕ) (d : ℝ) (h1 : (l : ℝ) ≤ d) (h2 : d ≤ h) :
    ∃ k : ℕ, l ≤ k ∧ k ≤ max l (h - 1) ∧ (k : ℝ) ≤ d ∧ d ≤ k + 1 := by
  have hd0 : (0 : ℝ) ≤ d := (Nat.cast_nonneg l).trans h1
  by_cases hf : ⌊d⌋₊ < h
  · refine ⟨⌊d⌋₊, Nat.le_floor h1, ?_, Nat.floor_le hd0, (Nat.lt_floor_add_one d).le⟩
    exact le_max_of_le_right (by omega)
  · have hf' : h ≤ ⌊d⌋₊ := not_lt.1 hf
    have hdh : (h : ℝ) ≤ d := (Nat.cast_le.2 hf').trans (Nat.floor_le hd0)
    have hlh : l ≤ h := by exact_mod_cast h1.trans h2
    by_cases hl : l < h
    · refine ⟨h - 1, by omega, le_max_right _ _, ?_, ?_⟩
      · have : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [this]; linarith
      · have : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [this]; linarith
    · have : l = h := by omega
      subst this
      exact ⟨l, le_rfl, le_max_left _ _, h1, by linarith⟩

/-- The range minimum over the cells of `[l, h]` is a lower bound for `kap` on `[l, h]`. -/
theorem kap_ge_rmin (tab : Array ℕ) (htab : TabOK tab) (l h : ℕ) (d : ℝ) (h1 : (l : ℝ) ≤ d)
    (h2 : d ≤ h) : ((rmin (sparse tab) l (max l (h - 1)) : ℕ) : ℝ) ≤ kap d := by
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := exists_cell l h d h1 h2
  exact (Nat.cast_le.2 (rmin_le tab l _ k hk1 hk2)).trans (htab k d hk3 hk4)

/-! ## Affine supports of the kernel table -/

theorem cellMinDown_le_acc (tab : Array ℕ) (s : ℕ) :
    ∀ n k c acc, cellMinDown tab s n k c acc ≤ acc := by
  intro n
  induction n with
  | zero => intro k c acc; exact le_rfl
  | succ n ih => intro k c acc; rw [cellMinDown]; exact (ih _ _ _).trans (min_le_left _ _)

theorem cellMinDown_le (tab : Array ℕ) (s : ℕ) :
    ∀ n k c acc t, t < n → t ≤ k →
      cellMinDown tab s n k c acc ≤ 2 * tab.getD (k - t) 0 + c + s * t := by
  intro n
  induction n with
  | zero => intro k c acc t ht; omega
  | succ n ih =>
    intro k c acc t ht hk
    rw [cellMinDown]
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · refine (cellMinDown_le_acc tab s _ _ _ _).trans ((min_le_right _ _).trans ?_)
      simp
    · have h := ih (k - 1) (c + s) (min acc (2 * tab.getD k 0 + c)) (t - 1) (by omega) (by omega)
      have e1 : k - 1 - (t - 1) = k - t := by omega
      have e2 : s * (t - 1) + s = s * t := by
        obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        simp [Nat.mul_succ]
      rw [e1] at h
      omega

theorem cellMinUp_le_acc (tab : Array ℕ) (s : ℕ) :
    ∀ n k c acc, cellMinUp tab s n k c acc ≤ acc := by
  intro n
  induction n with
  | zero => intro k c acc; exact le_rfl
  | succ n ih => intro k c acc; rw [cellMinUp]; exact (ih _ _ _).trans (min_le_left _ _)

theorem cellMinUp_le (tab : Array ℕ) (s : ℕ) :
    ∀ n k c acc t, t < n →
      cellMinUp tab s n k c acc ≤ 2 * tab.getD (k + t) 0 + c + s * t := by
  intro n
  induction n with
  | zero => intro k c acc t ht; omega
  | succ n ih =>
    intro k c acc t ht
    rw [cellMinUp]
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · refine (cellMinUp_le_acc tab s _ _ _ _).trans ((min_le_right _ _).trans ?_)
      simp
    · have h := ih (k + 1) (c + s) (min acc (2 * tab.getD k 0 + c)) (t - 1) (by omega)
      have e1 : k + 1 + (t - 1) = k + t := by omega
      have e2 : s * (t - 1) + s = s * t := by
        obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        simp [Nat.mul_succ]
      rw [e1] at h
      omega

/-- The affine function computed by `kaff` is below `2 kap` on every cell of the edge. -/
theorem kaff_spec (tab : Array ℕ) (htab : TabOK tab) (e : Edge) (k : ℕ) (hk1 : e.ls ≤ k)
    (hk2 : k ≤ e.hs) (d : ℝ) (hd1 : (k : ℝ) ≤ d) (hd2 : d ≤ k + 1) :
    (((kaff tab e).s.toInt : ℤ) : ℝ) * d + (((kaff tab e).o.toInt : ℤ) : ℝ) ≤ 2 * kap d := by
  have hcell : ((tab.getD k 0 : ℕ) : ℝ) ≤ kap d := htab k d hd1 hd2
  unfold kaff
  simp only
  generalize (if (e.ls + e.hs) / 2 = 0 ∨ cR ≤ (e.ls + e.hs) / 2 then 0
    else tab.getD ((e.ls + e.hs) / 2 + 1) 0) = a
  generalize (if (e.ls + e.hs) / 2 = 0 ∨ cR ≤ (e.ls + e.hs) / 2 then 0
    else tab.getD ((e.ls + e.hs) / 2 - 1) 0) = b
  split
  · -- nonnegative slope `s = a - b`
    have hM := cellMinDown_le tab (a - b) (e.hs + 1 - e.ls) e.hs 0 (2 * tab.getD e.hs 0)
      (e.hs - k) (by omega) (by omega)
    have e1 : e.hs - (e.hs - k) = k := by omega
    rw [e1] at hM
    have hM' : ((cellMinDown tab (a - b) (e.hs + 1 - e.ls) e.hs 0 (2 * tab.getD e.hs 0) : ℕ) : ℝ)
        ≤ 2 * (tab.getD k 0 : ℕ) + 0 + ((a - b : ℕ) : ℝ) * ((e.hs : ℝ) - k) := by
      have : (((e.hs - k : ℕ) : ℕ) : ℝ) = (e.hs : ℝ) - k := by rw [Nat.cast_sub hk2]
      rw [← this]
      exact_mod_cast hM
    have hs : (0 : ℝ) ≤ ((a - b : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only [SInt.toInt_mk]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hd2 hs]
  · -- negative slope `-(b - a)`
    have hM := cellMinUp_le tab (b - a) (e.hs + 1 - e.ls) e.ls ((b - a) * e.ls)
      (2 * tab.getD e.ls 0 + (b - a) * e.ls) (k - e.ls) (by omega)
    have e1 : e.ls + (k - e.ls) = k := by omega
    rw [e1] at hM
    have hM' : ((cellMinUp tab (b - a) (e.hs + 1 - e.ls) e.ls ((b - a) * e.ls)
        (2 * tab.getD e.ls 0 + (b - a) * e.ls) : ℕ) : ℝ)
        ≤ 2 * (tab.getD k 0 : ℕ) + ((b - a : ℕ) : ℝ) * e.ls
          + ((b - a : ℕ) : ℝ) * ((k : ℝ) - e.ls) := by
      have : (((k - e.ls : ℕ) : ℕ) : ℝ) = (k : ℝ) - e.ls := by rw [Nat.cast_sub hk1]
      rw [← this]
      exact_mod_cast hM
    have hs : (0 : ℝ) ≤ ((b - a : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only [SInt.toInt_mk]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hd1 hs]

end Local
end Simple673
