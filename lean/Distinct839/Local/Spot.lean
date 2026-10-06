/-
Distinct839/Local/Spot.lean — the range-minimum test on a single box, for the kernel
(spot-checks, not used by the proof).

The complete check of the local inequality is evaluated by compiled code (`native_decide`,
`Distinct839/Local/RunAll.lean`). The Lean kernel cannot evaluate it: the table has 209010
entries, each costing the kernel about 0.1 s, and kernel arrays are lists. What the kernel can
do is check one small box, reading the table as the function `kTab` and taking range minima by
direct evaluation. This file provides the tools:

* `basicF f lo hi` is the range-minimum test of `node` (its second test, the one that accepts
  about 70% of the terminal boxes of the search), with the table given as a function
  `f : ℕ → ℕ`;
* `basicF_sound`: if `f` is a sound table and `basicF f lo hi = true`, the local inequality
  holds on the box (`BoxOK lo hi`), by the same lemmas as for `node`.

`Distinct839/Local/SpotChecks.lean` applies this to four small boxes of the domain.
-/
import Distinct839.Local.Search
import Distinct839.Kernel.Sound

open Finset

namespace Distinct839
namespace Local

/-- `min acc (min (f l) … (f (l + n - 1)))`, by direct evaluation. (The comparison in each step
makes the kernel evaluate the running minimum, so that no long chain of suspended `min`s
builds up.) -/
def minF (f : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | n + 1, l, acc => if f l ≤ acc then minF f n (l + 1) (f l) else minF f n (l + 1) acc

theorem minF_le_acc (f : ℕ → ℕ) : ∀ n l acc, minF f n l acc ≤ acc := by
  intro n
  induction n with
  | zero => intro l acc; exact le_rfl
  | succ n ih =>
    intro l acc
    rw [minF]
    split_ifs with h
    · exact (ih _ _).trans h
    · exact ih _ _

theorem minF_le (f : ℕ → ℕ) : ∀ n l acc c, l ≤ c → c < l + n → minF f n l acc ≤ f c := by
  intro n
  induction n with
  | zero => intro l acc c h1 h2; omega
  | succ n ih =>
    intro l acc c h1 h2
    rw [minF]
    rcases Nat.eq_or_lt_of_le h1 with rfl | h3
    · split_ifs with h
      · exact minF_le_acc f n _ _
      · exact (minF_le_acc f n _ _).trans (not_le.1 h).le
    · split_ifs with h
      · exact ih _ _ c h3 (by omega)
      · exact ih _ _ c h3 (by omega)

/-- The edge data of `mkEdge`, with the kernel bound taken directly from a table function. -/
def mkEdgeF (f : ℕ → ℕ) (lo hi : Array ℕ) (total i j : ℕ) : Edge :=
  let l := sumTo (fun k => g lo (i + k)) (j - i)
  let h := min (sumTo (fun k => g hi (i + k)) (j - i)) (cR + l - total)
  let last := max l (h - 1)
  ⟨l, last, minF f (last + 1 - l) l (f l)⟩

/-- Edge data for all pairs, index `i * 7 + j`. -/
def edgesF (f : ℕ → ℕ) (lo hi : Array ℕ) (total : ℕ) : Array Edge :=
  Array.ofFn (n := 49) fun q =>
    if q.val / 7 < q.val % 7 then mkEdgeF f lo hi total (q.val / 7) (q.val % 7) else ⟨0, 0, 0⟩

/-- The range-minimum test of `node`, with the table given as a function. -/
def basicF (f : ℕ → ℕ) (lo hi : Array ℕ) : Bool :=
  let total := sumTo (g lo) 6
  let hi' := clamp lo hi total
  let ed := edgesF f lo hi' total
  let bm := bmArr lo hi'
  (SInt.ofNat (2 * cH1 * cV)).le (((baseOf total ed bm).smul 2).add (penalty (incArr ed bm)))

theorem edAt_edgesF (f : ℕ → ℕ) (lo hi : Array ℕ) (total i j : ℕ) (hij : i < j) (hj : j < 7) :
    edAt (edgesF f lo hi total) i j = mkEdgeF f lo hi total i j := by
  unfold edAt edgesF
  rw [getD_ofFn _ _ _ (by omega)]
  have h1 : (i * 7 + j) / 7 = i := by omega
  have h2 : (i * 7 + j) % 7 = j := by omega
  simp only [h1, h2, if_pos hij]

/-- A sound table function bounds `kap` on its cells. -/
theorem kap_ge_of_tableSound (f : ℕ → ℕ) (hf : TableSound f) (k : ℕ) (d : ℝ) (h1 : (k : ℝ) ≤ d)
    (h2 : d ≤ k + 1) : ((f k : ℕ) : ℝ) ≤ kap d := by
  have hH : (0 : ℝ) < (gridH : ℝ) := by norm_num [gridH]
  have hV : (0 : ℝ) < (scaleV : ℝ) := by norm_num [scaleV]
  have h := hf k (d / gridH) (div_le_div_of_nonneg_right h1 hH.le)
    (div_le_div_of_nonneg_right h2 hH.le)
  rw [div_le_iff₀ hV] at h
  unfold kap
  linarith

/-- If the range-minimum test passes for a sound table function, the local inequality holds on
the box. -/
theorem basicF_sound (f : ℕ → ℕ) (hf : TableSound f) (lo hi : Array ℕ)
    (h : basicF f lo hi = true) : BoxOK lo hi := by
  intro u hu hsum
  have hu' := inBox_clamp lo hi u hu hsum
  have hed : EdOK (edgesF f lo (clamp lo hi (sumTo (g lo) 6)) (sumTo (g lo) 6)) u := by
    intro i j hij hj
    rw [edAt_edgesF _ _ _ _ i j hij hj]
    obtain ⟨k, hk1, hk2, hk3, hk4⟩ := dist_cell lo _ u hu' hsum i j hij hj
    simp only [mkEdgeF]
    exact (Nat.cast_le.2 (minF_le f _ _ _ k hk1 (by omega))).trans
      (kap_ge_of_tableSound f hf k _ hk3 hk4)
  intro m _
  have hs := shortcut _ lo _ u hed hu' m
  have h1' := stage1 _ lo _ u hed hu'
  unfold basicF at h
  dsimp only at h
  rw [SInt.le_iff, SInt.toInt_add, SInt.toInt_smul, SInt.toInt_ofNat] at h
  have e := (Int.cast_le (R := ℝ)).2 h
  push_cast at e
  rw [rhsOf_zero] at hs
  push_cast at hs
  linarith

end Local
end Distinct839
