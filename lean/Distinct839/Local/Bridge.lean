/-
Distinct839/Local/Bridge.lean — from the checked root box to the statement `LocalInequality`.

The search proves the scaled inequality `Good u` for all grid points `u` of the root box
`[13926, 209009]⁶` with `∑ u ≤ 209009`. Here we

* check that the integer tables of the checker are those of `Distinct839/Defs.lean`
  (`hT_eq`, `wT_eq`, `knot_eq`, by kernel evaluation);
* code a labeling `lab : Fin 7 → Fin 2` as a number `< 128` (`code`, `bit_code`);
* translate gaps `g_r ≥ 17/20` to grid units `u_r = 16384 g_r ≥ 13926`, use the pressure bound
  when `∑ u ≥ 209009`, and divide the scaled inequality by `2 · 10⁶ · 2²⁸`
  (`localInequality_of_boxOK`).
-/
import Distinct839.Local.Search

open Finset

namespace Distinct839
namespace Local

/-! ## The tables of the checker are the tables of `Defs` -/

theorem hT_eq : ∀ (a : Fin 2) (i : Fin 7), (hT a.val i.val : ℤ) = hTab a i := by decide +kernel

theorem wT_eq : ∀ (t : Fin 3) (i j : Fin 7), (wT t.val i.val j.val : ℤ) = Wtab t i j := by
  decide +kernel

theorem knot_eq : ∀ (r : Fin 6) (t : Fin 3) (k : Fin 14),
    (knot r.val t.val k.val).toInt = knotTab r t k := by decide +kernel

/-! ## Labelings -/

/-- The code of a labeling: bit `i` is the label of site `i`. -/
def code (lab : Fin 7 → Fin 2) : ℕ := ∑ i : Fin 7, (lab i).val * 2 ^ i.val

theorem code_lt (lab : Fin 7 → Fin 2) : code lab < 128 := by
  unfold code
  simp only [Fin.sum_univ_seven]
  have := (lab 0).isLt; have := (lab 1).isLt; have := (lab 2).isLt; have := (lab 3).isLt
  have := (lab 4).isLt; have := (lab 5).isLt; have := (lab 6).isLt
  norm_num
  omega

theorem bit_code (lab : Fin 7 → Fin 2) (i : Fin 7) : bit (code lab) i.val = (lab i).val := by
  unfold code bit
  simp only [Fin.sum_univ_seven, Nat.shiftRight_eq_div_pow]
  have := (lab 0).isLt; have := (lab 1).isLt; have := (lab 2).isLt; have := (lab 3).isLt
  have := (lab 4).isLt; have := (lab 5).isLt; have := (lab 6).isLt
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => norm_num; omega

/-! ## Sums over `Fin` and over `range` -/

theorem sum_pairs (F : ℕ → ℕ → ℝ) :
    ∑ i : Fin 7, ∑ j : Fin 7, (if i < j then F i.val j.val else 0)
      = ∑ j ∈ range 7, ∑ i ∈ range j, F i j := by
  have h1 : ∀ i : ℕ, ∑ j : Fin 7, (if i < j.val then F i j.val else 0)
      = ∑ j ∈ range 7, (if i < j then F i j else 0) :=
    fun i => Fin.sum_univ_eq_sum_range (fun j => if i < j then F i j else 0) 7
  have h2 : ∑ i : Fin 7, ∑ j ∈ range 7, (if i.val < j then F i.val j else 0)
      = ∑ i ∈ range 7, ∑ j ∈ range 7, (if i < j then F i j else 0) :=
    Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range 7, (if i < j then F i j else 0)) 7
  simp only [Fin.lt_def, h1, h2]
  simp only [sum_range_succ, sum_range_zero]
  norm_num
  ring

/-! ## Grid units -/

/-- The gaps in grid units, as a function on `ℕ` (zero beyond the sixth). -/
noncomputable def gridU (gp : Fin 6 → ℝ) (r : ℕ) : ℝ :=
  if h : r < 6 then (gridH : ℝ) * gp ⟨r, h⟩ else 0

theorem gridU_fin (gp : Fin 6 → ℝ) (r : Fin 6) : gridU gp r.val = (gridH : ℝ) * gp r := by
  unfold gridU; rw [dif_pos r.isLt]

theorem sum_gridU (gp : Fin 6 → ℝ) :
    ∑ r ∈ range 6, gridU gp r = (gridH : ℝ) * ∑ r : Fin 6, gp r := by
  rw [← Fin.sum_univ_eq_sum_range (gridU gp) 6, mul_sum]
  exact sum_congr rfl fun r _ => gridU_fin gp r

/-- The position of site `i` in grid units is a partial sum of the gaps. -/
theorem pos_eq (gp : Fin 6 → ℝ) (i : Fin 7) :
    (gridH : ℝ) * pos gp i = ∑ r ∈ range i.val, gridU gp r := by
  unfold pos
  rw [mul_sum]
  have h1 : ∑ r : Fin 6, (gridH : ℝ) * (if r.val < i.val then gp r else 0)
      = ∑ r : Fin 6, (if r.val < i.val then gridU gp r.val else 0) :=
    sum_congr rfl fun r _ => by rw [gridU_fin]; split_ifs <;> simp
  rw [h1, Fin.sum_univ_eq_sum_range (fun r => if r < i.val then gridU gp r else 0) 6,
    ← sum_filter]
  congr 1
  ext r
  simp only [mem_filter, mem_range]
  have := i.isLt
  omega

theorem dist_eq (gp : Fin 6 → ℝ) (i j : Fin 7) (hij : i ≤ j) :
    dist (gridU gp) i.val j.val = (gridH : ℝ) * (pos gp j - pos gp i) := by
  rw [mul_sub, pos_eq, pos_eq, dist, ← sum_Ico_eq_sum_range, sum_Ico_eq_sub _ hij]

theorem kap_dist (gp : Fin 6 → ℝ) (i j : Fin 7) (hij : i ≤ j) :
    kap (dist (gridU gp) i.val j.val) = (scaleV : ℝ) * K (pos gp j - pos gp i) ^ 2 := by
  unfold kap
  rw [dist_eq gp i j hij, mul_div_cancel_left₀ _ (by norm_num [gridH] : (gridH : ℝ) ≠ 0)]

/-- The potentials of the checker are the potentials of `Defs`, scaled by `10⁶ V`. -/
theorem betN_eq (r : Fin 6) (t : Fin 3) (x : ℝ) :
    betN r.val t.val ((gridH : ℝ) * x) = 1000000 * (cV : ℝ) * Bpot r t x := by
  unfold betN Bpot
  rw [← Fin.sum_univ_eq_sum_range (fun k => (((knot r.val t.val k).toInt : ℤ) : ℝ) * (cV : ℝ)
    * hat (((gridH : ℝ) * x - knotX k) / 2048)) 14, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [knot_eq r t k]
  have e : ((gridH : ℝ) * x - knotX k.val) / 2048 = 8 * (x - (3 / 4 + (k.val : ℝ) / 8)) := by
    unfold knotX
    norm_num [gridH]
    ring
  rw [e]
  ring

/-! ## The local inequality -/

/-- If the scaled inequality holds on the root box (for `∑ u ≤ R`), then the local inequality
of `Defs` holds for all gaps `≥ 17/20` and all labelings. -/
theorem localInequality_of_boxOK (h : BoxOK rootLo rootHi) : LocalInequality := by
  intro gp lab hsep
  have hU0 : ∀ r < 6, (13926 : ℝ) ≤ gridU gp r := by
    intro r hr
    have h1 := hsep ⟨r, hr⟩
    unfold gridU
    rw [dif_pos hr]
    unfold sep at h1
    norm_num [gridH]
    linarith
  have hgood : Good (gridU gp) := by
    by_cases hs : (cR : ℝ) ≤ ∑ r ∈ range 6, gridU gp r
    · exact good_of_sum_ge _ hs
    · have hs' := (not_le.1 hs).le
      refine h _ (fun r hr => ⟨?_, ?_⟩) hs'
      · have e : g rootLo r = 13926 := by interval_cases r <;> rfl
        rw [e]
        exact_mod_cast hU0 r hr
      · have e : g rootHi r = cR := by interval_cases r <;> rfl
        rw [e]
        refine le_trans ?_ hs'
        exact single_le_sum (f := gridU gp)
          (fun s hs => le_trans (by norm_num) (hU0 s (mem_range.1 hs))) (mem_range.2 hr)
  have hm := hgood (code lab) (code_lt lab)
  -- the rewards
  have e1 : (rhsOf (code lab) : ℝ)
      = 2 * 1000000 * (cV : ℝ) * ∑ i : Fin 7, (hTab (lab i) i : ℝ) / 1000000 := by
    unfold rhsOf
    rw [sumTo_eq]
    push_cast
    rw [← Fin.sum_univ_eq_sum_range (fun i => (hT (bit (code lab) i) i : ℝ)) 7, mul_sum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [bit_code lab i]
    have e : ((hT (lab i).val i.val : ℕ) : ℝ) = ((hTab (lab i) i : ℤ) : ℝ) := by
      rw [← hT_eq (lab i) i]
      exact (Int.cast_natCast _).symm
    rw [e]
    ring
  -- the pressure
  have e2 : 2 * (cP : ℝ) * ∑ r ∈ range 6, gridU gp r
      = 2 * 1000000 * (cV : ℝ) * (alphaP * ∑ r : Fin 6, gp r) := by
    rw [sum_gridU]
    unfold alphaP
    norm_num [cP, cV, gridH]
    ring
  -- the kernel terms
  have e3 : ∑ j ∈ range 7, ∑ i ∈ range j,
        (wT (bit (code lab) i + bit (code lab) j) i j : ℝ) * kap (dist (gridU gp) i j)
      = 1000000 * (cV : ℝ) * ∑ i : Fin 7, ∑ j : Fin 7,
          (if i < j then (Wtab (pairTy (lab i) (lab j)) i j : ℝ) / 1000000
            * K (pos gp j - pos gp i) ^ 2 else 0) := by
    rw [← sum_pairs (fun i j => (wT (bit (code lab) i + bit (code lab) j) i j : ℝ)
      * kap (dist (gridU gp) i j)), mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · rw [bit_code lab i, bit_code lab j, kap_dist gp i j hij.le]
      have e : ((wT ((lab i).val + (lab j).val) i.val j.val : ℕ) : ℝ)
          = ((Wtab (pairTy (lab i) (lab j)) i j : ℤ) : ℝ) := by
        rw [← wT_eq (pairTy (lab i) (lab j)) i j]
        exact (Int.cast_natCast _).symm
      rw [e]
      have hV : (scaleV : ℝ) = (cV : ℝ) := by norm_num [scaleV, cV]
      rw [hV]
      ring
    · simp
  -- the potentials
  have e4 : ∑ r ∈ range 6, betN r (bit (code lab) r + bit (code lab) (r + 1)) (gridU gp r)
      = 1000000 * (cV : ℝ) * ∑ r : Fin 6,
          Bpot r (pairTy (lab r.castSucc) (lab r.succ)) (gp r) := by
    rw [← Fin.sum_univ_eq_sum_range (fun r => betN r (bit (code lab) r + bit (code lab) (r + 1))
      (gridU gp r)) 6, mul_sum]
    refine sum_congr rfl fun r _ => ?_
    have b1 : bit (code lab) r.val = (lab r.castSucc).val := bit_code lab r.castSucc
    have b2 : bit (code lab) (r.val + 1) = (lab r.succ).val := bit_code lab r.succ
    rw [b1, b2, gridU_fin]
    exact betN_eq r (pairTy (lab r.castSucc) (lab r.succ)) (gp r)
  unfold rhsR at hm
  rw [e1, e2, e3, e4] at hm
  have hV : (0 : ℝ) < (cV : ℝ) := Nat.cast_pos.2 (by decide +kernel)
  have hpos : (0 : ℝ) < 2 * 1000000 * (cV : ℝ) := by linarith
  refine le_of_mul_le_mul_left ?_ hpos
  linarith

end Local
end Distinct839
