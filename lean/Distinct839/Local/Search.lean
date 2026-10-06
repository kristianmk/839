/-
Distinct839/Local/Search.lean — soundness of the branch and bound.

* `node_ok`: a box that `node` accepts satisfies the inequality (on its part with `∑ u ≤ R`);
* `node_split`: the two halves produced by a split cover that part of the box;
* `searchBox_sound`, `searchPath_sound`: the search and the search below all paths of a given
  depth, for an abstract verdict function;
* `checkAll_sound`, `checkChunks_sound`: the two with the verdicts of `node`.
-/
import Distinct839.Local.Node

open Finset

namespace Distinct839
namespace Local

theorem rhsOf_zero : rhsOf 0 = 2 * cH1 * cV := by
  unfold rhsOf
  simp only [bit_zero, sum_h0]
  ring

/-- The halves of a box split at `mid` in coordinate `r` cover the box. -/
theorem inBox_split (lo hi : Array ℕ) (r mid : ℕ) (u : ℕ → ℝ) (hu : InBox lo hi u) :
    InBox lo (hi.setIfInBounds r mid) u ∨ InBox (lo.setIfInBounds r mid) hi u := by
  by_cases h : u r ≤ mid
  · left
    intro k hk
    refine ⟨(hu k hk).1, ?_⟩
    rw [g_setIfInBounds]
    split_ifs with h'
    · rw [← h'.1]; exact h
    · exact (hu k hk).2
  · right
    intro k hk
    refine ⟨?_, (hu k hk).2⟩
    rw [g_setIfInBounds]
    split_ifs with h'
    · rw [← h'.1]; exact (not_le.1 h).le
    · exact (hu k hk).1

/-- A box accepted by `node` satisfies the inequality. -/
theorem node_ok (tab : Array ℕ) (htab : TabOK tab) (lo hi : Array ℕ) (st : ℕ)
    (h : node tab (sparse tab) lo hi = .ok st) : BoxOK lo hi := by
  intro u hu hsum
  have hu' := inBox_clamp lo hi u hu hsum
  obtain ⟨hed, haff⟩ := edges_ok tab htab lo _ u hu' hsum
  unfold node at h
  dsimp only at h
  split_ifs at h with h0 h1 h2 h3
  · -- pressure
    apply good_of_pressure
    have e : (((cH2 + cBudget) * cV : ℕ) : ℝ) ≤ ((sumTo (g lo) 6 * cP : ℕ) : ℝ) := by
      exact_mod_cast h0
    push_cast at e
    have ht := total_le lo u (fun r hr => (hu r hr).1)
    have hP : (0 : ℝ) ≤ cP := Nat.cast_nonneg _
    nlinarith
  · -- range minima and the label shortcut
    intro m _
    have hs := shortcut _ lo _ u hed hu' m
    have h1' := stage1 _ lo _ u hed hu'
    rw [SInt.le_iff, SInt.toInt_add, SInt.toInt_smul, SInt.toInt_ofNat] at h1
    have e := (Int.cast_le (R := ℝ)).2 h1
    push_cast at e
    rw [rhsOf_zero] at hs
    push_cast at hs
    linarith
  · -- affine bounds
    intro m hm
    have hs := shortcut _ lo _ u hed hu' m
    rw [rhsOf_zero] at hs
    push_cast at hs
    rw [Bool.and_eq_true] at h2
    have h4 := h2.2
    unfold affineOK at h4
    dsimp only at h4
    rw [Bool.or_eq_true] at h4
    rcases h4 with h5 | h5
    · have h6 := stage2 tab _ lo _ u haff hu' 0
      rw [SInt.le_iff, SInt.toInt_add, SInt.toInt_ofNat] at h5
      have e := (Int.cast_le (R := ℝ)).2 h5
      push_cast at e
      linarith
    · have h6 := allFromTo_spec _ 128 0 h5 m (Nat.zero_le _) (by omega)
      rw [SInt.le_iff, SInt.toInt_ofNat] at h6
      have e := (Int.cast_le (R := ℝ)).2 h6
      have h7 := stage2 tab _ lo _ u haff hu' m
      push_cast at e
      linarith

/-- The halves of a split box cover its part with `∑ u ≤ R`. -/
theorem node_split (tab : Array ℕ) (lo hi hi' : Array ℕ) (r mid : ℕ)
    (h : node tab (sparse tab) lo hi = .split hi' r mid) (u : ℕ → ℝ) (hu : InBox lo hi u)
    (hsum : ∑ s ∈ range 6, u s ≤ cR) :
    InBox lo (hi'.setIfInBounds r mid) u ∨ InBox (lo.setIfInBounds r mid) hi' u := by
  have hu' := inBox_clamp lo hi u hu hsum
  unfold node at h
  dsimp only at h
  split_ifs at h
  injection h with e1 e2 e3
  subst e1 e2 e3
  exact inBox_split _ _ _ _ u hu'

/-! ## The generic search -/

/-- Soundness of the branch and bound, for any verdict function whose acceptances are correct
and whose splits cover. -/
theorem searchBox_sound (nd : Array ℕ → Array ℕ → Verdict)
    (hok : ∀ lo hi st, nd lo hi = .ok st → BoxOK lo hi)
    (hsplit : ∀ lo hi hi' r mid, nd lo hi = .split hi' r mid → ∀ u, InBox lo hi u →
      ∑ s ∈ range 6, u s ≤ cR →
      InBox lo (hi'.setIfInBounds r mid) u ∨ InBox (lo.setIfInBounds r mid) hi' u) :
    ∀ fuel lo hi, searchBox nd fuel lo hi = true → BoxOK lo hi := by
  intro fuel
  induction fuel with
  | zero => intro lo hi h; exact absurd h (by simp [searchBox])
  | succ fuel ih =>
    intro lo hi h
    rw [searchBox] at h
    generalize hn : nd lo hi = v at h
    cases v with
    | ok st => exact hok lo hi st hn
    | fail => exact absurd h (by simp)
    | split hi' r mid =>
      simp only [Bool.and_eq_true] at h
      intro u hu hsum
      rcases hsplit lo hi hi' r mid hn u hu hsum with h1 | h1
      · exact ih _ _ h.1 u h1 hsum
      · exact ih _ _ h.2 u h1 hsum

/-- Soundness of the search below all paths of a given depth. -/
theorem searchPath_sound (nd : Array ℕ → Array ℕ → Verdict)
    (hok : ∀ lo hi st, nd lo hi = .ok st → BoxOK lo hi)
    (hsplit : ∀ lo hi hi' r mid, nd lo hi = .split hi' r mid → ∀ u, InBox lo hi u →
      ∑ s ∈ range 6, u s ≤ cR →
      InBox lo (hi'.setIfInBounds r mid) u ∨ InBox (lo.setIfInBounds r mid) hi' u)
    (fuel : ℕ) :
    ∀ depth lo hi, (∀ p < 2 ^ depth, searchPath nd fuel depth p lo hi = true) →
      BoxOK lo hi := by
  intro depth
  induction depth with
  | zero =>
    intro lo hi h
    have h0 := h 0 (by norm_num)
    rw [searchPath] at h0
    exact searchBox_sound nd hok hsplit fuel lo hi h0
  | succ depth ih =>
    intro lo hi h
    have key : ∀ p < 2 ^ (depth + 1),
        (match nd lo hi with
          | .ok _ => true
          | .fail => false
          | .split hi' r mid =>
            if p % 2 = 0 then searchPath nd fuel depth (p / 2) lo (hi'.setIfInBounds r mid)
            else searchPath nd fuel depth (p / 2) (lo.setIfInBounds r mid) hi') = true := by
      intro p hp
      have h0 := h p hp
      rw [searchPath] at h0
      exact h0
    generalize hn : nd lo hi = v at key
    cases v with
    | ok st => exact hok lo hi st hn
    | fail => exact absurd (key 0 (by positivity)) (by simp)
    | split hi' r mid =>
      have h1 : BoxOK lo (hi'.setIfInBounds r mid) := by
        refine ih _ _ fun p hp => ?_
        have h0 := key (2 * p) (by rw [pow_succ]; omega)
        have e1 : 2 * p % 2 = 0 := by omega
        have e2 : 2 * p / 2 = p := by omega
        simpa only [e1, e2, if_true] using h0
      have h2 : BoxOK (lo.setIfInBounds r mid) hi' := by
        refine ih _ _ fun p hp => ?_
        have h0 := key (2 * p + 1) (by rw [pow_succ]; omega)
        have e1 : ¬ (2 * p + 1) % 2 = 0 := by omega
        have e2 : (2 * p + 1) / 2 = p := by omega
        simpa only [e1, e2, if_false] using h0
      intro u hu hsum
      rcases hsplit lo hi hi' r mid hn u hu hsum with h3 | h3
      · exact h1 u h3 hsum
      · exact h2 u h3 hsum

/-! ## The search with the verdicts of `node` -/

/-- If every chunk `i < n` passes, the root box is checked. -/
theorem checkChunks_sound (tab : Array ℕ) (htab : TabOK tab) (depth n : ℕ) (hn : 0 < n)
    (h : ∀ i < n, checkChunk tab depth n i = true) : BoxOK rootLo rootHi := by
  refine searchPath_sound (node tab (sparse tab)) (node_ok tab htab) (node_split tab) cFuel depth
    rootLo rootHi fun p hp => ?_
  have h0 := h (p % n) (Nat.mod_lt _ hn)
  unfold checkChunk at h0
  have h1 := allFromTo_spec _ _ 0 h0 p (Nat.zero_le _) (by omega)
  simpa using h1

/-- The single check `checkAll` covers the root box. -/
theorem checkAll_sound (tab : Array ℕ) (htab : TabOK tab) (h : checkAll tab = true) :
    BoxOK rootLo rootHi := by
  unfold checkAll at h
  exact searchBox_sound (node tab (sparse tab)) (node_ok tab htab) (node_split tab) cFuel
    rootLo rootHi h

end Local
end Distinct839
