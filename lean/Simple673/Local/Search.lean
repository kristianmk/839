/-
Simple673/Local/Search.lean — soundness of the branch and bound.

* `node_ok`: a box that `node` accepts satisfies the inequality (on its part with `∑ u ≤ R`);
* `node_split`: the two halves produced by a split cover that part of the box;
* `searchBox_sound`, `searchPath_sound`: the search and the search below all paths of a given
  depth, for an abstract verdict function;
* `checkAll_sound`, `checkChunks_sound`: the two with the verdicts of `node`;
* `frontier_sound`, `searchEvery_sound`, `checkAllPar_sound`: the search cut into parts
  (`checkAllPar`). A task has the value of its function (`Task.spawn f = ⟨f ()⟩`), so nothing
  about threads enters the proof.
-/
import Simple673.Local.Node

open Finset

namespace Simple673
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
    have e : (((cH2 + cBudget) * cV : ℕ) : ℝ) ≤ ((sumTo (g lo) 7 * cP : ℕ) : ℝ) := by
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
    · have h6 := allFromTo_spec _ 256 0 h5 m (Nat.zero_le _) (by omega)
      rw [SInt.le_iff, SInt.toInt_ofNat] at h6
      have e := (Int.cast_le (R := ℝ)).2 h6
      have h7 := stage2 tab _ lo _ u haff hu' m
      push_cast at e
      linarith

/-- The halves of a split box cover its part with `∑ u ≤ R`. -/
theorem node_split (tab : Array ℕ) (lo hi hi' : Array ℕ) (r mid : ℕ)
    (h : node tab (sparse tab) lo hi = .split hi' r mid) (u : ℕ → ℝ) (hu : InBox lo hi u)
    (hsum : ∑ s ∈ range 7, u s ≤ cR) :
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
      ∑ s ∈ range 7, u s ≤ cR →
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
      ∑ s ∈ range 7, u s ≤ cR →
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

/-! ## The search in parallel parts -/

/-- The boxes returned by `frontier` contain the boxes it was given, and if the inequality holds
on each of them, it holds on the box `lo hi`. -/
theorem frontier_sound (nd : Array ℕ → Array ℕ → Verdict)
    (hok : ∀ lo hi st, nd lo hi = .ok st → BoxOK lo hi)
    (hsplit : ∀ lo hi hi' r mid, nd lo hi = .split hi' r mid → ∀ u, InBox lo hi u →
      ∑ s ∈ range 7, u s ≤ cR →
      InBox lo (hi'.setIfInBounds r mid) u ∨ InBox (lo.setIfInBounds r mid) hi' u) :
    ∀ depth lo hi acc bs, frontier nd depth lo hi acc = some bs →
      (∀ b ∈ acc, b ∈ bs) ∧ ((∀ b ∈ bs, BoxOK b.1 b.2) → BoxOK lo hi) := by
  intro depth
  induction depth with
  | zero =>
    intro lo hi acc bs h
    rw [frontier] at h
    injection h with h
    subst h
    exact ⟨fun b hb => List.mem_cons_of_mem _ hb, fun hbs => hbs (lo, hi) List.mem_cons_self⟩
  | succ depth ih =>
    intro lo hi acc bs h
    rw [frontier] at h
    generalize hn : nd lo hi = v at h
    cases v with
    | ok st =>
      injection h with h
      subst h
      exact ⟨fun b hb => hb, fun _ => hok lo hi st hn⟩
    | fail => exact absurd h (by simp)
    | split hi' r mid =>
      dsimp only at h
      generalize h1 : frontier nd depth lo (hi'.setIfInBounds r mid) acc = o at h
      cases o with
      | none => exact absurd h (by simp)
      | some acc' =>
        dsimp only at h
        obtain ⟨hs1, hb1⟩ := ih _ _ _ _ h1
        obtain ⟨hs2, hb2⟩ := ih _ _ _ _ h
        refine ⟨fun b hb => hs2 b (hs1 b hb), fun hbs u hu hsum => ?_⟩
        rcases hsplit lo hi hi' r mid hn u hu hsum with h3 | h3
        · exact hb1 (fun b hb => hbs b (hs2 b hb)) u h3 hsum
        · exact hb2 hbs u h3 hsum

/-- If every part `i < parts` of `searchEvery` passes, the inequality holds on every box of the
list. -/
theorem searchEvery_sound (nd : Array ℕ → Array ℕ → Verdict)
    (hok : ∀ lo hi st, nd lo hi = .ok st → BoxOK lo hi)
    (hsplit : ∀ lo hi hi' r mid, nd lo hi = .split hi' r mid → ∀ u, InBox lo hi u →
      ∑ s ∈ range 7, u s ≤ cR →
      InBox lo (hi'.setIfInBounds r mid) u ∨ InBox (lo.setIfInBounds r mid) hi' u)
    (parts : ℕ) (hparts : 0 < parts) :
    ∀ (bs : List (Array ℕ × Array ℕ)) (k : ℕ),
      (∀ i < parts, searchEvery nd parts i k bs = true) → ∀ b ∈ bs, BoxOK b.1 b.2 := by
  intro bs
  induction bs with
  | nil => intro k _ b hb; exact absurd hb (by simp)
  | cons a bs ih =>
    intro k h b hb
    rcases List.mem_cons.1 hb with rfl | hb'
    · have h0 := h (k % parts) (Nat.mod_lt _ hparts)
      rw [searchEvery, Bool.and_eq_true] at h0
      have h1 : searchBox nd cFuel b.1 b.2 = true := by simpa using h0.1
      exact searchBox_sound nd hok hsplit cFuel _ _ h1
    · refine ih (k + 1) (fun i hi => ?_) b hb'
      have h0 := h i hi
      rw [searchEvery, Bool.and_eq_true] at h0
      exact h0.2

/-- A copy of a table has the entries of the table. -/
theorem getD_copyTab (tab : Array ℕ) (k : ℕ) : (copyTab tab).getD k 0 = tab.getD k 0 := by
  unfold copyTab
  by_cases hk : k < tab.size
  · rw [getD_ofFn _ _ _ hk]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simpa using hk),
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]

theorem tabOK_copyTab (tab : Array ℕ) (htab : TabOK tab) : TabOK (copyTab tab) := by
  intro k d h1 h2
  rw [getD_copyTab]
  exact htab k d h1 h2

/-- The check in parallel parts covers the root box. -/
theorem checkAllPar_sound (tab : Array ℕ) (htab : TabOK tab) (depth parts : ℕ)
    (hparts : 0 < parts) (h : checkAllPar tab depth parts = true) : BoxOK rootLo rootHi := by
  unfold checkAllPar at h
  generalize hf : frontier (node tab (sparse tab)) depth rootLo rootHi [] = o at h
  cases o with
  | none => exact absurd h (by simp)
  | some boxes =>
    dsimp only at h
    rw [List.all_eq_true] at h
    refine (frontier_sound (node tab (sparse tab)) (node_ok tab htab) (node_split tab) depth
      rootLo rootHi [] boxes hf).2 ?_
    refine searchEvery_sound (node (copyTab tab) (sparse (copyTab tab)))
      (node_ok _ (tabOK_copyTab tab htab)) (node_split _) parts hparts boxes 0 fun i hi => ?_
    exact h (Task.spawn (prio := Task.Priority.dedicated) fun _ => checkPart tab boxes parts i)
      (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)

end Local
end Simple673
