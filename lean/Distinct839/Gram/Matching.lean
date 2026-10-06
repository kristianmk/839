/-
Distinct839/Gram/Matching.lean — a maximal matching of close pairs.

Given positions `y : ι → ℝ` on a finite index set and a threshold `d`, a *close matching* is an
involution `σ` of `ι` such that every point moved by `σ` is at distance less than `d` from its
partner. A close matching with the largest number of moved points has a `d`-separated set of
fixed points: two fixed points at distance less than `d` could be matched to each other.
The pairs `{i, σ i}` are the removed pairs of the Gram theorem, the fixed points form the
separated remainder.
-/
import Mathlib

open Finset

namespace Distinct839.Gram

variable {ι : Type*}

/-- `σ` is a close matching for the positions `y` and the threshold `d`: an involution whose
moved points are at distance less than `d` from their partners. -/
structure IsCloseMatching (y : ι → ℝ) (d : ℝ) (σ : ι → ι) : Prop where
  /-- `σ` is an involution -/
  invol : ∀ i, σ (σ i) = i
  /-- partners are close -/
  close : ∀ i, σ i ≠ i → |y i - y (σ i)| < d

lemma IsCloseMatching.id (y : ι → ℝ) (d : ℝ) : IsCloseMatching y d (fun i => i) :=
  ⟨fun _ => rfl, fun _ h => absurd rfl h⟩

/-- Matching two fixed points of a close matching that are close to each other gives a close
matching. -/
lemma IsCloseMatching.addPair [DecidableEq ι] {y : ι → ℝ} {d : ℝ} {σ : ι → ι}
    (hσ : IsCloseMatching y d σ) {i j : ι} (hi : σ i = i) (hj : σ j = j) (hij : i ≠ j)
    (hd : |y i - y j| < d) :
    IsCloseMatching y d (fun x => if x = i then j else if x = j then i else σ x) := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · by_cases hxi : x = i
    · subst hxi
      simp [hij.symm]
    · by_cases hxj : x = j
      · subst hxj
        simp [hxi]
      · have h1 : σ x ≠ i := fun h => hxi (by rw [← hσ.invol x, h, hi])
        have h2 : σ x ≠ j := fun h => hxj (by rw [← hσ.invol x, h, hj])
        simp [hxi, hxj, h1, h2, hσ.invol x]
  · by_cases hxi : x = i
    · subst hxi
      simpa using hd
    · by_cases hxj : x = j
      · subst hxj
        simp only [if_neg hxi, if_true]
        rw [abs_sub_comm]; exact hd
      · simp only [if_neg hxi, if_neg hxj] at hx ⊢
        exact hσ.close x hx

/-- **Maximal matching.** There is a close matching whose fixed points are pairwise at
distance at least `d`. -/
theorem exists_maximal_matching [Fintype ι] [DecidableEq ι] (y : ι → ℝ) (d : ℝ) :
    ∃ σ : ι → ι, IsCloseMatching y d σ ∧
      ∀ i j, σ i = i → σ j = j → i ≠ j → d ≤ |y i - y j| := by
  classical
  -- a close matching with the largest number of moved points
  obtain ⟨σ, hσmem, hσmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun σ : ι → ι => IsCloseMatching y d σ)
    (fun σ => (Finset.univ.filter fun i => σ i ≠ i).card)
    ⟨fun i => i, by simp [IsCloseMatching.id]⟩
  have hσ : IsCloseMatching y d σ := by simpa using hσmem
  refine ⟨σ, hσ, fun i j hi hj hij => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  set τ : ι → ι := fun x => if x = i then j else if x = j then i else σ x with hτ
  have hτm : IsCloseMatching y d τ := hσ.addPair hi hj hij hlt
  have hlt' : (Finset.univ.filter fun x => σ x ≠ x).card
      < (Finset.univ.filter fun x => τ x ≠ x).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨i, ?_, ?_⟩
      · simp [hτ, hij.symm]
      · simp [hi]
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have hxi : x ≠ i := fun h => hx (h ▸ hi)
      have hxj : x ≠ j := fun h => hx (h ▸ hj)
      simpa [hτ, hxi, hxj] using hx
  exact absurd (hσmax τ (by simpa using hτm)) (not_le.2 hlt')

/-! ### The block labels of a matching -/

/-- The block label of a point: `none` for a fixed point of `σ`, and the unordered pair
`{i, σ i}` for a moved point. The fibres of this map are the remainder set and the pairs. -/
def matchLabel [DecidableEq ι] (σ : ι → ι) (i : ι) : Option (Sym2 ι) :=
  if σ i = i then none else some s(i, σ i)

lemma matchLabel_eq_none [DecidableEq ι] {σ : ι → ι} {i : ι} :
    matchLabel σ i = none ↔ σ i = i := by
  unfold matchLabel
  split_ifs with h <;> simp [h]

lemma matchLabel_eq_some [DecidableEq ι] {σ : ι → ι} {i : ι} {z : Sym2 ι} :
    matchLabel σ i = some z ↔ σ i ≠ i ∧ s(i, σ i) = z := by
  unfold matchLabel
  split_ifs with h <;> simp [h]

/-- The partner of a moved point has the same label. -/
lemma matchLabel_partner [DecidableEq ι] {σ : ι → ι} (hσ : ∀ i, σ (σ i) = i) {i : ι}
    (hi : σ i ≠ i) : matchLabel σ (σ i) = some s(i, σ i) := by
  rw [matchLabel_eq_some, hσ i]
  exact ⟨fun h => hi h.symm, Sym2.eq_swap⟩

/-- The fibre of the label of a moved point `i` is `{i, σ i}`. -/
lemma eq_or_eq_of_matchLabel [DecidableEq ι] {σ : ι → ι} {i l : ι}
    (h : matchLabel σ l = some s(i, σ i)) : l = i ∨ l = σ i := by
  rw [matchLabel_eq_some] at h
  rcases Sym2.eq_iff.1 h.2 with h1 | h1
  · exact Or.inl h1.1
  · exact Or.inr h1.1

end Distinct839.Gram
