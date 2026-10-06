/-
Distinct839/Local/Potential.lean — the piecewise linear potentials on the integer grid.

In grid units (`u = H · t`, `H = 16384`) the potential `10⁶ V · B_r^t` is
`betN r t u = V ∑_k c_k · hat((u - x_k)/2048)` with knots `x_k = 12288 + 2048 k`, `k = 0, …, 13`.
We prove:

* `betN` is affine between consecutive knots, and zero outside `[x_0, x_13]`;
* at an integer point it equals the integer `bv r t x` computed by the checker (`betN_nat`);
* a function that is affine between consecutive knots is bounded below on `[lo, hi]` by its
  minimum over `lo`, `hi` and the knots in between (`knot_min`), which is what `pmin` computes
  (`pmin_spec`);
* the resulting specifications of the minima and affine supports used by the checker
  (`bm0_spec`, `bmD_spec`, `paff_spec`) and the lower bound `betN_lower` behind the pressure test.
-/
import Distinct839.Defs
import Distinct839.Local.Basic

open Finset

namespace Distinct839
namespace Local

/-! ## Functions that are affine on an interval -/

/-- `F` is affine on `[a, b]`. -/
def AffOn (F : ℝ → ℝ) (a b : ℝ) : Prop := ∃ m c : ℝ, ∀ u, a ≤ u → u ≤ b → F u = m * u + c

theorem AffOn.linear (m c a b : ℝ) : AffOn (fun u => m * u + c) a b := ⟨m, c, fun _ _ _ => rfl⟩

theorem AffOn.add {F G : ℝ → ℝ} {a b : ℝ} (hF : AffOn F a b) (hG : AffOn G a b) :
    AffOn (fun u => F u + G u) a b := by
  obtain ⟨m, c, h⟩ := hF
  obtain ⟨m', c', h'⟩ := hG
  exact ⟨m + m', c + c', fun u h1 h2 => by dsimp only; rw [h u h1 h2, h' u h1 h2]; ring⟩

theorem AffOn.sub {F G : ℝ → ℝ} {a b : ℝ} (hF : AffOn F a b) (hG : AffOn G a b) :
    AffOn (fun u => F u - G u) a b := by
  obtain ⟨m, c, h⟩ := hF
  obtain ⟨m', c', h'⟩ := hG
  exact ⟨m - m', c - c', fun u h1 h2 => by dsimp only; rw [h u h1 h2, h' u h1 h2]; ring⟩

theorem AffOn.const_mul {F : ℝ → ℝ} {a b : ℝ} (k : ℝ) (hF : AffOn F a b) :
    AffOn (fun u => k * F u) a b := by
  obtain ⟨m, c, h⟩ := hF
  exact ⟨k * m, k * c, fun u h1 h2 => by dsimp only; rw [h u h1 h2]; ring⟩

theorem AffOn.sum {ι : Type} (s : Finset ι) (f : ι → ℝ → ℝ) (a b : ℝ)
    (h : ∀ k ∈ s, AffOn (f k) a b) : AffOn (fun u => ∑ k ∈ s, f k u) a b := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, fun u _ _ => by simp⟩
  | insert k s hk ih =>
    have h1 := h k (mem_insert_self k s)
    have h2 := ih (fun j hj => h j (mem_insert_of_mem hj))
    have h3 := h1.add h2
    obtain ⟨m, c, h4⟩ := h3
    exact ⟨m, c, fun u hu1 hu2 => by dsimp only; rw [sum_insert hk]; exact h4 u hu1 hu2⟩

/-- Precomposition with an increasing affine map. -/
theorem AffOn.comp {F : ℝ → ℝ} {a b : ℝ} (α β : ℝ) (hα : 0 ≤ α)
    (hF : AffOn F (α * a + β) (α * b + β)) : AffOn (fun u => F (α * u + β)) a b := by
  obtain ⟨m, c, h⟩ := hF
  refine ⟨m * α, m * β + c, fun u h1 h2 => ?_⟩
  dsimp only
  rw [h (α * u + β) (by nlinarith) (by nlinarith)]; ring

/-- An affine function on `[a, b]` is at least the smaller of its end values. -/
theorem AffOn.min_le {F : ℝ → ℝ} {a b u m : ℝ} (hF : AffOn F a b) (h1 : a ≤ u) (h2 : u ≤ b)
    (ha : m ≤ F a) (hb : m ≤ F b) : m ≤ F u := by
  obtain ⟨s, c, h⟩ := hF
  have hab : a ≤ b := h1.trans h2
  rw [h a le_rfl hab] at ha
  rw [h b hab le_rfl] at hb
  rw [h u h1 h2]
  rcases le_total 0 s with hs | hs
  · nlinarith [mul_le_mul_of_nonneg_left h1 hs]
  · nlinarith [mul_le_mul_of_nonpos_left h2 hs]

/-- Linear interpolation of an affine function. -/
theorem AffOn.interp {F : ℝ → ℝ} {a b u : ℝ} (hF : AffOn F a b) (h1 : a ≤ u) (h2 : u ≤ b) :
    F u * (b - a) = F a * (b - u) + F b * (u - a) := by
  obtain ⟨s, c, h⟩ := hF
  have hab : a ≤ b := h1.trans h2
  rw [h a le_rfl hab, h b hab le_rfl, h u h1 h2]; ring

/-! ## The hat function -/

theorem hat_eq_zero_of_le {s : ℝ} (h : s ≤ -1) : hat s = 0 := by
  unfold hat
  rw [abs_of_nonpos (by linarith)]
  exact max_eq_left (by linarith)

theorem hat_eq_zero_of_ge {s : ℝ} (h : 1 ≤ s) : hat s = 0 := by
  unfold hat
  rw [abs_of_nonneg (by linarith)]
  exact max_eq_left (by linarith)

theorem hat_of_neg {s : ℝ} (h1 : -1 ≤ s) (h2 : s ≤ 0) : hat s = 1 + s := by
  unfold hat
  rw [abs_of_nonpos h2, max_eq_right (by linarith)]; ring

theorem hat_of_pos {s : ℝ} (h1 : 0 ≤ s) (h2 : s ≤ 1) : hat s = 1 - s := by
  unfold hat
  rw [abs_of_nonneg h1, max_eq_right (by linarith)]

/-- `hat` is affine on every interval whose interior avoids `-1, 0, 1`. -/
theorem hat_affOn (a b : ℝ) (hm : ¬ (a < -1 ∧ -1 < b)) (h0 : ¬ (a < 0 ∧ 0 < b))
    (hp : ¬ (a < 1 ∧ 1 < b)) : AffOn hat a b := by
  by_cases c1 : b ≤ -1
  · exact ⟨0, 0, fun u _ h2 => by rw [hat_eq_zero_of_le (h2.trans c1)]; ring⟩
  have c2 : -1 ≤ a := by
    by_contra hc; exact hm ⟨not_le.1 hc, not_le.1 c1⟩
  by_cases c3 : b ≤ 0
  · exact ⟨1, 1, fun u h1 h2 => by rw [hat_of_neg (c2.trans h1) (h2.trans c3)]; ring⟩
  have c4 : 0 ≤ a := by
    by_contra hc; exact h0 ⟨not_le.1 hc, not_le.1 c3⟩
  by_cases c5 : b ≤ 1
  · exact ⟨-1, 1, fun u h1 h2 => by rw [hat_of_pos (c4.trans h1) (h2.trans c5)]; ring⟩
  have c6 : 1 ≤ a := by
    by_contra hc; exact hp ⟨not_le.1 hc, not_le.1 c5⟩
  exact ⟨0, 0, fun u h1 _ => by rw [hat_eq_zero_of_ge (c6.trans h1)]; ring⟩

/-- `hat` at a difference of two integers. -/
theorem hat_nat_sub (j k : ℕ) : hat ((j : ℝ) - k) = if j = k then 1 else 0 := by
  by_cases h : j = k
  · subst h; simp [hat]
  · rw [if_neg h]
    rcases Nat.lt_or_gt_of_ne h with h1 | h1
    · apply hat_eq_zero_of_le
      have : (j : ℝ) + 1 ≤ k := by exact_mod_cast h1
      linarith
    · apply hat_eq_zero_of_ge
      have : (k : ℝ) + 1 ≤ j := by exact_mod_cast h1
      linarith

/-! ## Knots -/

/-- Position of knot `j` in grid units: `H (3/4 + j/8) = 12288 + 2048 j`. -/
def knotX (j : ℕ) : ℝ := 12288 + 2048 * j

theorem knotX_eq_cast (j : ℕ) : knotX j = ((12288 + j * 2048 : ℕ) : ℝ) := by
  unfold knotX; push_cast; ring

theorem knotX_lt {j k : ℕ} (h : knotX j < knotX k) : j < k := by
  unfold knotX at h
  have : (j : ℝ) < k := by linarith
  exact_mod_cast this

/-- `F` is affine on every interval that has no knot in its interior. -/
def KnotAff (F : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, (∀ j < 14, ¬ (a < knotX j ∧ knotX j < b)) → AffOn F a b

theorem KnotAff.sub {F G : ℝ → ℝ} (hF : KnotAff F) (hG : KnotAff G) :
    KnotAff (fun u => F u - G u) := fun a b h => (hF a b h).sub (hG a b h)

theorem KnotAff.sub_linear {F : ℝ → ℝ} (hF : KnotAff F) (m : ℝ) :
    KnotAff (fun u => F u - m * u) := fun a b h => by
  have h1 := (hF a b h).sub (AffOn.linear m 0 a b)
  obtain ⟨s, c, h2⟩ := h1
  exact ⟨s, c, fun u hu1 hu2 => by rw [← h2 u hu1 hu2]; ring⟩

/-- The scaled hat at knot `k` is affine away from the knots `k - 1`, `k`, `k + 1`. -/
theorem hatK_affOn (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 12) (a b : ℝ)
    (h : ∀ j < 14, ¬ (a < knotX j ∧ knotX j < b)) :
    AffOn (fun u => hat ((u - knotX k) / 2048)) a b := by
  have e : (fun u : ℝ => hat ((u - knotX k) / 2048))
      = fun u => hat (1 / 2048 * u + -(knotX k) / 2048) := by
    funext u; congr 1; ring
  rw [e]
  refine AffOn.comp (F := hat) (1 / 2048) (-(knotX k) / 2048) (by norm_num) ?_
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hm := h k' (by omega)
  have h0 := h (k' + 1) (by omega)
  have hp := h (k' + 2) (by omega)
  unfold knotX at hm h0 hp ⊢
  push_cast at hm h0 hp ⊢
  apply hat_affOn
  · rintro ⟨h1, h2⟩; exact hm ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact h0 ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact hp ⟨by linarith, by linarith⟩

/-- Lower bound for a function that is affine between knots: if `m` is below the values at the
end points and at the knots inside, it is below the function on the whole interval. -/
theorem knot_min {F : ℝ → ℝ} (hF : KnotAff F) (m : ℝ) (a b : ℝ)
    (ha : m ≤ F a) (hb : m ≤ F b)
    (hk : ∀ j < 14, a < knotX j → knotX j < b → m ≤ F (knotX j))
    (u : ℝ) (h1 : a ≤ u) (h2 : u ≤ b) : m ≤ F u := by
  have key : ∀ n, n ≤ 14 → ∀ a b : ℝ,
      (∀ j, n ≤ j → j < 14 → ¬ (a < knotX j ∧ knotX j < b)) → m ≤ F a → m ≤ F b →
      (∀ j < 14, a < knotX j → knotX j < b → m ≤ F (knotX j)) →
      ∀ u, a ≤ u → u ≤ b → m ≤ F u := by
    intro n
    induction n with
    | zero =>
      intro _ a b hno ha hb _ u h1 h2
      exact (hF a b (fun j hj => hno j (Nat.zero_le j) hj)).min_le h1 h2 ha hb
    | succ n ih =>
      intro hn a b hno ha hb hk u h1 h2
      by_cases hc : a < knotX n ∧ knotX n < b
      · have hmid : m ≤ F (knotX n) := hk n (by omega) hc.1 hc.2
        rcases le_total u (knotX n) with hu | hu
        · refine ih (by omega) a (knotX n) ?_ ha hmid ?_ u h1 hu
          · rintro j hj _ ⟨_, h4⟩
            exact absurd (knotX_lt h4) (by omega)
          · intro j hj h3 h4
            exact hk j hj h3 (h4.trans hc.2)
        · refine ih (by omega) (knotX n) b ?_ hmid hb ?_ u hu h2
          · rintro j hj hj' ⟨h3, h4⟩
            have h5 := knotX_lt h3
            exact hno j (by omega) hj' ⟨hc.1.trans h3, h4⟩
          · intro j hj h3 h4
            exact hk j hj (hc.1.trans h3) h4
      · refine ih (by omega) a b ?_ ha hb hk u h1 h2
        intro j hj hj' h3
        rcases Nat.eq_or_lt_of_le hj with rfl | h4
        · exact hc h3
        · exact hno j h4 hj' h3
  exact key 14 le_rfl a b (fun j h3 h4 => absurd h4 (by omega)) ha hb hk u h1 h2

/-! ## The loop `pmin` -/

theorem pminLoop_le_acc (f : ℕ → SInt) (lo hi : ℕ) :
    ∀ j acc, (pminLoop f lo hi j acc).toInt ≤ acc.toInt := by
  intro j
  induction j with
  | zero => intro acc; exact le_rfl
  | succ j ih =>
    intro acc
    rw [pminLoop]
    refine (ih _).trans ?_
    split
    · exact SInt.toInt_min_le_left _ _
    · exact le_rfl

theorem pminLoop_le_knot (f : ℕ → SInt) (lo hi : ℕ) :
    ∀ j acc k, k < j → lo < 12288 + k * 2048 → 12288 + k * 2048 < hi →
      (pminLoop f lo hi j acc).toInt ≤ (f (12288 + k * 2048)).toInt := by
  intro j
  induction j with
  | zero => intro acc k hk; omega
  | succ j ih =>
    intro acc k hk h1 h2
    rw [pminLoop]
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with rfl | h3
    · refine (pminLoop_le_acc f lo hi _ _).trans ?_
      rw [if_pos ⟨h1, h2⟩]
      exact SInt.toInt_min_le_right _ _
    · exact ih _ k h3 h1 h2

/-- `pmin f lo hi` is a lower bound on `[lo, hi]` for every function that is affine between
knots and agrees with `f` at the integers. -/
theorem pmin_spec {F : ℝ → ℝ} (hF : KnotAff F) (f : ℕ → SInt)
    (hf : ∀ p : ℕ, F p = ((f p).toInt : ℝ)) (lo hi : ℕ) (u : ℝ) (h1 : (lo : ℝ) ≤ u)
    (h2 : u ≤ hi) : (((pmin f lo hi).toInt : ℤ) : ℝ) ≤ F u := by
  refine knot_min hF _ lo hi ?_ ?_ ?_ u h1 h2
  · rw [hf]
    have : (pmin f lo hi).toInt ≤ (f lo).toInt :=
      (pminLoop_le_acc f lo hi 14 _).trans (SInt.toInt_min_le_left _ _)
    exact_mod_cast this
  · rw [hf]
    have : (pmin f lo hi).toInt ≤ (f hi).toInt :=
      (pminLoop_le_acc f lo hi 14 _).trans (SInt.toInt_min_le_right _ _)
    exact_mod_cast this
  · intro j hj h3 h4
    rw [knotX_eq_cast] at h3 h4 ⊢
    rw [hf]
    have h5 : lo < 12288 + j * 2048 := by exact_mod_cast h3
    have h6 : 12288 + j * 2048 < hi := by exact_mod_cast h4
    have : (pmin f lo hi).toInt ≤ (f (12288 + j * 2048)).toInt :=
      pminLoop_le_knot f lo hi 14 _ j hj h5 h6
    exact_mod_cast this

/-! ## The potentials -/

/-- `10⁶ V · B_r^t(u / H)` as a function of the grid coordinate `u`, with the checker's table
of knot values. -/
noncomputable def betN (r t : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ range 14, (((knot r t k).toInt : ℤ) : ℝ) * (cV : ℝ) * hat ((u - knotX k) / 2048)

/-- The first and the last knot value of every potential are zero. -/
theorem knot_ends : ∀ r < 6, ∀ t < 3, (knot r t 0).toInt = 0 ∧ (knot r t 13).toInt = 0 := by
  decide +kernel

theorem betN_knotAff {r t : ℕ} (hr : r < 6) (ht : t < 3) : KnotAff (betN r t) := by
  intro a b h
  unfold betN
  apply AffOn.sum
  intro k hk
  rw [mem_range] at hk
  by_cases hk' : 1 ≤ k ∧ k ≤ 12
  · exact (hatK_affOn k hk'.1 hk'.2 a b h).const_mul _
  · have hz : (knot r t k).toInt = 0 := by
      have he := knot_ends r hr t ht
      have : k = 0 ∨ k = 13 := by omega
      rcases this with rfl | rfl
      · exact he.1
      · exact he.2
    exact ⟨0, 0, fun u _ _ => by rw [hz]; simp⟩

theorem betN_knot (r t j : ℕ) (hj : j < 14) :
    betN r t (knotX j) = (((knot r t j).toInt : ℤ) : ℝ) * cV := by
  unfold betN
  rw [sum_eq_single j]
  · have : (knotX j - knotX j) / 2048 = ((j : ℝ) - j) := by ring
    rw [this, hat_nat_sub, if_pos rfl, mul_one]
  · intro k _ hkj
    have : (knotX j - knotX k) / 2048 = ((j : ℝ) - k) := by unfold knotX; ring
    rw [this, hat_nat_sub, if_neg (Ne.symm hkj), mul_zero]
  · intro h; exact absurd (mem_range.2 hj) h

theorem betN_eq_zero_of_le {r t : ℕ} (hr : r < 6) (ht : t < 3) {u : ℝ} (hu : u ≤ knotX 0) :
    betN r t u = 0 := by
  unfold betN
  apply sum_eq_zero
  intro k _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [(knot_ends r hr t ht).1]; simp
  · rw [hat_eq_zero_of_le, mul_zero]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    unfold knotX at hu ⊢
    rw [div_le_iff₀ (by norm_num)]
    push_cast at hu
    linarith

theorem betN_eq_zero_of_ge {r t : ℕ} (hr : r < 6) (ht : t < 3) {u : ℝ} (hu : knotX 13 ≤ u) :
    betN r t u = 0 := by
  unfold betN
  apply sum_eq_zero
  intro k hk
  rw [mem_range] at hk
  rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with rfl | hk'
  · rw [(knot_ends r hr t ht).2]; simp
  · rw [hat_eq_zero_of_ge, mul_zero]
    have : (k : ℝ) + 1 ≤ 13 := by exact_mod_cast hk'
    unfold knotX at hu ⊢
    rw [le_div_iff₀ (by norm_num)]
    push_cast at hu
    linarith

/-- At an integer point the potential is the integer computed by the checker. -/
theorem betN_nat {r t : ℕ} (hr : r < 6) (ht : t < 3) (x : ℕ) :
    betN r t x = (((bv r t x).toInt : ℤ) : ℝ) := by
  unfold bv
  by_cases h : x ≤ 12288 ∨ 38912 ≤ x
  · rw [if_pos h, SInt.toInt_zero, Int.cast_zero]
    rcases h with h | h
    · apply betN_eq_zero_of_le hr ht
      rw [show knotX 0 = 12288 by norm_num [knotX]]
      exact_mod_cast h
    · apply betN_eq_zero_of_ge hr ht
      rw [show knotX 13 = 38912 by norm_num [knotX]]
      exact_mod_cast h
  · rw [if_neg h]
    simp only [not_or, not_le] at h
    obtain ⟨h1, h2⟩ := h
    dsimp only
    have hq' : (x - 12288) % 2048 < 2048 := Nat.mod_lt _ (by norm_num)
    have hx : x = 12288 + 2048 * ((x - 12288) / 2048) + (x - 12288) % 2048 := by omega
    have hk' : (x - 12288) / 2048 ≤ 12 := by omega
    generalize (x - 12288) / 2048 = k at hx hk' ⊢
    generalize (x - 12288) % 2048 = q at hx hq' ⊢
    have haff : AffOn (betN r t) (knotX k) (knotX (k + 1)) := by
      apply betN_knotAff hr ht
      rintro j _ ⟨h3, h4⟩
      have := knotX_lt h3
      have := knotX_lt h4
      omega
    have hxr : (x : ℝ) = 12288 + 2048 * k + q := by exact_mod_cast hx
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hq1 : (q : ℝ) ≤ 2048 := by exact_mod_cast hq'.le
    have hi := haff.interp (u := (x : ℝ))
      (by unfold knotX; rw [hxr]; linarith)
      (by unfold knotX; rw [hxr]; push_cast; linarith)
    rw [betN_knot r t k (by omega), betN_knot r t (k + 1) (by omega)] at hi
    have e1 : knotX (k + 1) - knotX k = 2048 := by unfold knotX; push_cast; ring
    have e2 : knotX (k + 1) - (x : ℝ) = 2048 - q := by unfold knotX; rw [hxr]; push_cast; ring
    have e3 : (x : ℝ) - knotX k = q := by unfold knotX; rw [hxr]; ring
    rw [e1, e2, e3] at hi
    have hsub : ((2048 - q : ℕ) : ℤ) = 2048 - (q : ℤ) := by
      rw [Nat.cast_sub hq'.le]; norm_num
    simp only [SInt.toInt_smul, SInt.toInt_add, hsub]
    have hV : (cV : ℝ) = 2048 * 131072 := by norm_num [cV]
    rw [hV] at hi
    push_cast
    linear_combination (1 / 2048 : ℝ) * hi

/-! ## Specifications of the minima and supports used by the checker -/

/-- Lower bound for `B_r^0` over `[lo, hi]`. -/
theorem bm0_spec {r : ℕ} (hr : r < 6) (lo hi : ℕ) (u : ℝ) (h1 : (lo : ℝ) ≤ u) (h2 : u ≤ hi) :
    (((pmin (bv r 0) lo hi).toInt : ℤ) : ℝ) ≤ betN r 0 u :=
  pmin_spec (betN_knotAff hr (by norm_num)) _ (fun p => betN_nat hr (by norm_num) p) lo hi u h1 h2

/-- Lower bound for `B_r^t - B_r^0` over `[lo, hi]`. -/
theorem bmD_spec {r t : ℕ} (hr : r < 6) (ht : t < 3) (lo hi : ℕ) (u : ℝ) (h1 : (lo : ℝ) ≤ u)
    (h2 : u ≤ hi) :
    (((pmin (fun x => (bv r t x).sub (bv r 0 x)) lo hi).toInt : ℤ) : ℝ)
      ≤ betN r t u - betN r 0 u := by
  refine pmin_spec (F := fun u => betN r t u - betN r 0 u)
    ((betN_knotAff hr ht).sub (betN_knotAff hr (by norm_num))) _ (fun p => ?_) lo hi u h1 h2
  simp only [SInt.toInt_sub, Int.cast_sub]
  rw [betN_nat hr ht, betN_nat hr (by norm_num)]

/-- The affine support computed by `paff` is below twice the potential on `[lo, hi]`. -/
theorem paff_spec {r t : ℕ} (hr : r < 6) (ht : t < 3) (lo hi : ℕ) (u : ℝ) (h1 : (lo : ℝ) ≤ u)
    (h2 : u ≤ hi) :
    (((paff r t lo hi).s.toInt : ℤ) : ℝ) * u + (((paff r t lo hi).o.toInt : ℤ) : ℝ)
      ≤ 2 * betN r t u := by
  unfold paff
  dsimp only
  simp only [SInt.toInt_smul]
  generalize pslope r t lo hi = s
  have h := pmin_spec (F := fun u => betN r t u - ((s.toInt : ℤ) : ℝ) * u)
    ((betN_knotAff hr ht).sub_linear _) (fun x => (bv r t x).sub (s.smul x)) (fun p => by
      simp only [SInt.toInt_sub, SInt.toInt_smul, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      rw [betN_nat hr ht]) lo hi u h1 h2
  push_cast
  linarith

/-- Bound for the negative part of the potential at position `r`. -/
def nb (r : ℕ) : ℕ := (#[1914, 924, 2113, 2113, 924, 1914] : Array ℕ).getD r 0

theorem knot_ge_nb : ∀ r < 6, ∀ t < 3, ∀ k < 14, -(nb r : ℤ) ≤ (knot r t k).toInt := by
  decide +kernel

theorem nb_sum : nb 0 + nb 1 + nb 2 + nb 3 + nb 4 + nb 5 = cBudget := by decide +kernel

/-- The potential at position `r` is at least `-nb r` (in units of `10⁻⁶ V`). -/
theorem betN_lower {r t : ℕ} (hr : r < 6) (ht : t < 3) (u : ℝ) :
    -((nb r : ℝ) * cV) ≤ betN r t u := by
  have hneg : -((nb r : ℝ) * cV) ≤ 0 := by
    have : (0 : ℝ) ≤ (nb r : ℝ) * cV := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith
  by_cases h1 : u ≤ knotX 0
  · rw [betN_eq_zero_of_le hr ht h1]; exact hneg
  by_cases h2 : knotX 13 ≤ u
  · rw [betN_eq_zero_of_ge hr ht h2]; exact hneg
  have hk : ∀ j < 14, -((nb r : ℝ) * cV) ≤ betN r t (knotX j) := by
    intro j hj
    rw [betN_knot r t j hj]
    have h3 : (((-(nb r : ℤ)) : ℤ) : ℝ) ≤ (((knot r t j).toInt : ℤ) : ℝ) :=
      Int.cast_le.2 (knot_ge_nb r hr t ht j hj)
    rw [Int.cast_neg, Int.cast_natCast] at h3
    have h4 : (0 : ℝ) ≤ cV := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_right h3 h4
    linarith
  exact knot_min (betN_knotAff hr ht) _ (knotX 0) (knotX 13) (hk 0 (by norm_num))
    (hk 13 (by norm_num)) (fun j hj _ _ => hk j hj) u (not_le.1 h1).le (not_le.1 h2).le

end Local
end Distinct839
