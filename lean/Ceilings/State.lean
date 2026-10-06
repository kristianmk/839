/-
Ceilings/State.lean — rational periodic trial states and the evaluation of their energies.

A trial state is one period of a labelled periodic configuration: a list of multiplicities and a
list of rational gaps (`State`). Its points are `pos k = g 0 + … + g (k - 1)`, continued
periodically, its period is `P = pos m`, and `n1`, `n2` count the simple and the double points.

* `State.star`, `State.star_all`, `State.star1`, `State.star1_all`: inequality (⋆) of
  `Ceilings/Periodic.lean` for a state whose gaps are at least `θ` (`sepOK`):
  `n₁ x₁ + n₂ x₂ - b P ≤ energy`, where `energy K r` is the pair energy per period of range `r`.
* `State.rangeUp k2 r`: a rational upper bound for `energy K r`, computed from an upper bound `k2`
  for `K²` at rational points (`energy_le_rangeUp`).
* `State.allUp Q kI E2 N₀`: a rational upper bound for `energy K r` for **all** `r`, for a state
  with integer period (`energy_le_allUp`); the conditions on the state are checked by `allOK`.

All evaluators are structural recursions on `ℚ`, so the kernel can evaluate them
(`decide +kernel`). Nothing here depends on a window.
-/
import Ceilings.Periodic
import Ceilings.KernelBound

open scoped BigOperators
open Finset

namespace Ceilings

open Distinct839 (mulOf)

/-- A periodic trial state: the multiplicities and the gaps of one period. -/
structure State where
  /-- multiplicities of the points of one period: `2` is a double point, every other entry (and
  every missing entry) a simple point -/
  mult : List ℕ
  /-- gaps: entry `i` is the distance from point `i` to the next point; the last entry is the gap
  to the first point of the next period -/
  gap : List ℚ

namespace State

variable (S : State)

/-- number of points per period -/
def m : ℕ := S.gap.length
/-- the gaps, continued periodically -/
def g (k : ℕ) : ℚ := S.gap.getD (k % S.m) 0
/-- point `k` (continued periodically) is a double point -/
def dbl (k : ℕ) : Bool := S.mult.getD (k % S.m) 1 == 2
/-- label of point `k`: `0` simple, `1` double -/
def lab (k : ℕ) : Fin 2 := if S.dbl k then 1 else 0
/-- multiplicity of point `k` as a rational number -/
def mu (k : ℕ) : ℚ := if S.dbl k then 2 else 1
/-- position of point `k`: the sum of the first `k` gaps -/
def pos (k : ℕ) : ℚ := sumN S.g k
/-- the period -/
def P : ℚ := S.pos S.m
/-- number of simple points per period -/
def n1 : ℕ := ((range S.m).filter fun i => ¬ S.dbl i = true).card
/-- number of double points per period -/
def n2 : ℕ := ((range S.m).filter fun i => S.dbl i = true).card
/-- the state has at least one point and all gaps are at least `θ` -/
def sepOK (θ : ℚ) : Bool := decide (0 < S.m) && S.gap.all fun x => decide (θ ≤ x)
/-- the state has no double point -/
def simpleOK : Bool := S.mult.all fun x => x != 2

/-! ## Periodicity -/

theorem g_add (k : ℕ) : S.g (k + S.m) = S.g k := by
  unfold g
  rw [Nat.add_mod_right]

theorem dbl_add (k : ℕ) : S.dbl (k + S.m) = S.dbl k := by
  unfold dbl
  rw [Nat.add_mod_right]

theorem lab_add (k : ℕ) : S.lab (k + S.m) = S.lab k := by
  unfold lab
  rw [dbl_add]

theorem mu_add (k : ℕ) : S.mu (k + S.m) = S.mu k := by
  unfold mu
  rw [dbl_add]

theorem pos_succ (k : ℕ) : S.pos (k + 1) = S.pos k + S.g k := rfl

theorem pos_add (k : ℕ) : S.pos (k + S.m) = S.pos k + S.P := by
  show sumN S.g (k + S.m) = sumN S.g k + sumN S.g S.m
  rw [sumN_eq, sumN_eq, sumN_eq, add_comm k S.m, sum_range_add, add_comm]
  congr 1
  exact sum_congr rfl fun x _ => by rw [add_comm, g_add]

/-! ## Labels, multiplicities and gaps -/

theorem mulOf_lab (k : ℕ) : mulOf (S.lab k) = ((S.mu k : ℚ) : ℝ) := by
  unfold lab mu
  by_cases h : S.dbl k = true
  · rw [if_pos h, if_pos h]
    norm_num [Distinct839.mulOf]
  · rw [if_neg h, if_neg h]
    norm_num [Distinct839.mulOf]

theorem mu_nonneg (k : ℕ) : 0 ≤ S.mu k := by
  unfold mu
  split_ifs <;> norm_num

theorem g_ge {θ : ℚ} (h : S.sepOK θ = true) (k : ℕ) : θ ≤ S.g k := by
  simp only [sepOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hm, hall⟩ := h
  have hk : k % S.m < S.gap.length := Nat.mod_lt _ hm
  unfold g
  rw [List.getD_eq_getElem _ _ hk]
  exact hall _ (List.getElem_mem hk)

theorem dbl_eq_false (h : S.simpleOK = true) (k : ℕ) : S.dbl k = false := by
  simp only [simpleOK, List.all_eq_true, bne_iff_ne, ne_eq] at h
  unfold dbl
  by_cases hk : k % S.m < S.mult.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact beq_false_of_ne (h _ (List.getElem_mem hk))
  · rw [List.getD_eq_default _ _ (not_lt.mp hk)]
    rfl

theorem mu_eq_one (h : S.simpleOK = true) (k : ℕ) : S.mu k = 1 := by
  unfold mu
  rw [S.dbl_eq_false h k]
  rfl

/-- The rewards of one period. -/
theorem sum_rew (x₁ x₂ : ℝ) :
    ∑ i ∈ range S.m, (if S.lab i = 0 then x₁ else x₂)
      = (S.n1 : ℝ) * x₁ + (S.n2 : ℝ) * x₂ := by
  have h : ∀ i, (if S.lab i = 0 then x₁ else x₂) = if S.dbl i = true then x₂ else x₁ := by
    intro i
    unfold lab
    by_cases hd : S.dbl i = true
    · simp [hd]
    · simp [hd]
  simp_rw [h]
  rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, add_comm]
  rfl

/-- The number of points per period is `n₁ + n₂`. -/
theorem n1_add_n2 : S.n1 + S.n2 = S.m := by
  unfold n1 n2
  rw [add_comm, card_filter_add_card_filter_not, card_range]

/-! ## Inequality (⋆) for a state -/

/-- Pair energy per period of the state, pairs of index distance at most `r`. -/
noncomputable def energy (K : ℝ → ℝ) (r : ℕ) : ℝ :=
  periodEnergy K (fun a => ((S.mu a : ℚ) : ℝ)) (fun a => ((S.pos a : ℚ) : ℝ)) S.m r

variable {K : ℝ → ℝ} {θ : ℚ}

lemma cast_pos_add (a : ℕ) :
    ((S.pos (a + S.m) : ℚ) : ℝ) = ((S.pos a : ℚ) : ℝ) + ((S.P : ℚ) : ℝ) := by
  rw [S.pos_add, Rat.cast_add]

lemma cast_gap_ge (hS : S.sepOK θ = true) (a : ℕ) :
    (θ : ℝ) ≤ ((S.pos (a + 1) : ℚ) : ℝ) - ((S.pos a : ℚ) : ℝ) := by
  rw [S.pos_succ, Rat.cast_add, add_sub_cancel_left]
  exact_mod_cast S.g_ge hS a

lemma energy_eq_mulOf (r : ℕ) :
    periodEnergy K (fun a => mulOf (S.lab a)) (fun a => ((S.pos a : ℚ) : ℝ)) S.m r
      = S.energy K r := by
  unfold energy
  simp only [S.mulOf_lab]

lemma energy_eq_one (h1 : S.simpleOK = true) (r : ℕ) :
    periodEnergy K (fun _ => 1) (fun a => ((S.pos a : ℚ) : ℝ)) S.m r = S.energy K r := by
  unfold energy
  simp only [S.mu_eq_one h1, Rat.cast_one]

/-- **(⋆) for a state, range `r`**: `n₁ x₁ + n₂ x₂ - b P ≤ energy K r`. -/
theorem star (hK : ∀ t, K (-t) = K t) (hθ : 0 ≤ θ) (hS : S.sepOK θ = true) {r : ℕ}
    {x₁ x₂ b : ℝ} (h : PairCertFor K (θ : ℝ) r x₁ x₂ b) :
    (S.n1 : ℝ) * x₁ + (S.n2 : ℝ) * x₂ - b * ((S.P : ℚ) : ℝ) ≤ S.energy K r := by
  have key := PairCertFor.star hK (by exact_mod_cast hθ) (m := S.m) (P := ((S.P : ℚ) : ℝ))
    (p := fun a => ((S.pos a : ℚ) : ℝ)) (L := S.lab) S.cast_pos_add S.lab_add
    (S.cast_gap_ge hS) h
  rw [S.sum_rew, S.energy_eq_mulOf] at key
  exact key

/-- **(⋆) for a state, all pairs**, with a common upper bound `e` for the energies of all
ranges. -/
theorem star_all (hK : ∀ t, K (-t) = K t) (hθ : 0 ≤ θ) (hS : S.sepOK θ = true)
    {x₁ x₂ b : ℝ} (h : PairCertAllFor K (θ : ℝ) x₁ x₂ b) {e : ℝ}
    (he : ∀ r, S.energy K r ≤ e) :
    (S.n1 : ℝ) * x₁ + (S.n2 : ℝ) * x₂ - b * ((S.P : ℚ) : ℝ) ≤ e := by
  have key := PairCertAllFor.star hK (by exact_mod_cast hθ) (m := S.m) (P := ((S.P : ℚ) : ℝ))
    (p := fun a => ((S.pos a : ℚ) : ℝ)) (L := S.lab) S.cast_pos_add S.lab_add
    (S.cast_gap_ge hS) h (e := e) (fun r => by rw [S.energy_eq_mulOf]; exact he r)
  rw [S.sum_rew] at key
  exact key

/-- **(⋆) for a state of simple points, range `r`**: `x m - b P ≤ energy K r`. -/
theorem star1 (hK : ∀ t, K (-t) = K t) (hθ : 0 ≤ θ) (hS : S.sepOK θ = true)
    (h1 : S.simpleOK = true) {r : ℕ} {x b : ℝ} (h : PairCert1For K (θ : ℝ) r x b) :
    x * (S.m : ℝ) - b * ((S.P : ℚ) : ℝ) ≤ S.energy K r := by
  have key := PairCert1For.star hK (by exact_mod_cast hθ) (m := S.m) (P := ((S.P : ℚ) : ℝ))
    (p := fun a => ((S.pos a : ℚ) : ℝ)) S.cast_pos_add (S.cast_gap_ge hS) h
  rw [S.energy_eq_one h1] at key
  exact key

/-- **(⋆) for a state of simple points, all pairs.** -/
theorem star1_all (hK : ∀ t, K (-t) = K t) (hθ : 0 ≤ θ) (hS : S.sepOK θ = true)
    (h1 : S.simpleOK = true) {x b : ℝ} (h : PairCert1AllFor K (θ : ℝ) x b) {e : ℝ}
    (he : ∀ r, S.energy K r ≤ e) :
    x * (S.m : ℝ) - b * ((S.P : ℚ) : ℝ) ≤ e :=
  PairCert1AllFor.star hK (by exact_mod_cast hθ) (m := S.m) (P := ((S.P : ℚ) : ℝ))
    (p := fun a => ((S.pos a : ℚ) : ℝ)) S.cast_pos_add (S.cast_gap_ge hS) h (e := e)
    (fun r => by rw [S.energy_eq_one h1]; exact he r)

/-! ## The energy of a finite range -/

/-- Rational upper bound for the pair energy per period of range `r`, from an upper bound `k2`
for `K²`. -/
def rangeUp (k2 : ℚ → ℚ) (r : ℕ) : ℚ :=
  sumN (fun i => sumN (fun s =>
    2 * S.mu i * S.mu (i + s + 1) * k2 (S.pos (i + s + 1) - S.pos i)) r) S.m

theorem energy_le_rangeUp {k2 : ℚ → ℚ} (hk2 : ∀ t : ℚ, K (t : ℝ) ^ 2 ≤ ((k2 t : ℚ) : ℝ))
    (r : ℕ) : S.energy K r ≤ ((S.rangeUp k2 r : ℚ) : ℝ) := by
  show ∑ i ∈ range S.m, ∑ s ∈ range r,
      2 * ((S.mu i : ℚ) : ℝ) * ((S.mu (i + s + 1) : ℚ) : ℝ)
        * K (((S.pos (i + s + 1) : ℚ) : ℝ) - ((S.pos i : ℚ) : ℝ)) ^ 2
    ≤ ((sumN (fun i => sumN (fun s =>
        2 * S.mu i * S.mu (i + s + 1) * k2 (S.pos (i + s + 1) - S.pos i)) r) S.m : ℚ) : ℝ)
  rw [cast_sumN]
  refine sum_le_sum fun i _ => ?_
  rw [cast_sumN]
  refine sum_le_sum fun s _ => ?_
  have h0 : (0 : ℝ) ≤ 2 * ((S.mu i : ℚ) : ℝ) * ((S.mu (i + s + 1) : ℚ) : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (by exact_mod_cast S.mu_nonneg i))
      (by exact_mod_cast S.mu_nonneg (i + s + 1))
  rw [Rat.cast_mul, Rat.cast_mul, Rat.cast_mul, Rat.cast_ofNat, ← Rat.cast_sub]
  exact mul_le_mul_of_nonneg_left (hk2 _) h0

/-! ## The energy of all pairs, for an integer period -/

/-- The conditions on a state under which `allUp` is an upper bound: the period is a positive
integer, and for two different points `i, i'` of a period the difference `Δ = pos i' - pos i` is
not an integer, `Δ + (N₀ + 1) P ≥ T₀` and `Δ + N₀ P + P/2 > 0`. -/
def allOK (T₀ : ℚ) (N₀ : ℕ) : Bool :=
  decide (S.P.den = 1) && decide (1 ≤ S.P.num) &&
  (List.range S.m).all fun i => (List.range S.m).all fun i' =>
    decide (i' = i) || (decide ((S.pos i' - S.pos i).den ≠ 1)
      && decide (T₀ ≤ S.pos i' - S.pos i + (N₀ + 1) * S.P.num)
      && decide (0 < S.pos i' - S.pos i + N₀ * S.P.num + S.P.num / 2))

/-- Rational upper bound for the pair energy per period of every range, for a state with integer
period: the pairs inside one period (`i < i'`) and, for every ordered pair `(i, i')`, the sum over
the later periods (`intTailUp` for `i' = i`, `tailUp` otherwise). -/
def allUp (Q : ℚ → ℚ) (kI : ℤ → ℚ) (E2 : ℚ) (N₀ : ℕ) : ℚ :=
  sumN (fun i => sumN (fun i' => 2 * S.mu i * S.mu i' *
    ((if i < i' then k2Up Q kI (S.pos i' - S.pos i) else 0)
      + (if i' = i then intTailUp kI S.P.num
         else tailUp Q E2 S.P.num N₀ (S.pos i' - S.pos i)))) S.m) S.m

theorem energy_le_allUp {Q : ℚ → ℚ} {kI : ℤ → ℚ} (hK : KernelEval K Q kI) {T₀ E2 : ℚ}
    (hQ : QTail Q T₀ E2) {N₀ : ℕ} (hS : S.allOK T₀ N₀ = true) (r : ℕ) :
    S.energy K r ≤ ((S.allUp Q kI E2 N₀ : ℚ) : ℝ) := by
  simp only [allOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at hS
  obtain ⟨⟨hden, hnum⟩, hall⟩ := hS
  have hP : ((S.P.num : ℤ) : ℚ) = S.P := Rat.coe_int_num_of_den_eq_one hden
  have hPr : ((S.P : ℚ) : ℝ) = ((S.P.num : ℤ) : ℝ) := by
    conv_lhs => rw [← hP]
    exact Rat.cast_intCast _
  have hT : ∀ i < S.m, ∀ i' < S.m, ∀ r : ℕ,
      ∑ n ∈ range r, K (((S.pos i' : ℚ) : ℝ) - ((S.pos i : ℚ) : ℝ)
          + ((n : ℝ) + 1) * ((S.P : ℚ) : ℝ)) ^ 2
        ≤ (((if i' = i then intTailUp kI S.P.num
            else tailUp Q E2 S.P.num N₀ (S.pos i' - S.pos i)) : ℚ) : ℝ) := by
    intro i hi i' hi' r
    by_cases h : i' = i
    · rw [if_pos h, h]
      have e : ∀ n : ℕ, ((S.pos i : ℚ) : ℝ) - ((S.pos i : ℚ) : ℝ)
          + ((n : ℝ) + 1) * ((S.P : ℚ) : ℝ) = ((n : ℝ) + 1) * ((S.P.num : ℤ) : ℝ) := fun n => by
        rw [sub_self, zero_add, hPr]
      rw [sum_congr rfl fun n _ => by rw [e n]]
      exact sum_K_sq_int_le hK hnum r
    · rw [if_neg h]
      rcases hall i hi i' hi' with h' | ⟨⟨h1, h2⟩, h3⟩
      · exact absurd h' h
      · have key := sum_K_sq_le_tailUp hK hQ hnum h1 h2 h3 r
        rw [Rat.cast_sub] at key
        rw [hPr]
        exact key
  have key := periodEnergy_le_all (K := K) (m := S.m) (P := ((S.P : ℚ) : ℝ))
    (d := fun a => ((S.mu a : ℚ) : ℝ)) (p := fun a => ((S.pos a : ℚ) : ℝ))
    (fun a => by exact_mod_cast S.mu_nonneg a) (fun a => by rw [S.mu_add]) S.cast_pos_add
    (fun i i' => (((if i' = i then intTailUp kI S.P.num
      else tailUp Q E2 S.P.num N₀ (S.pos i' - S.pos i)) : ℚ) : ℝ)) hT r
  refine key.trans ?_
  unfold allUp
  rw [cast_sumN]
  refine sum_le_sum fun i _ => ?_
  rw [cast_sumN]
  refine sum_le_sum fun i' _ => ?_
  have h0 : (0 : ℝ) ≤ 2 * ((S.mu i : ℚ) : ℝ) * ((S.mu i' : ℚ) : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (by exact_mod_cast S.mu_nonneg i))
      (by exact_mod_cast S.mu_nonneg i')
  have hite : (if i < i' then K (((S.pos i' : ℚ) : ℝ) - ((S.pos i : ℚ) : ℝ)) ^ 2 else 0)
      ≤ (((if i < i' then k2Up Q kI (S.pos i' - S.pos i) else 0) : ℚ) : ℝ) := by
    split_ifs
    · rw [← Rat.cast_sub]
      exact k2Up_sound hK _
    · simp
  rw [Rat.cast_mul, Rat.cast_mul, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_add]
  exact mul_le_mul_of_nonneg_left (add_le_add hite le_rfl) h0

end State

end Ceilings
