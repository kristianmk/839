/-
Distinct839/Assembly/EdgeCount.lean — the zeros near the ends of the window.

`Nedge Z T` counts (with multiplicity) the zeros with ordinate in
`(T − √T, T + √T] ∪ (2T − √T, 2T + √T]`. From the local count `N(t, t+1) ≤ A₀ log(|t| + 3)`
(the second field of `RiemannVonMangoldt`) it is `O(√T · log T)`, hence `o(N(T, 2T))`.
The upstream analogue for `NII` (zeros with ordinate in `(T − √T, T] ∪ (2T, 2T + √T]`) is
`Zeta23.Tail.eventually_NII_le`.
-/
import Zeta23.XiPrime.Assembly

noncomputable section

open Filter Asymptotics Topology Real

namespace Distinct839.Assembly

open Zeta23 Zeta23.Assembly

/-- Number of zeros, with multiplicity, with ordinate within `√T` of `T` or of `2T`. -/
def Nedge (Z : ZeroConfig) (T : ℝ) : ℕ :=
  Z.N (T - D0 T) (T + D0 T) + Z.N (2 * T - D0 T) (2 * T + D0 T)

variable (Z : ZeroConfig)

lemma N_mono_right {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) : Z.N a b ≤ Z.N a c := by
  rw [N_add Z hab hbc]; exact Nat.le_add_right _ _

lemma N_mono_left {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) : Z.N b c ≤ Z.N a c := by
  rw [N_add Z hab hbc]; exact Nat.le_add_left _ _

/-- `NII ≤ Nedge`. -/
lemma NII_le_Nedge (T : ℝ) : NII Z T ≤ Nedge Z T := by
  have h0 := D0_nonneg T
  unfold NII Nedge
  exact Nat.add_le_add (N_mono_right Z (by linarith) (by linarith))
    (N_mono_left Z (by linarith) (by linarith))

/-- Local count on an interval of integer length. -/
lemma N_le_of_local {A₀ : ℝ} (hA₀ : 0 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (a : ℝ) (n : ℕ) :
    (Z.N a (a + n) : ℝ) ≤ n * (A₀ * Real.log (|a| + n + 3)) := by
  induction n with
  | zero => simp [N_self]
  | succ n ih =>
    have hadd : Z.N a (a + (n + 1 : ℕ)) = Z.N a (a + n) + Z.N (a + n) (a + n + 1) := by
      rw [N_add Z (a := a) (b := a + n) (c := a + (n + 1 : ℕ)) (by simp) (by push_cast; linarith)]
      congr 2; push_cast; ring
    have ha0 := abs_nonneg a
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hlog1 : Real.log (|a| + n + 3) ≤ Real.log (|a| + (n + 1 : ℕ) + 3) :=
      Real.log_le_log (by positivity) (by push_cast; linarith)
    have hlog2 : Real.log (|a + n| + 3) ≤ Real.log (|a| + (n + 1 : ℕ) + 3) := by
      refine Real.log_le_log (by positivity) ?_
      have := abs_add_le a (n : ℝ)
      rw [abs_of_nonneg hn0] at this
      push_cast; linarith
    have h2 := hloc (a + n)
    rw [hadd]
    push_cast
    have e1 : (n : ℝ) * (A₀ * Real.log (|a| + n + 3))
        ≤ n * (A₀ * Real.log (|a| + (n + 1 : ℕ) + 3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog1 hA₀) hn0
    have e2 : A₀ * Real.log (|a + n| + 3) ≤ A₀ * Real.log (|a| + (n + 1 : ℕ) + 3) :=
      mul_le_mul_of_nonneg_left hlog2 hA₀
    push_cast at e1 e2 ⊢
    linarith

/-- Local count on a general interval. -/
lemma N_le_of_local' {A₀ : ℝ} (hA₀ : 0 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {a b : ℝ} (hab : a ≤ b) :
    (Z.N a b : ℝ) ≤ (b - a + 1) * (A₀ * Real.log (|a| + (b - a) + 4)) := by
  set n : ℕ := ⌈b - a⌉₊ with hn
  have hn1 : b - a ≤ n := Nat.le_ceil _
  have hn2 : (n : ℝ) < b - a + 1 := Nat.ceil_lt_add_one (by linarith)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha0 := abs_nonneg a
  have h1 : (Z.N a b : ℝ) ≤ Z.N a (a + n) := by
    exact_mod_cast N_mono_right Z hab (by linarith)
  have h2 := N_le_of_local Z hA₀ hloc a n
  have hlog : Real.log (|a| + n + 3) ≤ Real.log (|a| + (b - a) + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog0 : 0 ≤ Real.log (|a| + n + 3) := Real.log_nonneg (by linarith)
  calc (Z.N a b : ℝ) ≤ n * (A₀ * Real.log (|a| + n + 3)) := h1.trans h2
    _ ≤ (b - a + 1) * (A₀ * Real.log (|a| + (b - a) + 4)) := by
        apply mul_le_mul hn2.le (mul_le_mul_of_nonneg_left hlog hA₀) (mul_nonneg hA₀ hlog0)
          (by linarith)

/-- `Nedge ≤ 6 A₀ √T log(4T)` for `T ≥ 4`. -/
lemma Nedge_le {A₀ : ℝ} (hA₀ : 0 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {T : ℝ} (hT : 4 ≤ T) :
    (Nedge Z T : ℝ) ≤ 6 * A₀ * Real.sqrt T * Real.log (4 * T) := by
  have hs0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hs1 : 1 ≤ Real.sqrt T := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hsT : Real.sqrt T ≤ T := by
    have h := Real.mul_self_sqrt (show (0 : ℝ) ≤ T by linarith)
    nlinarith
  have hlog4 : 0 ≤ Real.log (4 * T) := Real.log_nonneg (by linarith)
  have h1 := N_le_of_local' Z hA₀ hloc (a := T - D0 T) (b := T + D0 T)
    (by unfold D0; linarith)
  have h2 := N_le_of_local' Z hA₀ hloc (a := 2 * T - D0 T) (b := 2 * T + D0 T)
    (by unfold D0; linarith)
  unfold D0 at h1 h2
  have ha1 : |T - Real.sqrt T| = T - Real.sqrt T := abs_of_nonneg (by linarith)
  have ha2 : |2 * T - Real.sqrt T| = 2 * T - Real.sqrt T := abs_of_nonneg (by linarith)
  rw [ha1] at h1
  rw [ha2] at h2
  have hl1 : Real.log (T - Real.sqrt T + (T + Real.sqrt T - (T - Real.sqrt T)) + 4)
      ≤ Real.log (4 * T) := Real.log_le_log (by linarith) (by linarith)
  have hl2 : Real.log (2 * T - Real.sqrt T + (2 * T + Real.sqrt T - (2 * T - Real.sqrt T)) + 4)
      ≤ Real.log (4 * T) := Real.log_le_log (by linarith) (by linarith)
  have hb1 : (Z.N (T - Real.sqrt T) (T + Real.sqrt T) : ℝ)
      ≤ (3 * Real.sqrt T) * (A₀ * Real.log (4 * T)) := by
    refine h1.trans ?_
    apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hl1 hA₀)
      (mul_nonneg hA₀ (Real.log_nonneg (by linarith))) (by linarith)
  have hb2 : (Z.N (2 * T - Real.sqrt T) (2 * T + Real.sqrt T) : ℝ)
      ≤ (3 * Real.sqrt T) * (A₀ * Real.log (4 * T)) := by
    refine h2.trans ?_
    apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hl2 hA₀)
      (mul_nonneg hA₀ (Real.log_nonneg (by linarith))) (by linarith)
  unfold Nedge D0
  push_cast
  linarith

/-- **`Nedge = o(N(T, 2T))`** under the Riemann–von Mangoldt input. -/
theorem isLittleO_Nedge (hR : RiemannVonMangoldt Z) :
    (fun T => (Nedge Z T : ℝ)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := hR.local_count
  have hA0 : 0 ≤ A₀ := by linarith
  have hO : (fun T => (Nedge Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
    refine IsBigO.of_bound (12 * A₀) ?_
    filter_upwards [eventually_ge_atTop (300 : ℝ), eventually_l_pos] with T hT hl
    have h1 := Nedge_le Z hA0 hloc (T := T) (by linarith)
    have h2 := Tail.log_four_mul_le_two_mul_l (T := T) hT
    have hs0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (by positivity)]
    calc (Nedge Z T : ℝ) ≤ 6 * A₀ * Real.sqrt T * Real.log (4 * T) := h1
      _ ≤ 6 * A₀ * Real.sqrt T * (2 * l T) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 12 * A₀ * (Real.sqrt T * l T) := by ring
  exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z hR isLittleO_sqrt_mul_l_Tl)

/-- `NII = o(N(T, 2T))`. -/
theorem isLittleO_NII (hR : RiemannVonMangoldt Z) :
    (fun T => (NII Z T : ℝ)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
  refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 ?_) (isLittleO_Nedge Z hR)
  refine Eventually.of_forall fun T => ?_
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (Nat.cast_nonneg _), one_mul]
  exact_mod_cast NII_le_Nedge Z T

end Distinct839.Assembly
