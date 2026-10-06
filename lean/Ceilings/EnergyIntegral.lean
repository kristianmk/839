/-
Ceilings/EnergyIntegral.lean — the second term of the energy constant as a double integral.

The energy constant of a window `f` on `[-1/2, 1/2]` is

    `C(f) = ∫ f² + ∬ |s - t| f(s) f(t) ds dt`        (both integrals over `[-1/2, 1/2]`).

The method uses the second term in the form `2 ∫₀¹ r (f⋆f)(r) dr`, where
`(f⋆f)(r) = ∫_{-1/2}^{1/2-r} f(s) f(s + r) ds` is the autocorrelation `Zeta23.XiPrime.vConv`, and
`Distinct839/Constant/Kappa.lean`, `Simple673/Constant/Kappa.lean` evaluate it in that form
(`Bconst`). This file proves that the two forms are equal, for every continuous function:

* `integral_integral_swap_triangle`: for a continuous function `G` of two real variables and
  `a ≤ b`, `∫_a^b (∫_a^x G(x, y) dy) dx = ∫_a^b (∫_y^b G(x, y) dx) dy` (the order of integration
  on the triangle `a ≤ y ≤ x ≤ b`; from Fubini's theorem for the indicator function of the
  triangle).
* `two_mul_integral_mul_vConv_eq`: for continuous `v`,
  `2 ∫₀¹ r (v⋆v)(r) dr = ∬ |s - t| v(s) v(t) ds dt`. Both sides are twice the integral of
  `(t - s) v(s) v(t)` over the triangle `-1/2 ≤ s ≤ t ≤ 1/2`: on the left by the substitution
  `t = s + r` and an exchange of the order of integration, on the right by the symmetry of the
  integrand in `s` and `t`.
* `integral_abs_sub_mul_fCos`, `integral_abs_sub_mul_fCos_line`: for the two windows
  `Distinct839.fCos`, `Simple673.fCos` the double integral is `Distinct839.Bconst`,
  `Simple673.Bconst`.

Nothing here depends on a compiled computation.
-/
import Mathlib
import Zeta23.XiPrime.Defs
import Distinct839.Constant.Kappa
import Simple673.Constant.Kappa

open MeasureTheory Set

namespace Ceilings

/-- **Order of integration on a triangle.** For a continuous function `G` of two real variables
and `a ≤ b`, the integral over the triangle `a ≤ y ≤ x ≤ b` can be taken in either order:
`∫_a^b (∫_a^x G(x, y) dy) dx = ∫_a^b (∫_y^b G(x, y) dx) dy`. -/
theorem integral_integral_swap_triangle {a b : ℝ} (hab : a ≤ b) {G : ℝ → ℝ → ℝ}
    (hG : Continuous (Function.uncurry G)) :
    ∫ x in a..b, ∫ y in a..x, G x y = ∫ y in a..b, ∫ x in y..b, G x y := by
  -- the triangle `a < y < x ≤ b`: its slices are the intervals `Ioo a x` and `Ioc y b`
  let T : Set (ℝ × ℝ) := {p | a < p.2 ∧ p.2 < p.1 ∧ p.1 ≤ b}
  have hTm : MeasurableSet T := by
    have h1 : MeasurableSet {p : ℝ × ℝ | a < p.2} :=
      measurableSet_lt measurable_const measurable_snd
    have h2 : MeasurableSet {p : ℝ × ℝ | p.2 < p.1} :=
      measurableSet_lt measurable_snd measurable_fst
    have h3 : MeasurableSet {p : ℝ × ℝ | p.1 ≤ b} :=
      measurableSet_le measurable_fst measurable_const
    exact h1.inter (h2.inter h3)
  have hTsub : T ⊆ Icc a b ×ˢ Icc a b := by
    rintro ⟨x, y⟩ ⟨h1, h2, h3⟩
    exact ⟨⟨(h1.trans h2).le, h3⟩, ⟨h1.le, h2.le.trans h3⟩⟩
  -- the indicator function of the triangle times `G` is integrable on the plane
  have hint : Integrable (Function.uncurry fun x y => T.indicator (Function.uncurry G) (x, y))
      (volume.prod volume) := by
    have hK : IntegrableOn (Function.uncurry G) (Icc a b ×ˢ Icc a b) (volume.prod volume) :=
      hG.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    exact (hK.mono_set hTsub).integrable_indicator hTm
  -- Fubini's theorem
  have key := integral_integral_swap hint
  -- the two iterated integrals of the indicator function are the two sides
  have hL : ∫ x, ∫ y, T.indicator (Function.uncurry G) (x, y)
      = ∫ x in a..b, ∫ y in a..x, G x y := by
    rw [intervalIntegral.integral_of_le hab, ← integral_indicator measurableSet_Ioc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    by_cases hx : x ∈ Ioc a b
    · rw [indicator_of_mem hx, intervalIntegral.integral_of_le hx.1.le,
        integral_Ioc_eq_integral_Ioo, ← integral_indicator measurableSet_Ioo]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      beta_reduce
      by_cases hy : y ∈ Ioo a x
      · rw [indicator_of_mem hy, indicator_of_mem (show (x, y) ∈ T from ⟨hy.1, hy.2, hx.2⟩)]
        rfl
      · rw [indicator_of_notMem hy, indicator_of_notMem]
        exact fun h => hy ⟨h.1, h.2.1⟩
    · rw [indicator_of_notMem hx]
      have h0 : ∀ y, T.indicator (Function.uncurry G) (x, y) = 0 := fun y =>
        indicator_of_notMem (fun h => hx ⟨h.1.trans h.2.1, h.2.2⟩) _
      simp [h0]
  have hR : ∫ y, ∫ x, T.indicator (Function.uncurry G) (x, y)
      = ∫ y in a..b, ∫ x in y..b, G x y := by
    rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
      ← integral_indicator measurableSet_Ioo]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    by_cases hy : y ∈ Ioo a b
    · rw [indicator_of_mem hy, intervalIntegral.integral_of_le hy.2.le,
        ← integral_indicator measurableSet_Ioc]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      by_cases hx : x ∈ Ioc y b
      · rw [indicator_of_mem hx, indicator_of_mem (show (x, y) ∈ T from ⟨hy.1, hx.1, hx.2⟩)]
        rfl
      · rw [indicator_of_notMem hx, indicator_of_notMem]
        exact fun h => hx ⟨h.2.1, h.2.2⟩
    · rw [indicator_of_notMem hy]
      have h0 : ∀ x, T.indicator (Function.uncurry G) (x, y) = 0 := fun x =>
        indicator_of_notMem (fun h => hy ⟨h.1, h.2.1.trans_le h.2.2⟩) _
      simp [h0]
  rw [← hL, ← hR]
  exact key

/-- **The energy integral as a double integral.** For a continuous function `v` on the real line,
`2 ∫₀¹ r (v⋆v)(r) dr = ∬ |s - t| v(s) v(t) ds dt`, the double integral over the square
`[-1/2, 1/2]²`, where `(v⋆v)(r) = ∫_{-1/2}^{1/2-r} v(s) v(s + r) ds` is the autocorrelation
`Zeta23.XiPrime.vConv`. -/
theorem two_mul_integral_mul_vConv_eq (v : ℝ → ℝ) (hv : Continuous v) :
    2 * ∫ r in (0 : ℝ)..1, r * Zeta23.XiPrime.vConv v r
      = ∫ s in (-(1 : ℝ) / 2)..(1 / 2), ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * v s * v t := by
  have hab : -(1 : ℝ) / 2 ≤ 1 / 2 := by norm_num
  -- `U` is the integral of `(t - s) v(s) v(t)` over the upper triangle `s ≤ t`
  set U : ℝ := ∫ s in (-(1 : ℝ) / 2)..(1 / 2), ∫ t in s..(1 / 2), (t - s) * v s * v t with hU
  -- the left side is `2 U`: put `x = 1/2 - r`, exchange the order of integration, then put
  -- `t = s + 1/2 - x`
  have hLeft : ∫ r in (0 : ℝ)..1, r * Zeta23.XiPrime.vConv v r = U := by
    let G : ℝ → ℝ → ℝ := fun x s => (1 / 2 - x) * v s * v (s + (1 / 2 - x))
    let Φ : ℝ → ℝ := fun x => ∫ s in (-(1 : ℝ) / 2)..x, G x s
    have hGc : Continuous (Function.uncurry G) := by
      have h : Continuous fun p : ℝ × ℝ => (1 / 2 - p.1) * v p.2 * v (p.2 + (1 / 2 - p.1)) := by
        fun_prop
      exact h
    calc ∫ r in (0 : ℝ)..1, r * Zeta23.XiPrime.vConv v r
        = ∫ r in (0 : ℝ)..1, Φ (1 / 2 - r) := by
          refine intervalIntegral.integral_congr fun r _ => ?_
          show r * Zeta23.XiPrime.vConv v r
            = ∫ s in (-(1 : ℝ) / 2)..(1 / 2 - r),
                (1 / 2 - (1 / 2 - r)) * v s * v (s + (1 / 2 - (1 / 2 - r)))
          unfold Zeta23.XiPrime.vConv
          rw [← intervalIntegral.integral_const_mul]
          simp only [sub_sub_cancel, mul_assoc]
      _ = ∫ x in (-(1 : ℝ) / 2)..(1 / 2), Φ x := by
          rw [intervalIntegral.integral_comp_sub_left Φ (1 / 2)]
          norm_num
      _ = ∫ s in (-(1 : ℝ) / 2)..(1 / 2), ∫ x in s..(1 / 2), G x s :=
          integral_integral_swap_triangle hab hGc
      _ = U := by
          refine intervalIntegral.integral_congr fun s _ => ?_
          have h := intervalIntegral.integral_comp_sub_left (a := s) (b := 1 / 2)
            (fun t : ℝ => (t - s) * v s * v t) (s + 1 / 2)
          rw [show s + 1 / 2 - 1 / 2 = s by ring, show s + 1 / 2 - s = 1 / 2 by ring] at h
          show ∫ x in s..(1 / 2), (1 / 2 - x) * v s * v (s + (1 / 2 - x))
            = ∫ t in s..(1 / 2), (t - s) * v s * v t
          rw [← h]
          refine intervalIntegral.integral_congr fun x _ => ?_
          show (1 / 2 - x) * v s * v (s + (1 / 2 - x))
            = (s + 1 / 2 - x - s) * v s * v (s + 1 / 2 - x)
          rw [show s + 1 / 2 - x - s = 1 / 2 - x by ring,
            show s + (1 / 2 - x) = s + 1 / 2 - x by ring]
  -- the right side is `2 U`: split the inner integral at `t = s`, and exchange the order of
  -- integration in the lower triangle `t ≤ s`
  have hRight : ∫ s in (-(1 : ℝ) / 2)..(1 / 2), ∫ t in (-(1 : ℝ) / 2)..(1 / 2),
      |s - t| * v s * v t = 2 * U := by
    have hLc : Continuous (Function.uncurry fun s t : ℝ => (s - t) * v s * v t) := by
      have h : Continuous fun p : ℝ × ℝ => (p.1 - p.2) * v p.1 * v p.2 := by fun_prop
      exact h
    have hUc : Continuous (Function.uncurry fun s t : ℝ => (t - s) * v s * v t) := by
      have h : Continuous fun p : ℝ × ℝ => (p.2 - p.1) * v p.1 * v p.2 := by fun_prop
      exact h
    have hA : Continuous fun s : ℝ => ∫ t in (-(1 : ℝ) / 2)..s, (s - t) * v s * v t :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hLc continuous_id
    have hB : Continuous fun s : ℝ => ∫ t in s..(1 / 2 : ℝ), (t - s) * v s * v t := by
      have h1 : Continuous fun s : ℝ => ∫ t in (1 / 2 : ℝ)..s, (t - s) * v s * v t :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hUc continuous_id
      have h2 : (fun s : ℝ => ∫ t in s..(1 / 2 : ℝ), (t - s) * v s * v t)
          = fun s => -∫ t in (1 / 2 : ℝ)..s, (t - s) * v s * v t := by
        funext s
        exact intervalIntegral.integral_symm _ _
      rw [h2]
      exact h1.neg
    have hsplit : ∀ s ∈ Icc (-(1 : ℝ) / 2) (1 / 2),
        ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * v s * v t
          = (∫ t in (-(1 : ℝ) / 2)..s, (s - t) * v s * v t)
            + ∫ t in s..(1 / 2), (t - s) * v s * v t := by
      intro s hs
      have hc : Continuous fun t : ℝ => |s - t| * v s * v t := by fun_prop
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := s)
        (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
      congr 1
      · refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le hs.1] at ht
        show |s - t| * v s * v t = (s - t) * v s * v t
        rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]
      · refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le hs.2] at ht
        show |s - t| * v s * v t = (t - s) * v s * v t
        rw [abs_of_nonpos (sub_nonpos.mpr ht.1), neg_sub]
    have hswap : ∫ s in (-(1 : ℝ) / 2)..(1 / 2), ∫ t in (-(1 : ℝ) / 2)..s, (s - t) * v s * v t
        = U := by
      rw [integral_integral_swap_triangle hab hLc]
      refine intervalIntegral.integral_congr fun t _ => ?_
      refine intervalIntegral.integral_congr fun s _ => ?_
      show (s - t) * v s * v t = (s - t) * v t * v s
      ring
    calc ∫ s in (-(1 : ℝ) / 2)..(1 / 2), ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * v s * v t
        = ∫ s in (-(1 : ℝ) / 2)..(1 / 2), ((∫ t in (-(1 : ℝ) / 2)..s, (s - t) * v s * v t)
            + ∫ t in s..(1 / 2), (t - s) * v s * v t) := by
          refine intervalIntegral.integral_congr fun s hs => ?_
          rw [uIcc_of_le hab] at hs
          exact hsplit s hs
      _ = (∫ s in (-(1 : ℝ) / 2)..(1 / 2), ∫ t in (-(1 : ℝ) / 2)..s, (s - t) * v s * v t)
            + U :=
          intervalIntegral.integral_add (hA.intervalIntegrable _ _) (hB.intervalIntegrable _ _)
      _ = 2 * U := by
          rw [hswap]
          ring
  rw [hLeft, hRight]

/-- For the window of `Distinct839` the double integral `∬ |s - t| f(s) f(t) ds dt` over
`[-1/2, 1/2]²` is the constant `Distinct839.Bconst`. -/
theorem integral_abs_sub_mul_fCos :
    ∫ s in (-(1 : ℝ) / 2)..(1 / 2), ∫ t in (-(1 : ℝ) / 2)..(1 / 2),
      |s - t| * Distinct839.fCos s * Distinct839.fCos t = Distinct839.Bconst := by
  rw [← two_mul_integral_mul_vConv_eq _ Distinct839.Constant.continuous_fCos,
    Distinct839.Constant.integral_mul_vConv_fCos]
  ring

/-- For the window of `Simple673` the double integral `∬ |s - t| f(s) f(t) ds dt` over
`[-1/2, 1/2]²` is the constant `Simple673.Bconst`. -/
theorem integral_abs_sub_mul_fCos_line :
    ∫ s in (-(1 : ℝ) / 2)..(1 / 2), ∫ t in (-(1 : ℝ) / 2)..(1 / 2),
      |s - t| * Simple673.fCos s * Simple673.fCos t = Simple673.Bconst := by
  rw [← two_mul_integral_mul_vConv_eq _ Simple673.Constant.continuous_fCos,
    Simple673.Constant.integral_mul_vConv_fCos]
  ring

end Ceilings
