/-
Distinct839/ZetaMoments/Coeff.lean — the coefficient family of ζ.

The generic prime side of `zeta23` (`Zeta23.XiPrime.coeffMoments_atV`) works with a height-indexed
coefficient family `c^{(T)} : ℕ → ℂ` and a diagonal density `D`, subject to the hypotheses
(H1)–(H3) of `Zeta23.XiPrime.CoeffFamily.Hyps`. Upstream only instantiates it for ξ′ and Z′. This
file supplies the instance for ζ itself:

* `zetaCoeffFamily`: `c^{(T)}_N = −Λ(N)` for every `T`, `D(s) = s`;
* `zetaCoeffFamily_hyps`: (H1)–(H3), from the Chebyshev–Mertens estimates of
  `Zeta23/Chebyshev.lean` (`Σ Λ(n)/√n ≪ √x`, `Σ Λ(n)² ≪ x log x`,
  `Σ Λ(n)²/n = (log x)²/2 + O(log x)`), and `c_1 = 0` since `Λ(1) = 0`;
* `GpC_zetaCoeff_eq_Gp`: with these coefficients the general prime-side matrix `P.GpC` is the
  ζ prime-side matrix `P.Gp` (the densities agree: `P_c = P_X` for `c = −Λ`).
-/
import Zeta23.XiPrime.Statement
import Zeta23.Chebyshev

open scoped BigOperators ArithmeticFunction.vonMangoldt
open Real Finset

noncomputable section

namespace Distinct839

open Zeta23 Zeta23.XiPrime

/-- **The coefficient family of ζ**: `c^{(T)}_N = −Λ(N)` (independent of `T`) and diagonal density
`D(s) = s`. -/
def zetaCoeffFamily : CoeffFamily := ⟨fun _ N => -((Λ N : ℝ) : ℂ), fun s => s⟩

namespace ZetaMoments

/-- `‖c^{(T)}_N‖ = Λ(N)`. -/
theorem norm_zetaCoeff (T : ℝ) (N : ℕ) : ‖zetaCoeffFamily.c T N‖ = Λ N := by
  show ‖-((Λ N : ℝ) : ℂ)‖ = Λ N
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- `l(T) ≥ l₀` once `T ≥ 2π e^{l₀}` (a copy of `Zeta23.XiPrime.l_ge_of_le`, which lives in the ξ′
coefficient development `XiPrime/Coeff/H3.lean`; copied to avoid that import). -/
theorem l_ge_of_le {l₀ T : ℝ} (hT : 2 * π * Real.exp l₀ ≤ T) : l₀ ≤ l T := by
  have h2pi : 0 < 2 * π := by positivity
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hT
  unfold l
  rw [Real.le_log_iff_exp_le (div_pos hTpos h2pi), le_div_iff₀ h2pi]
  linarith

/-- On the range of (H1)–(H2), `log 2 ≤ log x ≤ l(T)`. -/
theorem log_two_le_log_le_l {T x : ℝ} (hx : 2 ≤ x) (hxl : x ≤ Real.exp (l T)) :
    Real.log 2 ≤ Real.log x ∧ Real.log x ≤ l T := by
  refine ⟨Real.log_le_log two_pos hx, ?_⟩
  have h := Real.log_le_log (by linarith) hxl
  rwa [Real.log_exp] at h

/-- (H1): `Σ_{N ≤ x} Λ(N)/√N ≤ C √x l(T)` on `2 ≤ x ≤ e^{l(T)}`. -/
theorem zeta_H1 : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp (l T) →
    (∑ N ∈ Ioc 0 ⌊x⌋₊, ‖zetaCoeffFamily.c T N‖ / Real.sqrt N) ≤ C * Real.sqrt x * l T := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨(2 * Real.log 4 + 16) / Real.log 2, 0, fun T _ x hx hxl => ?_⟩
  obtain ⟨h2, hl⟩ := log_two_le_log_le_l hx hxl
  simp only [norm_zetaCoeff]
  have hsum := Cheb.sum_vonMangoldt_div_sqrt_le (x := x) (by linarith)
  have hC : 0 ≤ (2 * Real.log 4 + 16) / Real.log 2 := by positivity
  have hsq : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have e : (2 * Real.log 4 + 16) * Real.sqrt x
      = (2 * Real.log 4 + 16) / Real.log 2 * Real.sqrt x * Real.log 2 := by
    field_simp
  calc ∑ N ∈ Ioc 0 ⌊x⌋₊, Λ N / Real.sqrt N ≤ (2 * Real.log 4 + 16) * Real.sqrt x := hsum
    _ = (2 * Real.log 4 + 16) / Real.log 2 * Real.sqrt x * Real.log 2 := e
    _ ≤ (2 * Real.log 4 + 16) / Real.log 2 * Real.sqrt x * l T :=
        mul_le_mul_of_nonneg_left (h2.trans hl) (mul_nonneg hC hsq)

/-- (H2): `Σ_{N ≤ x} Λ(N)² ≤ C x l(T)²` on `2 ≤ x ≤ e^{l(T)}`. -/
theorem zeta_H2 : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp (l T) →
    (∑ N ∈ Ioc 0 ⌊x⌋₊, ‖zetaCoeffFamily.c T N‖ ^ 2) ≤ C * x * l T ^ 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨(Real.log 4 + 4) / Real.log 2, 0, fun T _ x hx hxl => ?_⟩
  obtain ⟨h2, hl⟩ := log_two_le_log_le_l hx hxl
  simp only [norm_zetaCoeff]
  have hsum := Cheb.sum_vonMangoldt_sq_le (x := x) (by linarith)
  have hC : 0 ≤ (Real.log 4 + 4) / Real.log 2 := by positivity
  have hx0 : 0 ≤ x := by linarith
  have hl0 : 0 ≤ l T := le_trans hlog2.le (h2.trans hl)
  have e : (Real.log 4 + 4) * x * l T = (Real.log 4 + 4) / Real.log 2 * x * l T * Real.log 2 := by
    field_simp
  calc ∑ N ∈ Ioc 0 ⌊x⌋₊, Λ N ^ 2 ≤ (Real.log 4 + 4) * x * Real.log x := hsum
    _ ≤ (Real.log 4 + 4) * x * l T := by gcongr
    _ = (Real.log 4 + 4) / Real.log 2 * x * l T * Real.log 2 := e
    _ ≤ (Real.log 4 + 4) / Real.log 2 * x * l T * l T :=
        mul_le_mul_of_nonneg_left (h2.trans hl) (by positivity)
    _ = (Real.log 4 + 4) / Real.log 2 * x * l T ^ 2 := by ring

/-- Below `e^y < 2` the diagonal sum is empty up to the term `N = 1`, which vanishes. -/
theorem diag_sum_eq_zero_of_lt_two {T y : ℝ} (hy : Real.exp y < 2) :
    ∑ N ∈ Ioc 0 ⌊Real.exp y⌋₊, ‖zetaCoeffFamily.c T N‖ ^ 2 / N = 0 := by
  have hfl : ⌊Real.exp y⌋₊ < 2 := (Nat.floor_lt (Real.exp_pos y).le).mpr (by exact_mod_cast hy)
  refine sum_eq_zero fun N hN => ?_
  obtain ⟨hN0, hN1⟩ := mem_Ioc.mp hN
  have hN : N = 1 := by omega
  subst hN
  rw [norm_zetaCoeff, ArithmeticFunction.vonMangoldt_apply_one]
  simp

/-- The diagonal sum against its main term, uniformly in `0 ≤ y ≤ l(T)`:
`|Σ_{N ≤ e^y} Λ(N)²/N − y²/2| ≤ C l(T) + 1` once `l(T) ≥ log 2`. -/
theorem diag_sum_close : ∃ C : ℝ, 0 < C ∧ ∀ T y : ℝ, Real.log 2 ≤ l T → 0 ≤ y → y ≤ l T →
    |(∑ N ∈ Ioc 0 ⌊Real.exp y⌋₊, ‖zetaCoeffFamily.c T N‖ ^ 2 / N) - y ^ 2 / 2| ≤ C * l T + 1 := by
  obtain ⟨C, hC, hcheb⟩ := Cheb.sum_vonMangoldt_sq_div_eq
  refine ⟨C, hC, fun T y hl2 hy0 hyl => ?_⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl0 : 0 ≤ l T := hlog2.le.trans hl2
  rcases lt_or_ge (Real.exp y) 2 with hlt | hge
  · -- small `y`: the sum vanishes and `y < log 2 < 1`
    rw [diag_sum_eq_zero_of_lt_two hlt, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
    have hy2 : y < Real.log 2 := by
      rw [Real.lt_log_iff_exp_lt two_pos]; exact hlt
    have hlog2_lt : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have hy1 : y ≤ 1 := by linarith
    nlinarith
  · have h := hcheb (Real.exp y) hge
    rw [Real.log_exp] at h
    simp only [norm_zetaCoeff]
    calc |(∑ N ∈ Ioc 0 ⌊Real.exp y⌋₊, Λ N ^ 2 / N) - y ^ 2 / 2| ≤ C * y := h
      _ ≤ C * l T := mul_le_mul_of_nonneg_left hyl hC.le
      _ ≤ C * l T + 1 := by linarith

/-- (H3): `Σ_{N ≤ e^y} Λ(N)²/N = l(T)² ∫₀^{y/l(T)} s ds + o(l(T)²)`, uniformly in `0 ≤ y ≤ l(T)`. -/
theorem zeta_H3 : ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ y : ℝ, 0 ≤ y → y ≤ l T →
    |(∑ N ∈ Ioc 0 ⌊Real.exp y⌋₊, ‖zetaCoeffFamily.c T N‖ ^ 2 / N)
        - l T ^ 2 * ∫ s in (0:ℝ)..(y / l T), zetaCoeffFamily.D s| ≤ ε * l T ^ 2 := by
  intro ε hε
  obtain ⟨C, hC, hclose⟩ := diag_sum_close
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2_lt : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  set l₀ : ℝ := max 1 ((C + 1) / ε) with hl₀
  refine ⟨2 * π * Real.exp l₀, fun T hT y hy0 hyl => ?_⟩
  have hlT : l₀ ≤ l T := l_ge_of_le hT
  have h1 : 1 ≤ l T := (le_max_left _ _).trans hlT
  have h2 : (C + 1) / ε ≤ l T := (le_max_right _ _).trans hlT
  have hl0 : 0 < l T := by linarith
  -- the main term is `y²/2`
  have hmain : l T ^ 2 * ∫ s in (0:ℝ)..(y / l T), zetaCoeffFamily.D s = y ^ 2 / 2 := by
    show l T ^ 2 * ∫ s in (0:ℝ)..(y / l T), s = y ^ 2 / 2
    rw [integral_id]
    field_simp
    ring
  rw [hmain]
  have hb := hclose T y (by linarith) hy0 hyl
  have hεl : C + 1 ≤ ε * l T := by rwa [div_le_iff₀ hε, mul_comm] at h2
  calc _ ≤ C * l T + 1 := hb
    _ ≤ (C + 1) * l T := by nlinarith
    _ ≤ ε * l T * l T := mul_le_mul_of_nonneg_right hεl hl0.le
    _ = ε * l T ^ 2 := by ring

end ZetaMoments

open ZetaMoments in
/-- **(H1)–(H3) for ζ**: the family `c^{(T)}_N = −Λ(N)`, `D(s) = s` satisfies the hypotheses of the
generic prime side. -/
theorem zetaCoeffFamily_hyps : zetaCoeffFamily.Hyps where
  c_one := fun T => by
    show -((Λ 1 : ℝ) : ℂ) = 0
    rw [ArithmeticFunction.vonMangoldt_apply_one]; simp
  H1 := zeta_H1
  H2 := zeta_H2
  H3 := zeta_H3
  D_cont := continuous_id
  D_nonneg := fun _ hs => hs.1

/-- With the coefficients `−Λ` and pole weight one, the general prime-side density is the ζ density:
`ν_{c,1}(X; τ) = μ(τ) + Π_X(τ) + P_X(τ) = ν_X(τ)`. -/
theorem ZetaMoments.nucW_zetaCoeff (T X τ : ℝ) : nucW 1 X (zetaCoeffFamily.c T) τ = nuX X τ := by
  unfold nucW nuX Pc PX
  rw [one_mul]
  congr 1
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun N _ => ?_
  have hre : (zetaCoeffFamily.c T N).re = -Λ N := by
    show (-((Λ N : ℝ) : ℂ)).re = -Λ N
    simp
  have him : (zetaCoeffFamily.c T N).im = 0 := by
    show (-((Λ N : ℝ) : ℂ)).im = 0
    simp
  rw [hre, him]
  ring

/-- **The prime-side matrices agree**: for every `Params` and height, the general fixed-coefficient
matrix with the ζ coefficients is the ζ prime-side matrix, `P.GpC T (−Λ) = P.Gp T`. -/
theorem GpC_zetaCoeff_eq_Gp (P : Params) (T : ℝ) : P.GpC T (zetaCoeffFamily.c T) = P.Gp T := by
  ext k l
  show ((P.GentryCW T 1 (zetaCoeffFamily.c T) k l : ℝ) : ℂ) = ((P.Gentry T k l : ℝ) : ℂ)
  congr 1
  unfold Params.GentryCW Params.Gentry
  simp only [ZetaMoments.nucW_zetaCoeff]

end Distinct839
