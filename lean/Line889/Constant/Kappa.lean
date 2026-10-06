/-
Line889/Constant/Kappa.lean — the second-moment constant of the six-harmonic window (third
window).

For the profile `vProf = (2/5) fCos` and bandwidth `λ`, the upstream window functional
(`Zeta23.XiPrime.cWin`, with `D(s) = s`) is

    c_λ = λ (∫v)² / (∫v² + λ 𝒥(λ)),     𝒥(λ) = 2 ∫₀¹ λ r (v⋆v)(r) dr,

and the zeta second-moment constant is `κ(λ) = 1 / c_λ` (`Line889.kappa`, defined in
`Line889/Spec2.lean`). Here we compute it in closed form:

    κ(λ) = A / λ + λ B,   A = ∫ fCos² = 1 + (1/2) ∑ a_j²,
                         B = 2 ∫₀¹ r (fCos⋆fCos)(r) dr = 1/3 + π⁻² ∑ ((-1)^j a_j / j² - a_j² / (4 j²)),

(`kappa_eq`), prove `A + B < C₀ = 6662319/5000000` (`Aconst_add_Bconst_lt`; the margin is
`1.67·10⁻⁷`, and the proof uses `π < 3.141593`) and `1332463/1000000 < A + B`
(`lt_Aconst_add_Bconst`, using `3.141592 < π`; the value is `A + B = 1.3324636331…`), and deduce
`κ(λ) ≤ C₀` for `1 - 10⁻⁸ ≤ λ < 1` (`kappaStatement`).

The integrals are computed exactly: `fCos = ∑_{j ≤ 6} b_j cos(2π j u)` is expanded, the
autocorrelation `fCos⋆fCos` becomes a double sum of the closed forms of
`Distinct839/Constant/Trig.lean` (which do not depend on the window and are imported), and the
49 terms are evaluated by `norm_num`.
-/
import Line889.Spec2
import Distinct839.Constant.Trig
import Zeta23.XiPrime.Defs

open Real intervalIntegral
open scoped BigOperators

noncomputable section

namespace Line889

/-! ### The constants -/

/-- `A = ∫_{-1/2}^{1/2} fCos² = 1 + (1/2) ∑_j a_j²`. -/
def Aconst : ℝ := 1 + 1 / 2 * ∑ j : Fin 6, aC j ^ 2

/-- `B = 1/3 + π⁻² ∑_j ((-1)^j a_j / j² - a_j² / (4 j²))` (the index `j = 1, …, 6` is
`(j : Fin 6) + 1`). It equals `2 ∫₀¹ r (fCos⋆fCos)(r) dr` (`integral_mul_vConv_fCos`), which is
the double integral `∬ |s - s'| fCos(s) fCos(s') ds ds'` (the latter identity is not needed
here; it is `Ceilings.two_mul_integral_mul_vConv_eq`, proved for every continuous function). -/
def Bconst : ℝ :=
  1 / 3 + (π ^ 2)⁻¹ * ∑ j : Fin 6, ((-1) ^ ((j : ℕ) + 1) * aC j / (((j : ℕ) : ℝ) + 1) ^ 2
    - aC j ^ 2 / (4 * (((j : ℕ) : ℝ) + 1) ^ 2))

end Line889

namespace Line889.Constant

/-! ### The coefficients and the constants as numbers -/

/-- Coefficients of `fCos u = ∑_{j ≤ 6} cf j · cos(2π j u)`: `cf 0 = 1`, `cf j = a_j`. -/
def cf : ℕ → ℝ
  | 0 => 1
  | 1 => 200566 / 1000000
  | 2 => 19 / 1000000
  | 3 => -9358 / 1000000
  | 4 => 9283 / 1000000
  | 5 => -6746 / 1000000
  | 6 => 8170 / 1000000
  | _ => 0

lemma cf_succ (j : Fin 6) : cf ((j : ℕ) + 1) = aC j := by
  fin_cases j <;> norm_num [cf, aC, aInt]

/-- `A` as a rational number: `A = 1.020256362193`. -/
lemma Aconst_eq : Aconst = 1020256362193 / 1000000000000 := by
  simp only [Aconst, ← cf_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [cf]

/-- `B` in terms of `π`: `B = 1/3 - S/π²` with `S = 1000828214586143 / 4800000000000000`
(`S = 0.20850587…`, `B = 0.31220727…`). -/
lemma Bconst_eq : Bconst = 1 / 3 - 1000828214586143 / 4800000000000000 / π ^ 2 := by
  simp only [Bconst, ← cf_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [cf]
  ring

/-! ### `fCos` as a cosine polynomial -/

lemma fCos_eq_sum (u : ℝ) :
    fCos u = ∑ j ∈ Finset.range 7, cf j * cos (2 * π * ((j : ℤ) : ℝ) * u) := by
  simp [Finset.sum_range_succ, fCos, Fin.sum_univ_succ, cf, aC, aInt]
  ring_nf

lemma continuous_fCos : Continuous fCos := by
  unfold fCos; fun_prop

/-! ### The three integrals -/

/-- `∫_{-1/2}^{1/2} cos(2π j s) ds = waveInt j 0 0` (that is, `1` for `j = 0` and `0` otherwise). -/
lemma integral_cos_int (j : ℤ) :
    ∫ s in (-(1:ℝ)/2)..(1/2), cos (2 * π * j * s) = Distinct839.Constant.waveInt j 0 0 := by
  have h := Distinct839.Constant.integral_wave j 0 0
  simp only [Int.cast_zero, mul_zero, add_zero, sub_zero] at h
  exact h

/-- `∫_{-1/2}^{1/2} fCos = 1`. -/
theorem integral_fCos : ∫ s in (-(1:ℝ)/2)..(1/2), fCos s = 1 := by
  simp_rw [fCos_eq_sum]
  rw [intervalIntegral.integral_finsetSum fun j _ =>
    Continuous.intervalIntegrable (by fun_prop) _ _]
  simp_rw [intervalIntegral.integral_const_mul, integral_cos_int]
  simp [Distinct839.Constant.waveInt, cf]

/-- The autocorrelation `(fCos⋆fCos)(r)` as a double sum of closed forms. -/
theorem vConv_fCos (r : ℝ) :
    Zeta23.XiPrime.vConv fCos r = ∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7,
      cf j * cf k * ((Distinct839.Constant.waveInt ((j : ℤ) + k) k r
        + Distinct839.Constant.waveInt ((j : ℤ) - k) (-k) r) / 2) := by
  unfold Zeta23.XiPrime.vConv
  simp_rw [fCos_eq_sum, Finset.sum_mul_sum]
  rw [intervalIntegral.integral_finsetSum fun j _ =>
    Continuous.intervalIntegrable (continuous_finsetSum _ fun k _ => by fun_prop) _ _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_finsetSum fun k _ =>
    Continuous.intervalIntegrable (by fun_prop) _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : ∀ s : ℝ, cf j * cos (2 * π * ((j : ℤ) : ℝ) * s)
      * (cf k * cos (2 * π * ((k : ℤ) : ℝ) * (s + r)))
      = cf j * cf k * (cos (2 * π * ((j : ℤ) : ℝ) * s) * cos (2 * π * ((k : ℤ) : ℝ) * (s + r))) :=
    fun s => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, Distinct839.Constant.integral_cos_mul_cos_shift]

/-- `∫_{-1/2}^{1/2} fCos² = A`. -/
theorem integral_fCos_sq : ∫ s in (-(1:ℝ)/2)..(1/2), fCos s ^ 2 = Aconst := by
  have h : ∫ s in (-(1:ℝ)/2)..(1/2), fCos s ^ 2 = Zeta23.XiPrime.vConv fCos 0 := by
    unfold Zeta23.XiPrime.vConv
    simp only [sub_zero, add_zero, sq]
  rw [h, vConv_fCos, Aconst_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num [Distinct839.Constant.waveInt, cf]

/-- `2 ∫₀¹ r (fCos⋆fCos)(r) dr = B`. -/
theorem integral_mul_vConv_fCos :
    ∫ r in (0:ℝ)..1, r * Zeta23.XiPrime.vConv fCos r = Bconst / 2 := by
  simp_rw [vConv_fCos, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum fun j _ => Continuous.intervalIntegrable
    (continuous_finsetSum _ fun k _ => by
      have := Distinct839.Constant.continuous_waveInt ((j : ℤ) + k) k
      have := Distinct839.Constant.continuous_waveInt ((j : ℤ) - k) (-k)
      fun_prop) _ _]
  have hterm : ∀ j k : ℕ, ∫ r in (0:ℝ)..1,
      r * (cf j * cf k * ((Distinct839.Constant.waveInt ((j : ℤ) + k) k r
        + Distinct839.Constant.waveInt ((j : ℤ) - k) (-k) r) / 2))
        = cf j * cf k * ((Distinct839.Constant.outerW ((j : ℤ) + k) k
          + Distinct839.Constant.outerW ((j : ℤ) - k) (-k)) / 2) := by
    intro j k
    have h1 := Distinct839.Constant.continuous_waveInt ((j : ℤ) + k) k
    have h2 := Distinct839.Constant.continuous_waveInt ((j : ℤ) - k) (-k)
    have e : ∀ r : ℝ,
        r * (cf j * cf k * ((Distinct839.Constant.waveInt ((j : ℤ) + k) k r
          + Distinct839.Constant.waveInt ((j : ℤ) - k) (-k) r) / 2))
          = cf j * cf k / 2 * (r * Distinct839.Constant.waveInt ((j : ℤ) + k) k r
            + r * Distinct839.Constant.waveInt ((j : ℤ) - k) (-k) r) :=
      fun r => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      Distinct839.Constant.integral_mul_waveInt, Distinct839.Constant.integral_mul_waveInt]
    ring
  rw [Finset.sum_congr rfl fun j _ => (intervalIntegral.integral_finsetSum fun k _ =>
    Continuous.intervalIntegrable (by
      have := Distinct839.Constant.continuous_waveInt ((j : ℤ) + k) k
      have := Distinct839.Constant.continuous_waveInt ((j : ℤ) - k) (-k)
      fun_prop) _ _)]
  simp_rw [hterm]
  rw [Bconst_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num [Distinct839.Constant.outerW, Distinct839.Constant.rhoW, Distinct839.Constant.sigmaW, cf]
  field_simp
  ring

/-! ### The profile `vProf = (2/5) fCos` -/

lemma integral_vProf : ∫ s in (-(1:ℝ)/2)..(1/2), vProf s = 2 / 5 := by
  unfold vProf
  rw [intervalIntegral.integral_const_mul, integral_fCos, mul_one]

lemma integral_vProf_sq : ∫ s in (-(1:ℝ)/2)..(1/2), vProf s ^ 2 = 4 / 25 * Aconst := by
  unfold vProf
  have e : ∀ s : ℝ, (2 / 5 * fCos s) ^ 2 = 4 / 25 * fCos s ^ 2 := fun s => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, integral_fCos_sq]

lemma vConv_vProf (r : ℝ) :
    Zeta23.XiPrime.vConv vProf r = 4 / 25 * Zeta23.XiPrime.vConv fCos r := by
  unfold Zeta23.XiPrime.vConv vProf
  have e : ∀ s : ℝ, 2 / 5 * fCos s * (2 / 5 * fCos (s + r)) = 4 / 25 * (fCos s * fCos (s + r)) :=
    fun s => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul]

/-- `𝒥_{id}(λ; vProf) = (4/25) λ B`. -/
lemma jWin_vProf (lam : ℝ) :
    Zeta23.XiPrime.jWin (fun s => s) lam vProf = 4 / 25 * lam * Bconst := by
  unfold Zeta23.XiPrime.jWin
  have e : ∀ r : ℝ, lam * r * Zeta23.XiPrime.vConv vProf r
      = 4 / 25 * lam * (r * Zeta23.XiPrime.vConv fCos r) := fun r => by
    rw [vConv_vProf]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, integral_mul_vConv_fCos]
  ring

/-- `c_λ(vProf) = λ / (A + λ² B)`. -/
lemma cWin_vProf (lam : ℝ) :
    Zeta23.XiPrime.cWin (fun s => s) lam vProf = lam / (Aconst + lam ^ 2 * Bconst) := by
  unfold Zeta23.XiPrime.cWin
  rw [integral_vProf, integral_vProf_sq, jWin_vProf]
  have h : 4 / 25 * Aconst + lam * (4 / 25 * lam * Bconst)
      = 4 / 25 * (Aconst + lam ^ 2 * Bconst) := by ring
  rw [h, show lam * (2 / 5 : ℝ) ^ 2 = 4 / 25 * lam by ring, mul_div_mul_left _ _ (by norm_num)]

/-! ### Numerical facts -/

/-- `B > 0` (with room). -/
lemma Bconst_pos : 0 < Bconst := by
  rw [Bconst_eq]
  have hπ : 3 < π := pi_gt_three
  have h9 : (9 : ℝ) < π ^ 2 := by nlinarith
  have h : 1000828214586143 / 4800000000000000 / π ^ 2
      < 1000828214586143 / 4800000000000000 / 9 :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) h9
  linarith

/-- Upper bound for `B` from `π < 3.141593`. -/
lemma Bconst_le : Bconst ≤ 1 / 3 - 1000828214586143 / 4800000000000000 / 3.141593 ^ 2 := by
  rw [Bconst_eq]
  have hπ := pi_lt_d6
  have hπ0 := pi_pos
  have h2 : π ^ 2 ≤ (3.141593 : ℝ) ^ 2 := by nlinarith
  have h : 1000828214586143 / 4800000000000000 / (3.141593 : ℝ) ^ 2
      ≤ 1000828214586143 / 4800000000000000 / π ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) h2
  linarith

/-- Lower bound for `B` from `3.141592 < π`. -/
lemma le_Bconst : 1 / 3 - 1000828214586143 / 4800000000000000 / 3.141592 ^ 2 ≤ Bconst := by
  rw [Bconst_eq]
  have hπ := pi_gt_d6
  have h2 : (3.141592 : ℝ) ^ 2 ≤ π ^ 2 := by nlinarith
  have h : 1000828214586143 / 4800000000000000 / π ^ 2
      ≤ 1000828214586143 / 4800000000000000 / (3.141592 : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
  linarith

end Line889.Constant

namespace Line889

open Constant

/-- **Closed form of the constant**: `κ(λ) = A/λ + λ B` for `λ > 0`. -/
theorem kappa_eq {lam : ℝ} (hlam : 0 < lam) : kappa lam = Aconst / lam + lam * Bconst := by
  unfold kappa
  rw [cWin_vProf, inv_div]
  field_simp

/-- **The constant at `λ = 1`**: `A + B < C₀ = 6662319/5000000` (the margin is `1.67·10⁻⁷`; the
proof, with `π < 3.141593`, keeps `1.62·10⁻⁷`). -/
theorem Aconst_add_Bconst_lt : Aconst + Bconst < energyC0 := by
  have hB := Bconst_le
  rw [Aconst_eq] at *
  unfold energyC0
  norm_num at hB ⊢
  linarith

/-- **Lower bound for the constant at `λ = 1`**: `1.332463 < A + B` (the value is
`1.3324636331…`). -/
theorem lt_Aconst_add_Bconst : 1332463 / 1000000 < Aconst + Bconst := by
  have hB := le_Bconst
  rw [Aconst_eq] at *
  norm_num at hB ⊢
  linarith

/-- **The constant near `λ = 1`**: `κ(λ) ≤ C₀` for `1 - 10⁻⁸ ≤ λ < 1` (after the two losses,
`π < 3.141593` and `A/λ ≤ A/(1 - 10⁻⁸)`, the margin is `1.52·10⁻⁷`). -/
theorem kappaStatement : KappaStatement := by
  refine ⟨1 - 1 / 100000000, by norm_num, by norm_num, fun lam h0 h1 => ?_⟩
  have hlam : 0 < lam := by linarith
  rw [kappa_eq hlam]
  have hB0 := Bconst_pos
  have hB := Bconst_le
  have hA : Aconst = 1020256362193 / 1000000000000 := Aconst_eq
  -- `A/λ ≤ A/λ₀` and `λ B ≤ B`
  have h2 : Aconst / lam ≤ Aconst / (1 - 1 / 100000000) :=
    div_le_div_of_nonneg_left (by rw [hA]; norm_num) (by norm_num) h0
  have h3 : lam * Bconst ≤ Bconst := by nlinarith
  have h4 : Aconst / (1 - 1 / 100000000)
      + (1 / 3 - 1000828214586143 / 4800000000000000 / 3.141593 ^ 2) ≤ energyC0 := by
    rw [hA]; unfold energyC0; norm_num
  linarith

end Line889

namespace Line889.Constant

/-- The energy constant of the window is the value at `λ = 1`: `κ(1) = A + B`. -/
theorem kappa_one : kappa 1 = Aconst + Bconst := by
  rw [kappa_eq one_pos, div_one, one_mul]

/-- `κ` is continuous on `(0, ∞)`. -/
theorem continuousOn_kappa : ContinuousOn kappa (Set.Ioi 0) := by
  have h : ContinuousOn (fun lam : ℝ => Aconst / lam + lam * Bconst) (Set.Ioi 0) := by
    refine ContinuousOn.add ?_ (by fun_prop)
    exact continuousOn_const.div continuousOn_id fun x hx => ne_of_gt hx
  exact h.congr fun lam hlam => kappa_eq hlam

/-- `κ` is continuous on `(0, 1]`. -/
theorem continuousOn_kappa_Ioc : ContinuousOn kappa (Set.Ioc 0 1) :=
  continuousOn_kappa.mono fun _ h => h.1

end Line889.Constant
