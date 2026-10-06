/-
Simple673/Constant/Kappa.lean — the second-moment constant of the window.

For the profile `vProf = (2/5) fCos` and bandwidth `λ`, the upstream window functional
(`Zeta23.XiPrime.cWin`, with `D(s) = s`) is

    c_λ = λ (∫v)² / (∫v² + λ 𝒥(λ)),     𝒥(λ) = 2 ∫₀¹ λ r (v⋆v)(r) dr,

and the zeta second-moment constant is `κ(λ) = 1 / c_λ` (`Simple673.kappa`, defined in
`Simple673/Spec2.lean`). Here we compute it in closed form:

    κ(λ) = A / λ + λ B,   A = ∫ fCos² = 1 + (1/2) ∑ a_j²,
                         B = 2 ∫₀¹ r (fCos⋆fCos)(r) dr
                           = 1/3 + π⁻² ∑ ((-1)^j a_j / j² - a_j² / (4 j²)),

(`kappa_eq`), prove `A + B < C₀ = 6639737/5000000` (`Aconst_add_Bconst_lt`; the margin is
`1.27·10⁻⁷`, and the proof uses `π < 3.141593`) and `1327947/1000000 < A + B`
(`lt_Aconst_add_Bconst`, using `3.141592 < π`; the value is `A + B = 1.3279472728…`), and deduce
`κ(λ) ≤ C₀` for `1 - 10⁻⁸ ≤ λ < 1` (`kappaStatement`).

The integrals are computed exactly: `fCos = ∑_{j ≤ 10} b_j cos(2π j u)` is expanded, and the
autocorrelation `fCos⋆fCos` becomes a double sum of the closed forms of
`Distinct839/Constant/Trig.lean` (which do not depend on the window and are imported). For `A`
the 121 terms are evaluated by `norm_num`. For `B` the weight of a pair of frequencies `(j, k)`
is first brought into closed form for all `j` and `k` (`pairW`, `outerW_pair`): it vanishes
unless `j = 0`, `k = 0` or `j = k`, so that 31 of the 121 terms remain.
-/
import Simple673.Spec2
import Distinct839.Constant.Trig
import Zeta23.XiPrime.Defs

open Real intervalIntegral
open scoped BigOperators

noncomputable section

namespace Simple673

/-! ### The constants -/

/-- `A = ∫_{-1/2}^{1/2} fCos² = 1 + (1/2) ∑_j a_j²`. -/
def Aconst : ℝ := 1 + 1 / 2 * ∑ j : Fin 10, aC j ^ 2

/-- `B = 1/3 + π⁻² ∑_j ((-1)^j a_j / j² - a_j² / (4 j²))` (the index `j = 1, …, 10` is
`(j : Fin 10) + 1`). It equals `2 ∫₀¹ r (fCos⋆fCos)(r) dr` (`integral_mul_vConv_fCos`), which is
the double integral `∬ |s - s'| fCos(s) fCos(s') ds ds'` (the latter identity is not needed
here; it is `Ceilings.two_mul_integral_mul_vConv_eq`, proved for every continuous function). -/
def Bconst : ℝ :=
  1 / 3 + (π ^ 2)⁻¹ * ∑ j : Fin 10, ((-1) ^ ((j : ℕ) + 1) * aC j / (((j : ℕ) : ℝ) + 1) ^ 2
    - aC j ^ 2 / (4 * (((j : ℕ) : ℝ) + 1) ^ 2))

end Simple673

namespace Simple673.Constant

/-! ### The coefficients and the constants as numbers -/

/-- Coefficients of `fCos u = ∑_{j ≤ 10} cf j · cos(2π j u)`: `cf 0 = 1`, `cf j = a_j`. -/
def cf : ℕ → ℝ
  | 0 => 1
  | 1 => 122290 / 1000000
  | 2 => -45012 / 1000000
  | 3 => 16241 / 1000000
  | 4 => 1887 / 1000000
  | 5 => 2711 / 1000000
  | 6 => 3731 / 1000000
  | 7 => -5307 / 1000000
  | 8 => 2982 / 1000000
  | 9 => -5153 / 1000000
  | 10 => 5358 / 1000000
  | _ => 0

lemma cf_succ (j : Fin 10) : cf ((j : ℕ) + 1) = aC j := by
  fin_cases j <;> norm_num [cf, aC, aInt]

/-- `A` as a rational number: `A = 1.008680921561`. -/
lemma Aconst_eq : Aconst = 1008680921561 / 1000000000000 := by
  simp only [Aconst, ← cf_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [cf]

/-- `B` in terms of `π`: `B = 1/3 - S/π²` with `S = 440830631846157799 / 3175200000000000000`
(`S = 0.13883554…`, `B = 0.3192663…`). -/
lemma Bconst_eq : Bconst = 1 / 3 - 440830631846157799 / 3175200000000000000 / π ^ 2 := by
  simp only [Bconst, ← cf_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [cf]
  ring

/-! ### `fCos` as a cosine polynomial -/

lemma fCos_eq_sum (u : ℝ) :
    fCos u = ∑ j ∈ Finset.range 11, cf j * cos (2 * π * ((j : ℤ) : ℝ) * u) := by
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
    Zeta23.XiPrime.vConv fCos r = ∑ j ∈ Finset.range 11, ∑ k ∈ Finset.range 11,
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

/-! ### The weight of a pair of frequencies -/

/-- `(-1)^(-n) = (-1)^n`. -/
lemma neg_one_zpow_neg (n : ℤ) : (-1 : ℝ) ^ (-n) = (-1) ^ n := by
  rw [zpow_neg, ← inv_zpow, inv_neg_one]

/-- `(-1)^(a - b) = (-1)^(a + b)`. -/
lemma neg_one_zpow_sub (a b : ℤ) : (-1 : ℝ) ^ (a - b) = (-1) ^ (a + b) := by
  rw [sub_eq_add_neg, zpow_add₀ (by norm_num), neg_one_zpow_neg, ← zpow_add₀ (by norm_num)]

/-! The closed forms `sigmaW`, `rhoW`, `outerW` of `Distinct839/Constant/Trig.lean` are defined
by cases on an integer being zero. The next five lemmas are these cases. -/

/-- `∫₀¹ r sin(2πnr) dr = 0` for `n = 0`. -/
lemma sigmaW_zero : Distinct839.Constant.sigmaW 0 = 0 := by
  rw [Distinct839.Constant.sigmaW, if_pos rfl]

/-- `∫₀¹ r sin(2πnr) dr = -1/(2πn)` for `n ≠ 0`. -/
lemma sigmaW_of_ne {n : ℤ} (h : n ≠ 0) : Distinct839.Constant.sigmaW n = -1 / (2 * π * n) := by
  rw [Distinct839.Constant.sigmaW, if_neg h]

/-- `∫₀¹ r (1 - r) cos(2πnr) dr = -1/(2π²n²)` for `n ≠ 0`. -/
lemma rhoW_of_ne {n : ℤ} (h : n ≠ 0) :
    Distinct839.Constant.rhoW n = -1 / (2 * π ^ 2 * n ^ 2) := by
  rw [Distinct839.Constant.rhoW, if_neg h]

/-- The outer integral for `m = 0`. -/
lemma outerW_zero (k : ℤ) : Distinct839.Constant.outerW 0 k = Distinct839.Constant.rhoW k := by
  rw [Distinct839.Constant.outerW, if_pos rfl]

/-- The outer integral for `m ≠ 0`. -/
lemma outerW_of_ne {m : ℤ} (h : m ≠ 0) (k : ℤ) : Distinct839.Constant.outerW m k
    = (-1) ^ m * (Distinct839.Constant.sigmaW (k - m) - Distinct839.Constant.sigmaW k)
      / (2 * π * m) := by
  rw [Distinct839.Constant.outerW, if_neg h]

/-- The weight of the pair of frequencies `(j, k)` in `∫₀¹ r (fCos⋆fCos)(r) dr`, that is,
`∫₀¹ r ∫_{-1/2}^{1/2-r} cos(2πjs) cos(2πk(s + r)) ds dr`: it is `1/6` for `j = k = 0`,
`(-1)^k / (4π²k²)` for `j = 0 < k` (and the same with `j` and `k` exchanged), `-1 / (8π²j²)` for
`j = k > 0`, and `0` for all other pairs. -/
def pairW (j k : ℕ) : ℝ :=
  if j = 0 then (if k = 0 then 1 / 6 else (-1) ^ k / (4 * π ^ 2 * (k : ℝ) ^ 2))
  else if k = 0 then (-1) ^ j / (4 * π ^ 2 * (j : ℝ) ^ 2)
  else if j = k then -1 / (8 * π ^ 2 * (j : ℝ) ^ 2)
  else 0

/-- The closed forms of `Distinct839/Constant/Trig.lean` for the pair of frequencies `(j, k)` add
up to `pairW j k`. -/
lemma outerW_pair (j k : ℕ) :
    (Distinct839.Constant.outerW ((j : ℤ) + k) k
      + Distinct839.Constant.outerW ((j : ℤ) - k) (-k)) / 2 = pairW j k := by
  have hπ : π ≠ 0 := pi_ne_zero
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · -- `j = k = 0`
      rw [pairW, if_pos rfl, if_pos rfl, Nat.cast_zero, add_zero, sub_zero, neg_zero,
        outerW_zero, Distinct839.Constant.rhoW, if_pos rfl]
      norm_num
    · -- `j = 0 < k`
      have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
      have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      rw [pairW, if_pos rfl, if_neg hk.ne', Nat.cast_zero, zero_add, zero_sub,
        outerW_of_ne hkZ, outerW_of_ne (neg_ne_zero.mpr hkZ), sub_self, sub_self, sigmaW_zero,
        sigmaW_of_ne hkZ, sigmaW_of_ne (neg_ne_zero.mpr hkZ), neg_one_zpow_neg, zpow_natCast]
      push_cast
      field_simp
      ring
  · have hjZ : (j : ℤ) ≠ 0 := by exact_mod_cast hj.ne'
    have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · -- `k = 0 < j`
      rw [pairW, if_neg hj.ne', if_pos rfl, Nat.cast_zero, add_zero, sub_zero, neg_zero,
        outerW_of_ne hjZ, zero_sub, sigmaW_zero, sigmaW_of_ne (neg_ne_zero.mpr hjZ),
        zpow_natCast]
      push_cast
      field_simp
      ring
    · have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
      have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      by_cases hjk : j = k
      · -- `j = k > 0`
        subst hjk
        have h2 : (j : ℤ) + j ≠ 0 := by omega
        have e : (j : ℤ) - (j + j) = -j := by ring
        rw [pairW, if_neg hj.ne', if_neg hj.ne', if_pos rfl, sub_self, outerW_zero,
          outerW_of_ne h2, e, rhoW_of_ne (neg_ne_zero.mpr hjZ), sigmaW_of_ne hjZ,
          sigmaW_of_ne (neg_ne_zero.mpr hjZ), Even.neg_one_zpow ⟨(j : ℤ), rfl⟩]
        push_cast
        field_simp
        ring
      · -- `j ≠ k`, both positive: the two closed forms cancel
        have h1 : (j : ℤ) + k ≠ 0 := by omega
        have h2 : (j : ℤ) - k ≠ 0 := by omega
        have h1R : (j : ℝ) + k ≠ 0 := by exact_mod_cast h1
        have h2R : (j : ℝ) - k ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hjk)
        have e1 : (k : ℤ) - (j + k) = -j := by ring
        have e2 : -(k : ℤ) - (j - k) = -j := by ring
        rw [pairW, if_neg hj.ne', if_neg hk.ne', if_neg hjk, outerW_of_ne h1, outerW_of_ne h2,
          e1, e2, sigmaW_of_ne (neg_ne_zero.mpr hjZ), sigmaW_of_ne hkZ,
          sigmaW_of_ne (neg_ne_zero.mpr hkZ), neg_one_zpow_sub]
        generalize (-1 : ℝ) ^ ((j : ℤ) + k) = z
        push_cast
        field_simp
        ring

/-! ### The integral of `r · (fCos⋆fCos)(r)` -/

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
        = cf j * cf k * pairW j k := by
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
      Distinct839.Constant.integral_mul_waveInt, Distinct839.Constant.integral_mul_waveInt,
      ← outerW_pair]
    ring
  rw [Finset.sum_congr rfl fun j _ => (intervalIntegral.integral_finsetSum fun k _ =>
    Continuous.intervalIntegrable (by
      have := Distinct839.Constant.continuous_waveInt ((j : ℤ) + k) k
      have := Distinct839.Constant.continuous_waveInt ((j : ℤ) - k) (-k)
      fun_prop) _ _)]
  simp_rw [hterm]
  rw [Bconst_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num [pairW, cf]
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
  have h : 440830631846157799 / 3175200000000000000 / π ^ 2
      < 440830631846157799 / 3175200000000000000 / 9 :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) h9
  linarith

/-- Upper bound for `B` from `π < 3.141593`. -/
lemma Bconst_le : Bconst ≤ 1 / 3 - 440830631846157799 / 3175200000000000000 / 3.141593 ^ 2 := by
  rw [Bconst_eq]
  have hπ := pi_lt_d6
  have hπ0 := pi_pos
  have h2 : π ^ 2 ≤ (3.141593 : ℝ) ^ 2 := by nlinarith
  have h : 440830631846157799 / 3175200000000000000 / (3.141593 : ℝ) ^ 2
      ≤ 440830631846157799 / 3175200000000000000 / π ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) h2
  linarith

/-- Lower bound for `B` from `3.141592 < π`. -/
lemma le_Bconst : 1 / 3 - 440830631846157799 / 3175200000000000000 / 3.141592 ^ 2 ≤ Bconst := by
  rw [Bconst_eq]
  have hπ := pi_gt_d6
  have h2 : (3.141592 : ℝ) ^ 2 ≤ π ^ 2 := by nlinarith
  have h : 440830631846157799 / 3175200000000000000 / π ^ 2
      ≤ 440830631846157799 / 3175200000000000000 / (3.141592 : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
  linarith

end Simple673.Constant

namespace Simple673

open Constant

/-- **Closed form of the constant**: `κ(λ) = A/λ + λ B` for `λ > 0`. -/
theorem kappa_eq {lam : ℝ} (hlam : 0 < lam) : kappa lam = Aconst / lam + lam * Bconst := by
  unfold kappa
  rw [cWin_vProf, inv_div]
  field_simp

/-- **The constant at `λ = 1`**: `A + B < C₀ = 6639737/5000000` (the margin is `1.27·10⁻⁷`; the
proof, with `π < 3.141593`, keeps `1.24·10⁻⁷`). -/
theorem Aconst_add_Bconst_lt : Aconst + Bconst < energyC0 := by
  have hB := Bconst_le
  rw [Aconst_eq] at *
  unfold energyC0
  norm_num at hB ⊢
  linarith

/-- **Lower bound for the constant at `λ = 1`**: `1.327947 < A + B` (the value is
`1.3279472728…`). -/
theorem lt_Aconst_add_Bconst : 1327947 / 1000000 < Aconst + Bconst := by
  have hB := le_Bconst
  rw [Aconst_eq] at *
  norm_num at hB ⊢
  linarith

/-- **The constant near `λ = 1`**: `κ(λ) ≤ C₀` for `1 - 10⁻⁸ ≤ λ < 1` (after the two losses,
`π < 3.141593` and `A/λ ≤ A/(1 - 10⁻⁸)`, the margin is `1.13·10⁻⁷`). -/
theorem kappaStatement : KappaStatement := by
  refine ⟨1 - 1 / 100000000, by norm_num, by norm_num, fun lam h0 h1 => ?_⟩
  have hlam : 0 < lam := by linarith
  rw [kappa_eq hlam]
  have hB0 := Bconst_pos
  have hB := Bconst_le
  have hA : Aconst = 1008680921561 / 1000000000000 := Aconst_eq
  -- `A/λ ≤ A/λ₀` and `λ B ≤ B`
  have h2 : Aconst / lam ≤ Aconst / (1 - 1 / 100000000) :=
    div_le_div_of_nonneg_left (by rw [hA]; norm_num) (by norm_num) h0
  have h3 : lam * Bconst ≤ Bconst := by nlinarith
  have h4 : Aconst / (1 - 1 / 100000000)
      + (1 / 3 - 440830631846157799 / 3175200000000000000 / 3.141593 ^ 2) ≤ energyC0 := by
    rw [hA]; unfold energyC0; norm_num
  linarith

end Simple673

namespace Simple673.Constant

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

end Simple673.Constant
