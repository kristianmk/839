/-
Ceilings/Distinct/Kernel.lean — the kernel of `Distinct839` in the form the ceilings need.

* `Distinct.kernelEval`: `Distinct839.K` is evaluated by the rational functions
  `Q = ratQgen aQ` (closed form `K(t) = sin(π t)/π · Q(t)`, `Distinct839.Kernel.K_eq_sin_mul_Qrat`)
  and `kI = kIntGen aQ` (values at the integers: `K(n) = a_{|n|}/2` for `1 ≤ |n| ≤ 6`, `K(n) = 0`
  for `|n| ≥ 7`), where `aQ` are the window coefficients as rational numbers.
* `Distinct.ceiling_of_range`, `Distinct.ceiling_of_all`: the ceiling of a mixture of trial states,
  for certificates of range `r` and for all pairs. The hypotheses are decidable conditions on
  rational data (gaps at least `17/20`, energy bounds, weights), checked by the kernel in the files
  `Range6.lean`, `Range8.lean`, `Range10.lean`, `All.lean`.
-/
import Ceilings.Mixture
import Ceilings.Distinct.Defs
import Distinct839.Kernel.Sound

open scoped BigOperators
open Real

namespace Ceilings.Distinct

/-- The window coefficients `a_1, …, a_6` of `Distinct839` as rational numbers. -/
def aQ (j : Fin 6) : ℚ := (Distinct839.aInt j : ℚ) / 1000000

/-- The rational factor `Q` of the kernel. -/
def Q : ℚ → ℚ := ratQgen aQ

/-- The values of the kernel at the integers. -/
def kI : ℤ → ℚ := kIntGen aQ

/-- Upper bound for `K²` at rational points. -/
def k2 : ℚ → ℚ := k2Up Q kI

lemma cast_aQ (j : Fin 6) : ((aQ j : ℚ) : ℝ) = Distinct839.aC j := by
  unfold aQ Distinct839.aC
  push_cast
  rfl

/-- The values of `Distinct839.K` at the integers. -/
theorem K_int (n : ℤ) : Distinct839.K (n : ℝ) = ((kI n : ℚ) : ℝ) := by
  have h := kernel_int Distinct839.aC n
  unfold kI
  rw [cast_kIntGen]
  simp only [cast_aQ]
  exact h

/-- **The kernel of `Distinct839` is evaluated by `Q` and `kI`.** -/
theorem kernelEval : KernelEval Distinct839.K Q kI where
  even := Distinct839.K_neg
  closed := fun t ht => by
    have hnot : ∀ n : ℤ, (t : ℝ) ≠ n := fun n h => ht (by
      have e : t = (n : ℚ) := by exact_mod_cast h
      rw [e]
      exact Rat.den_intCast n)
    rw [Distinct839.Kernel.K_eq_sin_mul_Qrat hnot, ← Distinct839.Kernel.ratQ_cast]
    rfl
  int := K_int
  int_zero := kIntGen_int_zero aQ (by decide)

/-- `Q(t)² ≤ E²/t²` for `t ≥ T > 6`. -/
theorem qTail {T : ℚ} (hT : 6 < T) : QTail Q T (E2gen aQ T) :=
  ⟨sq_nonneg _, fun _ ht => ratQgen_sq_le aQ hT ht⟩

lemma sep_cast : Distinct839.sep = (((17 / 20 : ℚ)) : ℝ) := by
  unfold Distinct839.sep
  norm_num

/-- **Ceiling of a mixture of states, certificates of range `r`.** -/
theorem ceiling_of_range {ι : Type*} [Fintype ι] {r : ℕ} (S : ι → State) (w e : ι → ℚ)
    (hsep : ∀ k, (S k).sepOK (17 / 20) = true) (henergy : ∀ k, (S k).rangeUp k2 r ≤ e k)
    (hmix : MixOK S w e CloQ) {x₁ x₂ b : ℝ} (h : PairCert r x₁ x₂ b) (hb : 0 ≤ b)
    (hD : 0 < 2 - 2 * x₁ + x₂) :
    (3 - energyC + x₂ - x₁ - b) / (2 - 2 * x₁ + x₂) ≤ ((mixL S w / mixN S w : ℚ) : ℝ) := by
  have h' : PairCertFor Distinct839.K (((17 / 20 : ℚ)) : ℝ) r x₁ x₂ b := by
    rw [← sep_cast]
    exact h
  refine ceiling_of_states S w e CloQ hmix (fun k => ?_) hb hD CloQ_le
  have h1 := (S k).star Distinct839.K_neg (by norm_num) (hsep k) h'
  have h2 := (S k).energy_le_rangeUp (k2Up_sound kernelEval) r
  have h3 : (((S k).rangeUp k2 r : ℚ) : ℝ) ≤ ((e k : ℚ) : ℝ) := by exact_mod_cast henergy k
  exact h1.trans (h2.trans h3)

/-- **Ceiling of a mixture of states with integer periods, certificates for all pairs.** State
`k` is evaluated with `N₀ k` explicit periods and the tail bound from `T₀ k` on. -/
theorem ceiling_of_all {ι : Type*} [Fintype ι] (S : ι → State) (w e : ι → ℚ) (T₀ : ι → ℚ)
    (N₀ : ι → ℕ) (hsep : ∀ k, (S k).sepOK (17 / 20) = true) (hT : ∀ k, 6 < T₀ k)
    (hok : ∀ k, (S k).allOK (T₀ k) (N₀ k) = true)
    (henergy : ∀ k, (S k).allUp Q kI (E2gen aQ (T₀ k)) (N₀ k) ≤ e k)
    (hmix : MixOK S w e CloQ) {x₁ x₂ b : ℝ} (h : PairCertAll x₁ x₂ b) (hb : 0 ≤ b)
    (hD : 0 < 2 - 2 * x₁ + x₂) :
    (3 - energyC + x₂ - x₁ - b) / (2 - 2 * x₁ + x₂) ≤ ((mixL S w / mixN S w : ℚ) : ℝ) := by
  have h' : PairCertAllFor Distinct839.K (((17 / 20 : ℚ)) : ℝ) x₁ x₂ b := by
    rw [← sep_cast]
    exact h
  refine ceiling_of_states S w e CloQ hmix (fun k => ?_) hb hD CloQ_le
  have h3 : (((S k).allUp Q kI (E2gen aQ (T₀ k)) (N₀ k) : ℚ) : ℝ) ≤ ((e k : ℚ) : ℝ) := by
    exact_mod_cast henergy k
  exact (S k).star_all Distinct839.K_neg (by norm_num) (hsep k) h'
    (fun r => ((S k).energy_le_allUp kernelEval (qTail (hT k)) (hok k) r).trans h3)

end Ceilings.Distinct
