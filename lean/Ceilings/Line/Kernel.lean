/-
Ceilings/Line/Kernel.lean — the kernel of `Simple673` in the form the ceilings need.

* `Line.kernelEval`: `Simple673.K` is evaluated by the rational functions `Q = ratQgen aQ` (closed
  form `K(t) = sin(π t)/π · Q(t)`, `Simple673.Kernel.K_eq_sin_mul_Qrat`) and `kI = kIntGen aQ`
  (values at the integers: `K(n) = a_{|n|}/2` for `1 ≤ |n| ≤ 10`, `K(n) = 0` for `|n| ≥ 11`),
  where `aQ` are the ten coefficients of the second window as rational numbers.
* `Line.ceiling_of_range`, `Line.ceiling_of_all`: the ceiling of a mixture of trial states of
  simple points, for certificates of range `r` and for all pairs. The hypotheses are decidable
  conditions on rational data, checked by the kernel in `Range7.lean` and `All.lean`.
-/
import Ceilings.Mixture
import Ceilings.Line.Defs
import Simple673.Kernel.Sound

open scoped BigOperators
open Real

namespace Ceilings.Line

/-- The window coefficients `a_1, …, a_10` of `Simple673` as rational numbers. -/
def aQ (j : Fin 10) : ℚ := (Simple673.aInt j : ℚ) / 1000000

/-- The rational factor `Q` of the kernel. -/
def Q : ℚ → ℚ := ratQgen aQ

/-- The values of the kernel at the integers. -/
def kI : ℤ → ℚ := kIntGen aQ

/-- Upper bound for `K²` at rational points. -/
def k2 : ℚ → ℚ := k2Up Q kI

lemma cast_aQ (j : Fin 10) : ((aQ j : ℚ) : ℝ) = Simple673.aC j := by
  unfold aQ Simple673.aC
  push_cast
  rfl

/-- The values of `Simple673.K` at the integers. -/
theorem K_int (n : ℤ) : Simple673.K (n : ℝ) = ((kI n : ℚ) : ℝ) := by
  have h := kernel_int Simple673.aC n
  unfold kI
  rw [cast_kIntGen]
  simp only [cast_aQ]
  exact h

/-- **The kernel of `Simple673` is evaluated by `Q` and `kI`.** -/
theorem kernelEval : KernelEval Simple673.K Q kI where
  even := Simple673.K_neg
  closed := fun t ht => by
    have hnot : ∀ n : ℤ, (t : ℝ) ≠ n := fun n h => ht (by
      have e : t = (n : ℚ) := by exact_mod_cast h
      rw [e]
      exact Rat.den_intCast n)
    rw [Simple673.Kernel.K_eq_sin_mul_Qrat hnot, ← Simple673.Kernel.ratQ_cast]
    rfl
  int := K_int
  int_zero := kIntGen_int_zero aQ (by decide)

/-- `Q(t)² ≤ E²/t²` for `t ≥ T > 10`. -/
theorem qTail {T : ℚ} (hT : 10 < T) : QTail Q T (E2gen aQ T) :=
  ⟨sq_nonneg _, fun _ ht => ratQgen_sq_le aQ hT ht⟩

lemma sep_cast : Simple673.sep = (((17 / 20 : ℚ)) : ℝ) := by
  unfold Simple673.sep
  norm_num

/-- **Ceiling of a mixture of states of simple points, certificates of range `r`.** -/
theorem ceiling_of_range {ι : Type*} [Fintype ι] {r : ℕ} (S : ι → State) (w e : ι → ℚ)
    (hsep : ∀ k, (S k).sepOK (17 / 20) = true) (hsimple : ∀ k, (S k).simpleOK = true)
    (henergy : ∀ k, (S k).rangeUp k2 r ≤ e k)
    (hmix : LineMixOK S w e CloLineQ) {x b : ℝ} (h : PairCert1 r x b) (hx : x < 1) :
    (2 - energyCLine - b) / (1 - x) ≤ ((mixM S w / mixP S w : ℚ) : ℝ) := by
  have h' : PairCert1For Simple673.K (((17 / 20 : ℚ)) : ℝ) r x b := by
    rw [← sep_cast]
    exact h
  refine line_ceiling_of_states S w e CloLineQ hmix (fun k => ?_) hx CloLineQ_le
  have h1 := (S k).star1 Simple673.K_neg (by norm_num) (hsep k) (hsimple k) h'
  have h2 := (S k).energy_le_rangeUp (k2Up_sound kernelEval) r
  have h3 : (((S k).rangeUp k2 r : ℚ) : ℝ) ≤ ((e k : ℚ) : ℝ) := by exact_mod_cast henergy k
  exact h1.trans (h2.trans h3)

/-- **Ceiling of a mixture of states of simple points with integer periods, certificates for all
pairs.** State `k` is evaluated with `N₀ k` explicit periods and the tail bound from `T₀ k` on. -/
theorem ceiling_of_all {ι : Type*} [Fintype ι] (S : ι → State) (w e : ι → ℚ) (T₀ : ι → ℚ)
    (N₀ : ι → ℕ) (hsep : ∀ k, (S k).sepOK (17 / 20) = true)
    (hsimple : ∀ k, (S k).simpleOK = true) (hT : ∀ k, 10 < T₀ k)
    (hok : ∀ k, (S k).allOK (T₀ k) (N₀ k) = true)
    (henergy : ∀ k, (S k).allUp Q kI (E2gen aQ (T₀ k)) (N₀ k) ≤ e k)
    (hmix : LineMixOK S w e CloLineQ) {x b : ℝ} (h : PairCert1All x b) (hx : x < 1) :
    (2 - energyCLine - b) / (1 - x) ≤ ((mixM S w / mixP S w : ℚ) : ℝ) := by
  have h' : PairCert1AllFor Simple673.K (((17 / 20 : ℚ)) : ℝ) x b := by
    rw [← sep_cast]
    exact h
  refine line_ceiling_of_states S w e CloLineQ hmix (fun k => ?_) hx CloLineQ_le
  have h3 : (((S k).allUp Q kI (E2gen aQ (T₀ k)) (N₀ k) : ℚ) : ℝ) ≤ ((e k : ℚ) : ℝ) := by
    exact_mod_cast henergy k
  exact (S k).star1_all Simple673.K_neg (by norm_num) (hsep k) (hsimple k) h'
    (fun r => ((S k).energy_le_allUp kernelEval (qTail (hT k)) (hok k) r).trans h3)

end Ceilings.Line
