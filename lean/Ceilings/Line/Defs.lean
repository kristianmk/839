/-
Ceilings/Line/Defs.lean — pair-energy certificates and the energy constant for the window of
`Simple673` (the 67.35% theorem for simple zeros on the critical line).

In that proof only the simple zeros on the line are kept, so there is one kind of point and no
labels.

* `PairCert1 r x b`, `PairCert1All x b`: the definitions of `Ceilings/Defs.lean` for the kernel
  `Simple673.K` and the separation `Simple673.sep = 17/20`, written out. The lower bound for the
  pair energy that the proof uses is of this kind, with the pair `(rewX, spanB)` and range seven
  (`line_certificate` in `Ceilings/Line/PaperCert.lean`).
* `energyCLine = A + B`: the energy constant `C(f)` of the second window. It is the constant of
  the method: `energyCLine = Simple673.kappa 1` (`energyCLine_eq_kappa_one`); the proof of the
  theorem uses the upper bound `energyCLine < Simple673.energyC0` (`energyCLine_lt`), the
  ceilings need the lower bound `1.327947272844 ≤ energyCLine` (`CloLineQ_le`).

A pair `(x, b)` gives the constant `(2 - energyCLine - b)/(1 - x)`.
-/
import Ceilings.Defs
import Simple673.Constant.Kappa

open scoped BigOperators
open Real

noncomputable section

namespace Ceilings

/-- **Pair-energy certificate of range `r` for simple points** (window of `Simple673`): for some
constant `C₃` and every chain `y` of `ℓ` points with gaps at least `17/20` in an interval of
length `R`, `x ℓ - b R - C₃ ≤ ∑_{i ≠ j, |i - j| ≤ r} K(y_j - y_i)²`. -/
def PairCert1 (r : ℕ) (x b : ℝ) : Prop :=
  ∃ C₃ : ℝ, ∀ (ℓ : ℕ) (y : Fin ℓ → ℝ) (R : ℝ),
    (∀ i j, i < j → Simple673.sep ≤ y j - y i) → 0 ≤ R → (∀ i j, y j - y i ≤ R) →
    x * ℓ - b * R - C₃
      ≤ ∑ i : Fin ℓ, ∑ j : Fin ℓ, if i ≠ j ∧ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ (r : ℤ) then
          Simple673.K (y j - y i) ^ 2 else 0

/-- **Pair-energy certificate for simple points, all pairs** (window of `Simple673`). -/
def PairCert1All (x b : ℝ) : Prop :=
  ∃ C₃ : ℝ, ∀ (ℓ : ℕ) (y : Fin ℓ → ℝ) (R : ℝ),
    (∀ i j, i < j → Simple673.sep ≤ y j - y i) → 0 ≤ R → (∀ i j, y j - y i ≤ R) →
    x * ℓ - b * R - C₃
      ≤ ∑ i : Fin ℓ, ∑ j : Fin ℓ, if i ≠ j then Simple673.K (y j - y i) ^ 2 else 0

/-- `PairCert1` is the general definition for the kernel and the separation of `Simple673`. -/
theorem pairCert1_iff_for {r : ℕ} {x b : ℝ} :
    PairCert1 r x b ↔ PairCert1For Simple673.K Simple673.sep r x b := Iff.rfl

theorem pairCert1All_iff_for {x b : ℝ} :
    PairCert1All x b ↔ PairCert1AllFor Simple673.K Simple673.sep x b := Iff.rfl

/-- A certificate of range `r` is a certificate of every range `r' ≥ r`. -/
theorem PairCert1.mono {r r' : ℕ} {x b : ℝ} (hr : r ≤ r') (h : PairCert1 r x b) :
    PairCert1 r' x b :=
  PairCert1For.mono hr h

/-- A certificate of range `r` is a certificate for all pairs. -/
theorem PairCert1.toAll {r : ℕ} {x b : ℝ} (h : PairCert1 r x b) : PairCert1All x b :=
  PairCert1For.toAll h

/-! ## The energy constant -/

/-- The energy constant `C(f) = A + B` of the window of `Simple673`. -/
def energyCLine : ℝ := Simple673.Aconst + Simple673.Bconst

/-- **`energyCLine` is the constant of the method**: the zeta second-moment constant `κ(λ)` of the
second window (`Simple673.kappa`) at `λ = 1`. -/
theorem energyCLine_eq_kappa_one : energyCLine = Simple673.kappa 1 :=
  Simple673.Constant.kappa_one.symm

/-- The upper bound for `energyCLine` that the proof of the 67.35% theorem uses. -/
theorem energyCLine_lt : energyCLine < Simple673.energyC0 := Simple673.Aconst_add_Bconst_lt

/-- Rational lower bound for `energyCLine` (the value is `1.32794727284455…`). -/
def CloLineQ : ℚ := 331986818211 / 250000000000

/-- **Lower bound for the energy constant**, from `π > 3.14159265358979323846`. -/
theorem CloLineQ_le : ((CloLineQ : ℚ) : ℝ) ≤ energyCLine := by
  unfold energyCLine
  rw [Simple673.Constant.Aconst_eq, Simple673.Constant.Bconst_eq]
  have hπ := Real.pi_gt_d20
  have hπ2 : (3.14159265358979323846 : ℝ) ^ 2 ≤ π ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hπ.le 2
  have h : 440830631846157799 / 3175200000000000000 / π ^ 2
      ≤ 440830631846157799 / 3175200000000000000 / (3.14159265358979323846 : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hπ2
  have h2 : ((CloLineQ : ℚ) : ℝ) ≤ 1008680921561 / 1000000000000
      + (1 / 3
        - 440830631846157799 / 3175200000000000000 / (3.14159265358979323846 : ℝ) ^ 2) := by
    unfold CloLineQ
    norm_num
  linarith

end Ceilings
