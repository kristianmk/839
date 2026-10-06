/-
Simple673/Spec2.lean — the interface statements of the zero side and of the window side.

The profile `vProf` is realised at height `T` by the upstream parameter family
`Pfam lam T = (paramsOf stdProfile lam).atV vProf T`. The on-line zeros give vectors
`(φ̂(γ - τ_k))_{0 ≤ k < d}`; `gramKappa` is the normalised inner product of two of them and `ypos`
the ordinate in units of the bandwidth (both are the definitions of `Distinct839/Spec2.lean`,
which do not depend on the window). This file contains definitions only.

The final statement is `SimpleCritical673`. The counting functions are the library's
`Zeta23.Ncount` and `Zeta23.N0simple` (`Zeta23/Statement.lean`), which are character for
character the Mathlib-only definitions of `ChallengeDeps.lean`.
-/
import Zeta23.XiPrime.Assembly
import Zeta23.XiPrime.PrimeSide.Concrete
import Zeta23.Final
import Distinct839.Spec2
import Simple673.Spec

open scoped BigOperators
open Real Filter Topology Zeta23

noncomputable section

namespace Simple673

export Distinct839 (gramKappa ypos)

/-! ## Definitions -/

/-- The family of parameter sets realising the profile `vProf` at bandwidth `lam`. -/
def Pfam (lam : ℝ) : ℝ → Params := (paramsOf stdProfile lam).atV vProf

/-- The second-moment constant of the window `vProf` at bandwidth `lam`:
`κ(λ) = 1 / cWin(D, λ, vProf)` with the diagonal density `D(s) = s`. -/
def kappa (lam : ℝ) : ℝ := (XiPrime.cWin (fun s => s) lam vProf)⁻¹

/-- The realised windows at bandwidth `lam` lie in the window class of the library, with
constant `cW`, at every height where the bandwidth is at least eight ramp widths. -/
def AdmAt (lam cW : ℝ) : Prop :=
  ∀ T, 8 * (paramsOf stdProfile lam).w ≤ (paramsOf stdProfile lam).L T →
    AdmWindow ((paramsOf stdProfile lam).phiV vProf T) ((paramsOf stdProfile lam).L T)
      (paramsOf stdProfile lam).w cW

/-- The Gram data of the realised window, for large `T`:
(1) for ordinates in the bulk `[T + √T, 2T - √T]` the Gram entries are within `η(T) → 0` of the
kernel values `K(y - y')`;
(2) on every finite set of ordinates that is `sep`-separated in bandwidth units, the Gram
matrix is bounded by `normS = 19/10`. -/
def GramDataStatement (lam : ℝ) : Prop :=
  (∃ η : ℝ → ℝ, Tendsto η atTop (𝓝 0) ∧ ∀ᶠ T in atTop, ∀ γ γ' : ℝ,
      T + D0 T ≤ γ → γ ≤ 2 * T - D0 T → T + D0 T ≤ γ' → γ' ≤ 2 * T - D0 T →
      |gramKappa (Pfam lam T) T γ γ' - K (ypos (Pfam lam T) T γ - ypos (Pfam lam T) T γ')| ≤ η T) ∧
  (∀ᶠ T in atTop, ∀ (ι : Type) [Fintype ι] (γ : ι → ℝ) (x : ι → ℝ),
      (∀ i j, i ≠ j → sep ≤ |ypos (Pfam lam T) T (γ i) - ypos (Pfam lam T) T (γ j)|) →
      ∑ i, ∑ j, x i * gramKappa (Pfam lam T) T (γ i) (γ j) * x j ≤ normS * ∑ i, x i ^ 2)

/-- **The target**: for every `ε > 0` and all large `T`,
`(1669159/2478195 − ε)·N(T) ≤ N₀ˢ(T)`, where `N(T)` counts the nontrivial zeros of the Riemann
zeta function with ordinate in `(0, T]` with multiplicity and `N₀ˢ(T)` counts those that are
simple and on the critical line. -/
def SimpleCritical673 : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (1669159 / 2478195 - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0simple 0 T

/-! ## Layer W1: the window lies in the window class of the library -/

/-- One constant `cW` serves all bandwidths `1/2 ≤ lam < 1`. -/
def WindowStatement : Prop := ∃ cW : ℝ, ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 → AdmAt lam cW

/-! ## Layer W2: window-side bookkeeping and moments of the realised window -/

/-- Given admissibility: `a_T ≥ 1/4` eventually, the windows form an admissible family
(`b_T ≥ 1/8`), and the zero-side package of the library holds for the zeros of `ζ`. -/
def WindowSideStatement : Prop :=
  ∀ lam cW : ℝ, 0 < lam → lam ≤ 1 → AdmAt lam cW →
    (∀ᶠ T in atTop, 1 / 4 ≤ (Pfam lam T).a T) ∧
    XiPrime.AdmFamily (paramsOf stdProfile lam) (fun T => (Pfam lam T).phi T) cW ∧
    XiPrime.WindowZeroSide zetaZeroConfig (paramsOf stdProfile lam) (Pfam lam)

/-- The ratio constant of the realised window tends to `cWin(D, λ, vProf)`, `D(s) = s`, and this
limit is positive. -/
def WindowMomentsStatement : Prop :=
  ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
    0 < XiPrime.cWin (fun s => s) lam vProf ∧
    Tendsto (fun T => ThmD.cRatio ((paramsOf stdProfile lam).lam1 T)
      ((Pfam lam T).a T) ((Pfam lam T).b T)
      (XiPrime.JD (fun s => s) ((Pfam lam T).g T) ((paramsOf stdProfile lam).L T) (l T))) atTop
      (𝓝 (XiPrime.cWin (fun s => s) lam vProf))

/-! ## Layer W3: the energy constant -/

/-- `κ(λ) ≤ C₀ = 6639737/5000000` for all `λ < 1` close to `1`. -/
def KappaStatement : Prop :=
  ∃ lam0 : ℝ, 1 / 2 ≤ lam0 ∧ lam0 < 1 ∧ ∀ lam, lam0 ≤ lam → lam < 1 → kappa lam ≤ energyC0

/-! ## Layer Z1: Gram entries of zeros on the line -/

/-- The Gram data, from admissibility, the integral formula for `K` and the majorant. -/
def GramDataLayer : Prop :=
  ∀ lam cW : ℝ, 1 / 2 ≤ lam → lam < 1 → AdmAt lam cW →
    KIntegral → MajorantPointwise → LMajBound → SeparatedBound → GramDataStatement lam

/-! ## Layer Z2: seam, counting and asymptotics -/

/-- The final assembly: from the two moments of the zero-side matrix with `κ ≤ C₀`, the
zero-side package, `a ≥ 1/4`, the Gram data and the finite Gram theorem, the target follows. -/
def AssemblyStatement : Prop :=
  ∀ lam κ : ℝ, 1 / 2 ≤ lam → lam < 1 → κ ≤ energyC0 →
    XiPrime.GzMoments zetaZeroConfig (Pfam lam) κ →
    XiPrime.WindowZeroSide zetaZeroConfig (paramsOf stdProfile lam) (Pfam lam) →
    (∀ᶠ T in atTop, 1 / 4 ≤ (Pfam lam T).a T) →
    GramDataStatement lam → GramEnergyStatement → SimpleCritical673

end Simple673
