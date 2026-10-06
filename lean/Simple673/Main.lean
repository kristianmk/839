/-
Simple673/Main.lean — the main theorem.

    liminf_{T → ∞} N₀ˢ(T) / N(T) ≥ 1669159/2478195 = 0.6735382001…

Each import below is the module in which a layer delivers its theorem; the layers and their
statements are listed in `Simple673/Compose.lean`, `Simple673/Spec.lean` and
`Simple673/Spec2.lean`.

`simple_critical_zeros_673_of_layers` (`Simple673/Compose.lean`) derives the bound from the
layer statements with the standard axioms. `localInequality` (`Simple673/Local/FinalAll.lean`)
proves the eight-point local inequality from the soundness of the kernel table and of the
branch-and-bound checker (standard axioms) and one evaluation of the checker by compiled code.
-/
import Simple673.Compose
import Simple673.Window.Admissible
import Simple673.WindowSide.Main
import Simple673.WindowSide.Limit
import Simple673.Constant.Kappa
import Simple673.Kernel.Basic
import Simple673.Kernel.Beta
import Simple673.Majorant.Pointwise
import Simple673.Majorant.Separated
import Simple673.ZeroKernel.GramData
import Simple673.Transfer.Main
import Simple673.Gram.Main
import Simple673.Assembly.Final
import Simple673.Local.FinalAll

open Zeta23

namespace Simple673

/-- The main theorem, conditional only on the eight-point local inequality. -/
theorem simple_critical_zeros_673_of_local (hLoc : LocalInequality) : SimpleCritical673 :=
  simple_critical_zeros_673_of_layers windowStatement windowSide windowMoments kappaStatement
    kIntegral betaBound majorantPointwise lMajBound separatedBound gramDataLayer transfer
    gramEnergy assembly hLoc

/-- **More than 67.35% of the zeros of the Riemann zeta function are simple and on the critical
line.** -/
theorem simple_critical_zeros_673 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1669159 / 2478195 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  simple_critical_zeros_673_of_local localInequality

end Simple673
