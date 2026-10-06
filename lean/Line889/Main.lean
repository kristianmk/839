/-
Line889/Main.lean — the main theorem.

    liminf_{T → ∞} N_{s∨0}(T) / N(T) ≥ 50652159/56956375 = 0.8893150064…

`N(T)` counts the zeros of the Riemann zeta function in the open critical strip with ordinate in
`(0, T]` with multiplicity, and `N_{s∨0}(T)` counts, with multiplicity, those that are simple or
on the critical line.

Each import below is the module in which a layer delivers its theorem; the layers and their
statements are listed in `Line889/Compose.lean`, `Line889/Spec.lean` and `Line889/Spec2.lean`.

`simple_or_critical_8893_of_layers` (`Line889/Compose.lean`) derives the bound from the layer
statements with the standard axioms. `localInequality` (`Line889/Local/FinalAll.lean`) proves
the seven-point local inequality from the soundness of the kernel table and of the
branch-and-bound checker (standard axioms) and one evaluation of the checker by compiled code.
-/
import Line889.Compose
import Line889.Window.Admissible
import Line889.WindowSide.Main
import Line889.WindowSide.Limit
import Line889.Constant.Kappa
import Line889.Kernel.Basic
import Line889.Kernel.Beta
import Line889.Majorant.Pointwise
import Line889.Majorant.Separated
import Line889.ZeroKernel.GramData
import Line889.Transfer.Main
import Line889.Gram.Main
import Line889.Assembly.Final
import Line889.Local.FinalAll

open Zeta23

namespace Line889

/-- The main theorem, conditional only on the seven-point local inequality. -/
theorem simple_or_critical_8893_of_local (hLoc : LocalInequality) : SimpleOrLine889 :=
  simple_or_critical_8893_of_layers windowStatement windowSide windowMoments kappaStatement
    kIntegral betaBound majorantPointwise lMajBound separatedBound gramDataLayer transfer
    gramEnergy assembly hLoc

/-- **More than 88.93% of the zeros of the Riemann zeta function are simple or on the critical
line** (counted with multiplicity). -/
theorem simple_or_critical_8893 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (50652159 / 56956375 - ε) * (Ncount 0 T : ℝ) ≤ Further.NsimpleOrLine 0 T :=
  simple_or_critical_8893_of_local localInequality

end Line889
