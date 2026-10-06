/-
Distinct839/Main.lean — the main theorem.

    liminf_{T → ∞} N_d(T) / N(T) ≥ 1645064/1960733 = 0.8390045967…

`distinct_zeros_839_of_local` (`Distinct839/Compose.lean`) derives the bound from the seven-point
local inequality with the standard axioms. `localInequality` (`Distinct839/Local/FinalAll.lean`)
proves the local inequality from the soundness of the kernel table and of the branch-and-bound
checker (standard axioms) and one evaluation of the checker by compiled code.
-/
import Distinct839.Compose
import Distinct839.Local.FinalAll

open Zeta23

namespace Distinct839

/-- **More than 83.9% of the zeros of the Riemann zeta function are distinct.** -/
theorem distinct_zeros_839 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1645064 / 1960733 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T :=
  distinct_zeros_839_of_local localInequality

end Distinct839
