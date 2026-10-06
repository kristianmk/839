/-
Distinct839/Compose.lean — composition of all layers except the computation: the bound
`liminf N_d(T)/N(T) ≥ 1645064/1960733` from the seven-point local inequality.

Layers used (directory: main result):
  Window      `admWindow_vProf`        the window lies in the upstream window class
  WindowSide  `admFamily_vProf_std`, `windowZeroSide_vProf_std`, `eventually_a_vProf_std`
  WindowMoments `tendsto_cRatio_vProf`, `cWin_vProf_pos`   moments of the realised window
  ZetaMoments `gzMoments_atV_zeta_std` trace and second moment of the zeta operator
  Constant    `exists_kappa_le`        the energy constant is below 266541/200000 for lam < 1 near 1
  ZeroKernel  `gramData`               Gram entries of zeros on the line, separated bound
  Majorant    `majorantPointwise`, `lMajBound`, `separatedBound`
  Kernel      `K_eq_integral`, `betaBound`
  Transfer    `transfer`               local inequality ⟹ bound for separated chains
  Gram        `gramEnergy`             labelled Gram bound (matching, pinching, pair blocks)
  Assembly    `distinct839_of`         seam, counting and asymptotics
-/
import Distinct839.Transfer.Main
import Distinct839.Gram.Main
import Distinct839.Majorant.Pointwise
import Distinct839.Majorant.Separated
import Distinct839.ZeroKernel.GramData
import Distinct839.ZetaMoments.Moments
import Distinct839.Window.Admissible
import Distinct839.WindowSide.Main
import Distinct839.Constant.Kappa
import Distinct839.Kernel.Table
import Distinct839.Kernel.Beta
import Distinct839.Assembly.Final
import Distinct839.WindowMoments.Limit

open Filter Topology Real
open Zeta23

noncomputable section

namespace Distinct839

/-- The main theorem, conditional only on the seven-point local inequality. -/
theorem distinct_zeros_839_of_local
    (hLoc : LocalInequality) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1645064 / 1960733 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T := by
  obtain ⟨lam, hlam, hlam1, hκ⟩ := exists_kappa_le
  have hl0 : 0 < lam := by linarith
  have hAdm := admWindow_vProf hlam hlam1
  have hcpos : 0 < XiPrime.cWin (fun s => s) lam vProf := cWin_vProf_pos hl0
  have hM : XiPrime.GzMoments zetaZeroConfig (Pfam lam) (kappa lam) :=
    gzMoments_atV_zeta_std hl0 hlam1 (admFamily_vProf_std hl0 hlam1.le hAdm) hcpos
      (tendsto_cRatio_vProf hlam hlam1 hAdm)
  have hGD : GramDataStatement lam :=
    gramData hlam hlam1 hAdm K_eq_integral majorantPointwise lMajBound separatedBound
  have hGE : GramEnergyStatement := gramEnergy betaBound (transfer hLoc)
  exact distinct839_of hlam hlam1 (hκ lam le_rfl hlam1) hM
    (windowZeroSide_vProf_std hl0 hlam1.le hAdm) (eventually_a_vProf_std hl0 hlam1.le) hGD hGE

end Distinct839
