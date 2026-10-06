/-
Line889/Compose.lean — composition of the layer statements: the bound
`liminf N_{s∨0}(T)/N(T) ≥ 50652159/56956375` from the statements of `Spec.lean` and `Spec2.lean`.

Every layer enters as a hypothesis, so this file compiles before the layers are proved. The
only step that is not a layer of `Line889` is the second moment of the zero-side matrix for an
admissible profile family, `Distinct839.gzMoments_atV_zeta_std`, which is generic in the profile
and is reused unchanged.

Layers (directory: statement, name of the theorem to be proved there):
  Window        `WindowStatement`          `windowStatement`      the window class
  WindowSide    `WindowSideStatement`      `windowSide`           `a ≥ 1/4`, `AdmFamily`, zero side
  WindowSide    `WindowMomentsStatement`   `windowMoments`        limit of the ratio constant
  Constant      `KappaStatement`           `kappaStatement`       `κ(λ) ≤ C₀` near `λ = 1`
  Kernel        `KIntegral`, `BetaBound`   `kIntegral`, `betaBound` (and the table, for `Local`)
  Majorant      `MajorantPointwise`, `LMajBound`, `SeparatedBound`
                                           `majorantPointwise`, `lMajBound`, `separatedBound`
  ZeroKernel    `GramDataLayer`            `gramDataLayer`        Gram entries of zeros on the line
  Transfer      `LocalInequality → TransferStatement`             `transfer`
  Gram          `BetaBound → TransferStatement → GramEnergyStatement`   `gramEnergy`
  Assembly      `AssemblyStatement`        `assembly`             seam, counting, asymptotics
  Local         `LocalInequality`          `localInequality`      the seven-point inequality
-/
import Distinct839.ZetaMoments.Moments
import Line889.Spec2

open Filter Topology Real
open Zeta23

noncomputable section

namespace Line889

/-- **The main theorem from the layer statements.** -/
theorem simple_or_critical_8893_of_layers
    (hWin : WindowStatement) (hSide : WindowSideStatement) (hMom : WindowMomentsStatement)
    (hKap : KappaStatement) (hKI : KIntegral) (hβ : BetaBound)
    (hMP : MajorantPointwise) (hLM : LMajBound) (hSB : SeparatedBound)
    (hGD : GramDataLayer) (hTr : LocalInequality → TransferStatement)
    (hGE : BetaBound → TransferStatement → GramEnergyStatement)
    (hAsm : AssemblyStatement) (hLoc : LocalInequality) : SimpleOrLine889 := by
  obtain ⟨cW, hAdm⟩ := hWin
  obtain ⟨lam, hlam, hlam1, hκ⟩ := hKap
  have hl0 : 0 < lam := by linarith
  have hA : AdmAt lam cW := hAdm lam hlam hlam1
  obtain ⟨ha, hFam, hWZ⟩ := hSide lam cW hl0 hlam1.le hA
  obtain ⟨hcpos, hc⟩ := hMom lam hl0 hlam1.le
  -- the two moments of the zero-side matrix (generic in the profile)
  have hM : XiPrime.GzMoments zetaZeroConfig (Pfam lam) (kappa lam) :=
    Distinct839.gzMoments_atV_zeta_std hl0 hlam1 hFam hcpos hc
  exact hAsm lam (kappa lam) hlam hlam1 (hκ lam le_rfl hlam1) hM hWZ ha
    (hGD lam cW hlam hlam1 hA hKI hMP hLM hSB) (hGE hβ (hTr hLoc))

/-- The statement in the form of the challenge file. -/
theorem simpleOrLine889_iff :
    SimpleOrLine889 ↔ ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (50652159 / 56956375 - ε) * (Ncount 0 T : ℝ) ≤ Further.NsimpleOrLine 0 T := Iff.rfl

/-- `e₀ = 2t − t²/4 = 999/256`. -/
theorem e0C_eq : e0C = 999 / 256 := by
  unfold e0C tLev; norm_num

/-- The constant: `(e₀ − C₀ − b)/(e₀ − 1 − x) = 50652159/56956375`. -/
theorem qFinal_eq : qFinal = (e0C - energyC0 - spanB) / (e0C - 1 - rewX) := by
  unfold qFinal e0C tLev energyC0 spanB alphaP rewX; norm_num

/-- The conditions on the two levels: `c ≤ t`, and `4t − t² ≥ 2 + 2x`, which says that a zero on
the line of multiplicity at least two, or a pair of simple zeros off the line, costs at most
`2t − 1 − x` per unit of multiplicity. -/
theorem levels_ok : clipC ≤ tLev ∧ 2 + 2 * rewX ≤ 4 * tLev - tLev ^ 2 := by
  unfold clipC tLev rewX; constructor <;> norm_num

end Line889
