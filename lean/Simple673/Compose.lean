/-
Simple673/Compose.lean — composition of the layer statements: the bound
`liminf N₀ˢ(T)/N(T) ≥ 1669159/2478195` from the statements of `Spec.lean` and `Spec2.lean`.

Every layer enters as a hypothesis, so this file compiles before the layers are proved. The
only step that is not a layer of `Simple673` is the second moment of the zero-side matrix for
an admissible profile family, `Distinct839.gzMoments_atV_zeta_std`, which is generic in the
profile and is reused unchanged.

Layers (directory: statement, name of the theorem to be proved there):
  Window        `WindowStatement`          `windowStatement`      the window class
  WindowSide    `WindowSideStatement`      `windowSide`           `a ≥ 1/4`, `AdmFamily`, zero side
  WindowMoments `WindowMomentsStatement`   `windowMoments`        limit of the ratio constant
  Constant      `KappaStatement`           `kappaStatement`       `κ(λ) ≤ C₀` near `λ = 1`
  Kernel        `KIntegral`, `BetaBound`   `kIntegral`, `betaBound` (and the table, for `Local`)
  Majorant      `MajorantPointwise`, `LMajBound`, `SeparatedBound`
  ZeroKernel    `GramDataLayer`            `gramDataLayer`        Gram entries of zeros on the line
  Transfer      `LocalInequality → TransferStatement`             `transfer`
  Gram          `BetaBound → TransferStatement → GramEnergyStatement`   `gramEnergy`
  Assembly      `AssemblyStatement`        `assembly`             seam, counting, asymptotics
  Local         `LocalInequality`          `localInequality`      the eight-point inequality
-/
import Distinct839.ZetaMoments.Moments
import Simple673.Spec2

open Filter Topology Real
open Zeta23

noncomputable section

namespace Simple673

/-- **The main theorem from the layer statements.** -/
theorem simple_critical_zeros_673_of_layers
    (hWin : WindowStatement) (hSide : WindowSideStatement) (hMom : WindowMomentsStatement)
    (hKap : KappaStatement) (hKI : KIntegral) (hβ : BetaBound)
    (hMP : MajorantPointwise) (hLM : LMajBound) (hSB : SeparatedBound)
    (hGD : GramDataLayer) (hTr : LocalInequality → TransferStatement)
    (hGE : BetaBound → TransferStatement → GramEnergyStatement)
    (hAsm : AssemblyStatement) (hLoc : LocalInequality) : SimpleCritical673 := by
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
theorem simpleCritical673_iff :
    SimpleCritical673 ↔ ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1669159 / 2478195 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := Iff.rfl

/-- The constant: `(2 − C₀ − b)/(1 − x₁) = 1669159/2478195`, with `b = 7α`. -/
theorem qFinal_eq : qFinal = (2 - energyC0 - spanB) / (1 - rewX) := by
  unfold qFinal energyC0 spanB alphaP rewX; norm_num

end Simple673
