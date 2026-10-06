/-
Further/Main.lean — the two further theorems.

    liminf_{T → ∞} (N_s(T) + N₀(T)) / (2 N(T)) ≥ 2073677/2478195 = 0.8367691000…,
    liminf_{T → ∞} N_{s∨0}(T) / N(T)           ≥ 3376433/3797325 = 0.8891609224….

`N(T)` counts the zeros of the Riemann zeta function in the open critical strip with ordinate in
`(0, T]` with multiplicity, `N_s(T)` the simple ones, `N₀(T)` those on the critical line (with
multiplicity) and `N_{s∨0}(T)` those that are simple or on the critical line (with multiplicity).

No new computation enters. The first theorem uses the layers of `Simple673` (second window,
clipping level `2`) and the eight-point local inequality of that development; the layers are
composed as in `Simple673/Compose.lean`, with `Further.average_of_layers` in place of the
assembly. The second theorem uses the layers of `Distinct839` (first window, clipping level
`67/20`) and its local inequality; the layers are composed as in `Distinct839/Compose.lean`, with
`Further.simple_or_line_of_layers` in place of `Distinct839.distinct839_of`.

What is new is the counting of the zeros outside the Gram part (`Further/Line/Block.lean`,
`Further/Dist/Block.lean`) and, for the second theorem, the threshold inequality with two levels
`c ≤ t` (`Further/Threshold.lean`).
-/
import Distinct839.Main
import Simple673.Main
import Further.Line.Final
import Further.Dist.Final

open Filter Topology Real
open Zeta23

noncomputable section

namespace Further

/-! ### The average of the proportions of simple zeros and of zeros on the critical line -/

open Simple673 in
/-- The first theorem, conditional only on the eight-point local inequality of the second
window. -/
theorem average_simple_and_critical_8367_of_local (hLoc : Simple673.LocalInequality) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2073677 / 2478195 - ε) * (Ncount 0 T : ℝ)
        ≤ ((Nsimple 0 T : ℝ) + (N0mult 0 T : ℝ)) / 2 := by
  obtain ⟨cW, hAdm⟩ := windowStatement
  obtain ⟨lam, hlam, hlam1, hκ⟩ := kappaStatement
  have hl0 : 0 < lam := by linarith
  have hA : AdmAt lam cW := hAdm lam hlam hlam1
  obtain ⟨ha, hFam, hWZ⟩ := windowSide lam cW hl0 hlam1.le hA
  obtain ⟨hcpos, hc⟩ := windowMoments lam hl0 hlam1.le
  -- the two moments of the zero-side matrix (generic in the profile)
  have hM : XiPrime.GzMoments zetaZeroConfig (Pfam lam) (kappa lam) :=
    Distinct839.gzMoments_atV_zeta_std hl0 hlam1 hFam hcpos hc
  exact average_of_layers hlam hlam1 (hκ lam le_rfl hlam1) hM hWZ ha
    (gramDataLayer lam cW hlam hlam1 hA kIntegral majorantPointwise lMajBound separatedBound)
    (gramEnergy betaBound (transfer hLoc))

/-- **The average of the proportion of simple zeros and the proportion of zeros on the critical
line (counted with multiplicity) is more than 83.67%.** -/
theorem average_simple_and_critical_8367 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2073677 / 2478195 - ε) * (Ncount 0 T : ℝ)
        ≤ ((Nsimple 0 T : ℝ) + (N0mult 0 T : ℝ)) / 2 :=
  average_simple_and_critical_8367_of_local Simple673.localInequality

/-! ### The zeros that are simple or on the critical line -/

open Distinct839 in
/-- The second theorem, conditional only on the seven-point local inequality of the first
window. -/
theorem simple_or_critical_8891_of_local (hLoc : Distinct839.LocalInequality) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3376433 / 3797325 - ε) * (Ncount 0 T : ℝ) ≤ NsimpleOrLine 0 T := by
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
  exact simple_or_line_of_layers hlam hlam1 (hκ lam le_rfl hlam1) hM
    (windowZeroSide_vProf_std hl0 hlam1.le hAdm) (eventually_a_vProf_std hl0 hlam1.le) hGD hGE

/-- **More than 88.91% of the zeros of the Riemann zeta function are simple or on the critical
line** (counted with multiplicity). -/
theorem simple_or_critical_8891 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3376433 / 3797325 - ε) * (Ncount 0 T : ℝ) ≤ NsimpleOrLine 0 T :=
  simple_or_critical_8891_of_local Distinct839.localInequality

end Further
