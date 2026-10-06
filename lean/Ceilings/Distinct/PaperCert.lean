/-
Ceilings/Distinct/PaperCert.lean — the certificate of the paper, without hypothesis.

`paper_certificate : PairCert 6 rewX rewY spanB`: the triple of the 83.90% theorem is a
pair-energy certificate of range six. It is `Distinct.paper_certificate_of_local` applied to
`Distinct839.localInequality`, the seven-point local inequality, whose proof evaluates the branch
and bound checker by compiled code. So this file, and only this file of `Ceilings/Distinct/`,
depends on the computational fact of `Distinct839/Local/RunAll.lean` (`#print axioms` lists it
next to the three standard axioms). The ceiling theorems do not import this file.

`paper_constant_lt_ceiling` applies `ceiling_range6` to this certificate: the hypotheses of the
ceiling theorem are satisfied by the certificate of the paper, and its constant with the exact
energy constant, `(3 - energyC + y - x - b)/(2 - 2x + y) = 0.839005…`, is below `0.83916`.
-/
import Ceilings.Distinct.Paper
import Ceilings.Distinct.Range6
import Distinct839.Local.FinalAll

namespace Ceilings

open Distinct839 (rewX rewY spanB alphaP)

/-- **The certificate of the paper**: `(rewX, rewY, spanB) = (0.054350, 0.069433, 0.037314)` is a
pair-energy certificate of range six for the window of `Distinct839`. -/
theorem paper_certificate : PairCert 6 rewX rewY spanB :=
  Distinct.paper_certificate_of_local Distinct839.localInequality

/-- The ceiling for range six applies to the certificate of the paper. -/
theorem paper_constant_lt_ceiling :
    (3 - energyC + rewY - rewX - spanB) / (2 - 2 * rewX + rewY) < 83916 / 100000 :=
  ceiling_range6 paper_certificate (by norm_num [spanB, alphaP]) (by norm_num [rewX, rewY])

end Ceilings
