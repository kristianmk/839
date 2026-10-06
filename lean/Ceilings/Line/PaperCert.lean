/-
Ceilings/Line/PaperCert.lean — the certificate of the 67.35% theorem is a pair-energy certificate
of range seven for simple points.

`Line.line_certificate_of_local : LocalInequality → PairCert1 7 rewX spanB` is the range-seven
form of the transfer lemma of `Simple673` (`Simple673.Transfer.transfer_range7_abs`), with
the constant `C₃ = 7 x₁ + Ω`. The statement without hypothesis, `line_certificate`, uses
`Simple673.localInequality`, whose proof evaluates the branch and bound checker by compiled
code; so `#print axioms line_certificate` lists that computational fact next to the three
standard axioms. The ceiling theorems do not import this file.

`Line.qFinal_eq` records that the constant of the theorem is the constant of this certificate,
`(2 - C₀ - b)/(1 - x₁)`, with the upper bound `C₀` for `energyCLine`, and
`line_constant_lt_ceiling` applies `ceiling_line_range7` to the certificate.
-/
import Ceilings.Line.Range7
import Simple673.Transfer.Main
import Simple673.Local.FinalAll

namespace Ceilings

open Simple673 (rewX spanB omegaB alphaP)

/-- **The certificate of the 67.35% theorem is a pair-energy certificate of range seven**, given
the eight-point local inequality of `Simple673`. -/
theorem Line.line_certificate_of_local (hloc : Simple673.LocalInequality) :
    PairCert1 7 rewX spanB := by
  refine ⟨7 * rewX + omegaB, fun ℓ y R hsep hR0 hR => ?_⟩
  have h := Simple673.Transfer.transfer_range7_abs hloc ℓ y R hsep hR0 hR
  exact_mod_cast h

/-- The constant of the 67.35% theorem is the constant of this certificate, with the upper bound
`C₀ = Simple673.energyC0` for the energy constant. -/
theorem Line.qFinal_eq :
    Simple673.qFinal = (2 - Simple673.energyC0 - spanB) / (1 - rewX) := by
  norm_num [Simple673.qFinal, Simple673.energyC0, rewX, spanB, alphaP]

/-- **The certificate of the 67.35% theorem**: `(rewX, spanB) = (0.008722, 0.004389)` is a
pair-energy certificate of range seven for simple points, for the window of `Simple673`. -/
theorem line_certificate : PairCert1 7 rewX spanB :=
  Line.line_certificate_of_local Simple673.localInequality

/-- The ceiling for range seven applies to the certificate of the 67.35% theorem. -/
theorem line_constant_lt_ceiling :
    (2 - energyCLine - spanB) / (1 - rewX) < 67357 / 100000 :=
  ceiling_line_range7 line_certificate (by norm_num [spanB, alphaP]) (by norm_num [rewX])

end Ceilings
