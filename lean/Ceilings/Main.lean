/-
Ceilings/Main.lean — upper limits for what pair-energy certificates can give: summary.

The proofs of the bounds for distinct zeros (`Distinct839`, 83.90%) and for simple zeros on the
critical line (`Simple673`, 67.35%) bound a pair energy from below by a linear function of the
numbers of points and of the length of the configuration (a *pair-energy certificate*,
`Ceilings/Defs.lean`). The theorems below say that no inequality of that kind can give more than
a stated constant. Each is proved from explicit periodic trial configurations with rational gaps
(`Ceilings/Periodic.lean`, `Ceilings/Mixture.lean`, `Ceilings/State.lean`), whose energies are
bounded by rational upper bounds for `K²` evaluated by the kernel (`Ceilings/Trig.lean`,
`Ceilings/KernelBound.lean`). All of them depend on the three standard axioms only.

First window (`Distinct839.K`, energy constant `energyC = Distinct839.kappa 1`), for a
certificate `(x₁, x₂, b)` with `b ≥ 0` and `2 - 2x₁ + x₂ > 0`, constant
`(3 - energyC + x₂ - x₁ - b)/(2 - 2x₁ + x₂)`:

* `ceiling_range6`  : `PairCert 6 x₁ x₂ b → … < 83916/100000`   (`Distinct/Range6.lean`)
* `ceiling_range8`  : `PairCert 8 x₁ x₂ b → … < 83943/100000`   (`Distinct/Range8.lean`)
* `ceiling_range10` : `PairCert 10 x₁ x₂ b → … < 83957/100000`  (`Distinct/Range10.lean`)
* `ceiling_all`     : `PairCertAll x₁ x₂ b → … < 83998/100000`  (`Distinct/All.lean`)
* `ceiling_gram`    : `GramCert x₁ x₂ b → … < 83998/100000`     (`Distinct/GramBridge.lean`),
  with `GramCert.toPairCertAll`: certificates in the sense of the finite Gram theorem are
  pair-energy certificates.

Second window (`Simple673.K`, energy constant `energyCLine = Simple673.kappa 1`), for a
certificate `(x, b)` for simple points with `x < 1`, constant `(2 - energyCLine - b)/(1 - x)`:

* `ceiling_line_range7` : `PairCert1 7 x b → … < 67357/100000`  (`Line/Range7.lean`)
* `ceiling_line_all`    : `PairCert1All x b → … < 67383/100000` (`Line/All.lean`)

The energy constants are `A + B` with `A = ∫ f²` and `B = 2 ∫₀¹ r (f⋆f)(r) dr`. That `B` is the
double integral `∬ |s - t| f(s) f(t) ds dt`, so that `A + B` is the energy constant in its usual
form, is `two_mul_integral_mul_vConv_eq` (`Ceilings/EnergyIntegral.lean`), for every continuous
function.

The certificates of the two theorems are certificates of range six and of range seven in this
sense: `paper_certificate : PairCert 6 rewX rewY spanB` (`Distinct/PaperCert.lean`) and
`line_certificate : PairCert1 7 rewX spanB` (`Line/PaperCert.lean`). These two files are not
imported here: they depend on the local inequalities for seven and for eight points, whose proofs
evaluate a checker by compiled code. The versions with the local inequality as a hypothesis
(`Distinct.paper_certificate_of_local`, in `Distinct/Paper.lean`) use the standard axioms only.
-/
import Ceilings.Distinct.Range6
import Ceilings.Distinct.Range8
import Ceilings.Distinct.Range10
import Ceilings.Distinct.All
import Ceilings.Distinct.Paper
import Ceilings.Distinct.GramBridge
import Ceilings.Line.Range7
import Ceilings.Line.All
import Ceilings.EnergyIntegral
