/-
scripts/PrintAxiomsCeilings.lean — axiom audit for the ceilings.
Run with `lake env lean scripts/PrintAxiomsCeilings.lean` after `lake build Ceilings SolutionCeilings`.
-/
import Ceilings
import SolutionCeilings

-- the six ceilings as stated in ChallengeCeilings.lean: the three standard axioms only
#print axioms ceiling_range6
#print axioms ceiling_range8
#print axioms ceiling_range10
#print axioms ceiling_all
#print axioms ceiling_line_range7
#print axioms ceiling_line_all
-- the same in the development
#print axioms Ceilings.ceiling_range6
#print axioms Ceilings.ceiling_range8
#print axioms Ceilings.ceiling_range10
#print axioms Ceilings.ceiling_all
#print axioms Ceilings.ceiling_line_range7
#print axioms Ceilings.ceiling_line_all
-- the constants in the conclusions are the energy constants of the two proofs
#print axioms Ceilings.energyC_eq_kappa_one
#print axioms Ceilings.energyCLine_eq_kappa_one
-- the energy constants of ChallengeCeilings.lean are defined as `∫ f² + ∬ |s - t| f(s) f(t) ds dt`:
-- the change of variables, the identification with the constant of the method, the closed forms
#print axioms Ceilings.two_mul_integral_mul_vConv_eq
#print axioms energyFirst_eq_kappa
#print axioms energySecond_eq_kappa
#print axioms energyFirst_closed
#print axioms energySecond_closed
-- certificates in the Gram form are pair-energy certificates
#print axioms Ceilings.GramCert.toPairCertAll
#print axioms Ceilings.ceiling_gram
-- the certificates of the paper are pair-energy certificates of range six (first window) and of
-- range seven (second window); these two statements inherit the axiom of the respective search
#print axioms Ceilings.paper_certificate
#print axioms Ceilings.line_certificate
