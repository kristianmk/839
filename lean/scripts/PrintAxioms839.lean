/-
scripts/PrintAxioms839.lean — axiom audit for the 83.9% distinct-zero theorem and its corollary
for simple zeros.
Run with `lake env lean scripts/PrintAxioms839.lean` after `lake build Solution839`
and `lake build Distinct839.Local.SpotChecks`.
-/
import Solution839
import Distinct839.Local.SpotChecks

-- the main theorem: the three standard axioms and one evaluation by compiled code
#print axioms distinct_zeros_839
-- its corollary for simple zeros: the same
#print axioms simple_zeros_678
-- the seven-point local inequality: the same
#print axioms Distinct839.localInequality
-- everything else: the three standard axioms only
#print axioms Distinct839.distinct_zeros_839_of_local
#print axioms Distinct839.localInequality_of_check
#print axioms Distinct839.kTabArray_sound
#print axioms Distinct839.gramEnergy
#print axioms Distinct839.transfer
#print axioms Distinct839.separatedBound
#print axioms Distinct839.gramData
#print axioms Distinct839.distinct839_of
#print axioms Distinct839.simple_of_distinct
#print axioms Distinct839.Local.spot_lattice
#print axioms Distinct839.Local.spot_double
#print axioms Distinct839.Local.spot_corner
#print axioms Distinct839.Local.spot_vacancy
