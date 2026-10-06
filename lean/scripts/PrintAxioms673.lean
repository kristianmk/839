/-
scripts/PrintAxioms673.lean — axiom audit for the theorem on zeros that are simple and on the
critical line.
Run with `lake env lean scripts/PrintAxioms673.lean` after `lake build Solution673`
(and `lake build Simple673.Local.SpotChecks` for the last four lines; remove them otherwise).
-/
import Solution673
import Simple673.Local.SpotChecks

-- the theorem: the three standard axioms and one evaluation by compiled code
#print axioms simple_critical_zeros_673
-- the eight-point local inequality for the second window: the same
#print axioms Simple673.localInequality
-- everything else: the three standard axioms only
#print axioms Simple673.simple_critical_zeros_673_of_local
#print axioms Simple673.localInequality_of_check
#print axioms Simple673.localInequality_of_checkPar
#print axioms Simple673.kTabArray_sound
#print axioms Simple673.betaBound
#print axioms Simple673.gramEnergy
#print axioms Simple673.transfer
#print axioms Simple673.Transfer.transfer_range7
#print axioms Simple673.majorantPointwise
#print axioms Simple673.separatedBound
#print axioms Simple673.windowStatement
#print axioms Simple673.windowSide
#print axioms Simple673.windowMoments
#print axioms Simple673.kappaStatement
#print axioms Simple673.gramDataLayer
#print axioms Simple673.assembly
-- four boxes checked by the kernel (not used by the proof): the standard axioms only
#print axioms Simple673.Local.spot_trial
#print axioms Simple673.Local.spot_second_trial
#print axioms Simple673.Local.spot_corner
#print axioms Simple673.Local.spot_tightest
