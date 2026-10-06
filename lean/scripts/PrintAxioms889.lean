/-
scripts/PrintAxioms889.lean — axiom audit for the theorem "more than 88.93% of the zeros of the
Riemann zeta function are simple or on the critical line" (third window).
Run with `lake env lean scripts/PrintAxioms889.lean` after `lake build Solution889`
(and `lake build Line889.Local.SpotChecks` for the last four lines; remove them otherwise).
-/
import Solution889
import Line889.Local.SpotChecks

-- the theorem: the three standard axioms and one evaluation by compiled code
#print axioms simple_or_critical_8893
-- the same theorem in the namespace of the development, and the seven-point inequality
#print axioms Line889.simple_or_critical_8893
#print axioms Line889.localInequality
-- everything else: the three standard axioms only
#print axioms Line889.simple_or_critical_8893_of_local
#print axioms Line889.simple_or_critical_8893_of_layers
#print axioms Line889.localInequality_of_check
#print axioms Line889.kTab_sound
#print axioms Line889.kTabArray_sound
#print axioms Line889.windowStatement
#print axioms Line889.windowSide
#print axioms Line889.windowMoments
#print axioms Line889.kappaStatement
#print axioms Line889.kIntegral
#print axioms Line889.betaBound
#print axioms Line889.majorantPointwise
#print axioms Line889.lMajBound
#print axioms Line889.separatedBound
#print axioms Line889.gramDataLayer
#print axioms Line889.transfer
#print axioms Line889.gramEnergy
#print axioms Line889.assembly
#print axioms Line889.Transfer.transfer_range6
#print axioms Line889.Gram.gramEnergy_explicit
#print axioms Line889.Assembly.seam_count_sl
#print axioms Line889.Assembly.seam_block_sl
#print axioms Line889.Assembly.seam_sl
#print axioms Line889.Assembly.sl_bound_family
#print axioms Further.seam_block2
#print axioms Further.count_certificate
#print axioms NsimpleOrLine_eq_library
-- four small boxes checked by the kernel itself (not used by the proof): standard axioms only
#print axioms Line889.Local.spot_corner
#print axioms Line889.Local.spot_lattice
#print axioms Line889.Local.spot_tightest
#print axioms Line889.Local.spot_second
