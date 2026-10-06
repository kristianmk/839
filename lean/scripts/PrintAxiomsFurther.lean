/-
scripts/PrintAxiomsFurther.lean — axiom audit for the two further theorems (Theorem 1.4 of the paper).
Run with `lake env lean scripts/PrintAxiomsFurther.lean` after `lake build SolutionFurther`.
-/
import SolutionFurther

-- the two theorems: the three standard axioms and one evaluation by compiled code each
#print axioms average_simple_and_critical_8367
#print axioms simple_or_critical_8891
-- the same theorems in the namespace of the development
#print axioms Further.average_simple_and_critical_8367
#print axioms Further.simple_or_critical_8891
-- everything else: the three standard axioms only
#print axioms Further.average_simple_and_critical_8367_of_local
#print axioms Further.simple_or_critical_8891_of_local
#print axioms Further.average_of_layers
#print axioms Further.simple_or_line_of_layers
#print axioms Further.threshold2_eig_phiC
#print axioms Further.seam_block2
#print axioms Further.count_certificate
#print axioms Further.Line.count_avg
#print axioms Further.Line.seam_avg
#print axioms Further.Line.avg_bound_family
#print axioms Further.Dist.seam_count_sl
#print axioms Further.Dist.seam_sl
#print axioms Further.Dist.sl_bound_family
#print axioms N0mult_eq_library
#print axioms Nsimple_eq_library
#print axioms NsimpleOrLine_eq_library
