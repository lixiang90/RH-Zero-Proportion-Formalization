/- Diagnostic only: no theorem or exclusion is asserted. -/
import StructuralGoal20261016.WindowMomentAggregateData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open StructuralGoal20261016
open WindowMomentAggregateData WindowMomentPolynomial WindowMomentLayout
#check row0
#reduce (row0.coeff (hIndex 0))
#check groups0
#reduce ((groups0 0).q 0 0)
#check aggregate0
#reduce (aggregate0.q 0 0)
#check flatten
#reduce (flatten aggregate0 (qIndex 0 0))
#check WindowMomentPolynomial.collectH
#reduce (WindowMomentPolynomial.collectH (fun _ _ => (1:ℚ)) 0)
