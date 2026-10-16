/- SPDX-License-Identifier: Apache-2.0
An exact two-entry formula for collecting a 9 by 9 matrix into the 45
unordered actual moment coordinates. This avoids numerical 81-entry sums.
-/
import StructuralGoal20261016.WindowMomentPolynomial
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowMomentCollectHDirect
open WindowMomentPolynomial WindowMomentLayout

theorem direct (M : Fin 9 → Fin 9 → ℚ) (e : Fin 45) :
 collectH M e = M (hFirst e) (hSecond e)+
   (if hFirst e = hSecond e then 0 else M (hSecond e) (hFirst e)) := by
 fin_cases e <;> simp [collectH,Fintype.sum_prod_type,Fin.sum_univ_succ,
   hLookup,hFirst,hSecond,Fin.succ]

set_option pp.fullNames true
#print axioms direct
end StructuralGoal20261016.WindowMomentCollectHDirect
end
