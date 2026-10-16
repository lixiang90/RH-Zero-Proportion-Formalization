/- Frozen 478-leaf W10 subtree; complete global coverage is not asserted. -/
import StructuralGoal20261016.W10Aux478Data
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
open StructuralW10Cert20261016.TreeCoverage
open StructuralGoal20261016.LeanCoverBase
open StructuralW10Unconditional20261016
open StructuralW10Cert20261016
namespace StructuralGoal20261016.W10Aux478
theorem normalized480 : AdaptiveCoverage.normalize SL cell960 = normal956 := by
  calc
    AdaptiveCoverage.normalize SL cell960 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell960)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell960)).symm
    _ = normal956 := by rfl
theorem left480 : leftChild 9 PR SL normal956 1 8 239664 = cell961 := by
  calc
    leftChild 9 PR SL normal956 1 8 239664 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal956) 1 8 239664).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal956) 1 8 239664).symm
    _ = cell961 := by rfl
theorem right480 : rightChild 9 PR SL normal956 1 8 239664 = cell962 := by
  calc
    rightChild 9 PR SL normal956 1 8 239664 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal956) 1 8 239664).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal956) 1 8 239664).symm
    _ = cell962 := by rfl

set_option pp.fullNames true
#print axioms normalized480
#print axioms left480
#print axioms right480
end StructuralGoal20261016.W10Aux478
end
