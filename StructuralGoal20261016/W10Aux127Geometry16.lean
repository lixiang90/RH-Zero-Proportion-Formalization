/- Frozen 127-leaf W10 subtree; complete global coverage is not asserted. -/
import StructuralGoal20261016.W10Aux127Data
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
namespace StructuralGoal20261016.W10Aux127
theorem normalized128 : AdaptiveCoverage.normalize SL cell256 = normal249 := by
  calc
    AdaptiveCoverage.normalize SL cell256 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell256)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell256)).symm
    _ = normal249 := by rfl
theorem left128 : leftChild 9 PR SL normal249 4 6 81920 = cell257 := by
  calc
    leftChild 9 PR SL normal249 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal249) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal249) 4 6 81920).symm
    _ = cell257 := by rfl
theorem right128 : rightChild 9 PR SL normal249 4 6 81920 = cell258 := by
  calc
    rightChild 9 PR SL normal249 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal249) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal249) 4 6 81920).symm
    _ = cell258 := by rfl
theorem normalized129 : AdaptiveCoverage.normalize SL cell254 = normal252 := by
  calc
    AdaptiveCoverage.normalize SL cell254 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell254)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell254)).symm
    _ = normal252 := by rfl
theorem left129 : leftChild 9 PR SL normal252 3 5 81920 = cell259 := by
  calc
    leftChild 9 PR SL normal252 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal252) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal252) 3 5 81920).symm
    _ = cell259 := by rfl
theorem right129 : rightChild 9 PR SL normal252 3 5 81920 = cell260 := by
  calc
    rightChild 9 PR SL normal252 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal252) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal252) 3 5 81920).symm
    _ = cell260 := by rfl

set_option pp.fullNames true
#print axioms normalized128
#print axioms left128
#print axioms right128
#print axioms normalized129
#print axioms left129
#print axioms right129
end StructuralGoal20261016.W10Aux127
end
