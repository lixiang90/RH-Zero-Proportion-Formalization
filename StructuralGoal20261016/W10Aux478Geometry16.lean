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
theorem normalized128 : AdaptiveCoverage.normalize SL cell255 = normal246 := by
  calc
    AdaptiveCoverage.normalize SL cell255 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell255)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell255)).symm
    _ = normal246 := by rfl
theorem left128 : leftChild 9 PR SL normal246 3 7 147456 = cell257 := by
  calc
    leftChild 9 PR SL normal246 3 7 147456 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal246) 3 7 147456).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal246) 3 7 147456).symm
    _ = cell257 := by rfl
theorem right128 : rightChild 9 PR SL normal246 3 7 147456 = cell258 := by
  calc
    rightChild 9 PR SL normal246 3 7 147456 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal246) 3 7 147456).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal246) 3 7 147456).symm
    _ = cell258 := by rfl
theorem normalized129 : AdaptiveCoverage.normalize SL cell258 = normal248 := by
  calc
    AdaptiveCoverage.normalize SL cell258 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell258)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell258)).symm
    _ = normal248 := by rfl
theorem left129 : leftChild 9 PR SL normal248 2 5 114688 = cell259 := by
  calc
    leftChild 9 PR SL normal248 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal248) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal248) 2 5 114688).symm
    _ = cell259 := by rfl
theorem right129 : rightChild 9 PR SL normal248 2 5 114688 = cell260 := by
  calc
    rightChild 9 PR SL normal248 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal248) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal248) 2 5 114688).symm
    _ = cell260 := by rfl
theorem normalized130 : AdaptiveCoverage.normalize SL cell180 = normal252 := by
  calc
    AdaptiveCoverage.normalize SL cell180 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell180)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell180)).symm
    _ = normal252 := by rfl
theorem left130 : leftChild 9 PR SL normal252 3 8 196608 = cell261 := by
  calc
    leftChild 9 PR SL normal252 3 8 196608 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal252) 3 8 196608).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal252) 3 8 196608).symm
    _ = cell261 := by rfl
theorem right130 : rightChild 9 PR SL normal252 3 8 196608 = cell262 := by
  calc
    rightChild 9 PR SL normal252 3 8 196608 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal252) 3 8 196608).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal252) 3 8 196608).symm
    _ = cell262 := by rfl
theorem normalized131 : AdaptiveCoverage.normalize SL cell261 = normal253 := by
  calc
    AdaptiveCoverage.normalize SL cell261 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell261)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell261)).symm
    _ = normal253 := by rfl
theorem left131 : leftChild 9 PR SL normal253 2 6 131072 = cell263 := by
  calc
    leftChild 9 PR SL normal253 2 6 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal253) 2 6 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal253) 2 6 131072).symm
    _ = cell263 := by rfl
theorem right131 : rightChild 9 PR SL normal253 2 6 131072 = cell264 := by
  calc
    rightChild 9 PR SL normal253 2 6 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal253) 2 6 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal253) 2 6 131072).symm
    _ = cell264 := by rfl
theorem normalized132 : AdaptiveCoverage.normalize SL cell264 = normal255 := by
  calc
    AdaptiveCoverage.normalize SL cell264 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell264)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell264)).symm
    _ = normal255 := by rfl
theorem left132 : leftChild 9 PR SL normal255 3 5 81920 = cell265 := by
  calc
    leftChild 9 PR SL normal255 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal255) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal255) 3 5 81920).symm
    _ = cell265 := by rfl
theorem right132 : rightChild 9 PR SL normal255 3 5 81920 = cell266 := by
  calc
    rightChild 9 PR SL normal255 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal255) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal255) 3 5 81920).symm
    _ = cell266 := by rfl
theorem normalized133 : AdaptiveCoverage.normalize SL cell265 = normal256 := by
  calc
    AdaptiveCoverage.normalize SL cell265 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell265)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell265)).symm
    _ = normal256 := by rfl
theorem left133 : leftChild 9 PR SL normal256 4 6 81920 = cell267 := by
  calc
    leftChild 9 PR SL normal256 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal256) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal256) 4 6 81920).symm
    _ = cell267 := by rfl
theorem right133 : rightChild 9 PR SL normal256 4 6 81920 = cell268 := by
  calc
    rightChild 9 PR SL normal256 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal256) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal256) 4 6 81920).symm
    _ = cell268 := by rfl
theorem normalized134 : AdaptiveCoverage.normalize SL cell267 = normal257 := by
  calc
    AdaptiveCoverage.normalize SL cell267 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell267)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell267)).symm
    _ = normal257 := by rfl
theorem left134 : leftChild 9 PR SL normal257 0 8 294912 = cell269 := by
  calc
    leftChild 9 PR SL normal257 0 8 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal257) 0 8 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal257) 0 8 294912).symm
    _ = cell269 := by rfl
theorem right134 : rightChild 9 PR SL normal257 0 8 294912 = cell270 := by
  calc
    rightChild 9 PR SL normal257 0 8 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal257) 0 8 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal257) 0 8 294912).symm
    _ = cell270 := by rfl
theorem normalized135 : AdaptiveCoverage.normalize SL cell269 = normal258 := by
  calc
    AdaptiveCoverage.normalize SL cell269 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell269)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell269)).symm
    _ = normal258 := by rfl
theorem left135 : leftChild 9 PR SL normal258 0 9 335872 = cell271 := by
  calc
    leftChild 9 PR SL normal258 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal258) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal258) 0 9 335872).symm
    _ = cell271 := by rfl
theorem right135 : rightChild 9 PR SL normal258 0 9 335872 = cell272 := by
  calc
    rightChild 9 PR SL normal258 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal258) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal258) 0 9 335872).symm
    _ = cell272 := by rfl

set_option pp.fullNames true
#print axioms normalized128
#print axioms left128
#print axioms right128
#print axioms normalized129
#print axioms left129
#print axioms right129
#print axioms normalized130
#print axioms left130
#print axioms right130
#print axioms normalized131
#print axioms left131
#print axioms right131
#print axioms normalized132
#print axioms left132
#print axioms right132
#print axioms normalized133
#print axioms left133
#print axioms right133
#print axioms normalized134
#print axioms left134
#print axioms right134
#print axioms normalized135
#print axioms left135
#print axioms right135
end StructuralGoal20261016.W10Aux478
end
