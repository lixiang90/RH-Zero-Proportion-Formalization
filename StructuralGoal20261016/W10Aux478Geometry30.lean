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
theorem normalized240 : AdaptiveCoverage.normalize SL cell479 = normal468 := by
  calc
    AdaptiveCoverage.normalize SL cell479 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell479)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell479)).symm
    _ = normal468 := by rfl
theorem left240 : leftChild 9 PR SL normal468 2 9 262144 = cell481 := by
  calc
    leftChild 9 PR SL normal468 2 9 262144 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal468) 2 9 262144).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal468) 2 9 262144).symm
    _ = cell481 := by rfl
theorem right240 : rightChild 9 PR SL normal468 2 9 262144 = cell482 := by
  calc
    rightChild 9 PR SL normal468 2 9 262144 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal468) 2 9 262144).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal468) 2 9 262144).symm
    _ = cell482 := by rfl
theorem normalized241 : AdaptiveCoverage.normalize SL cell481 = normal469 := by
  calc
    AdaptiveCoverage.normalize SL cell481 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell481)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell481)).symm
    _ = normal469 := by rfl
theorem left241 : leftChild 9 PR SL normal469 2 4 81920 = cell483 := by
  calc
    leftChild 9 PR SL normal469 2 4 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal469) 2 4 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal469) 2 4 81920).symm
    _ = cell483 := by rfl
theorem right241 : rightChild 9 PR SL normal469 2 4 81920 = cell484 := by
  calc
    rightChild 9 PR SL normal469 2 4 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal469) 2 4 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal469) 2 4 81920).symm
    _ = cell484 := by rfl
theorem normalized242 : AdaptiveCoverage.normalize SL cell480 = normal473 := by
  calc
    AdaptiveCoverage.normalize SL cell480 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell480)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell480)).symm
    _ = normal473 := by rfl
theorem left242 : leftChild 9 PR SL normal473 3 7 147456 = cell485 := by
  calc
    leftChild 9 PR SL normal473 3 7 147456 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal473) 3 7 147456).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal473) 3 7 147456).symm
    _ = cell485 := by rfl
theorem right242 : rightChild 9 PR SL normal473 3 7 147456 = cell486 := by
  calc
    rightChild 9 PR SL normal473 3 7 147456 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal473) 3 7 147456).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal473) 3 7 147456).symm
    _ = cell486 := by rfl
theorem normalized243 : AdaptiveCoverage.normalize SL cell485 = normal474 := by
  calc
    AdaptiveCoverage.normalize SL cell485 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell485)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell485)).symm
    _ = normal474 := by rfl
theorem left243 : leftChild 9 PR SL normal474 2 4 81920 = cell487 := by
  calc
    leftChild 9 PR SL normal474 2 4 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal474) 2 4 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal474) 2 4 81920).symm
    _ = cell487 := by rfl
theorem right243 : rightChild 9 PR SL normal474 2 4 81920 = cell488 := by
  calc
    rightChild 9 PR SL normal474 2 4 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal474) 2 4 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal474) 2 4 81920).symm
    _ = cell488 := by rfl
theorem normalized244 : AdaptiveCoverage.normalize SL cell470 = normal478 := by
  calc
    AdaptiveCoverage.normalize SL cell470 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell470)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell470)).symm
    _ = normal478 := by rfl
theorem left244 : leftChild 9 PR SL normal478 2 5 114688 = cell489 := by
  calc
    leftChild 9 PR SL normal478 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal478) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal478) 2 5 114688).symm
    _ = cell489 := by rfl
theorem right244 : rightChild 9 PR SL normal478 2 5 114688 = cell490 := by
  calc
    rightChild 9 PR SL normal478 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal478) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal478) 2 5 114688).symm
    _ = cell490 := by rfl
theorem normalized245 : AdaptiveCoverage.normalize SL cell460 = normal481 := by
  calc
    AdaptiveCoverage.normalize SL cell460 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell460)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell460)).symm
    _ = normal481 := by rfl
theorem left245 : leftChild 9 PR SL normal481 0 9 335872 = cell491 := by
  calc
    leftChild 9 PR SL normal481 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal481) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal481) 0 9 335872).symm
    _ = cell491 := by rfl
theorem right245 : rightChild 9 PR SL normal481 0 9 335872 = cell492 := by
  calc
    rightChild 9 PR SL normal481 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal481) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal481) 0 9 335872).symm
    _ = cell492 := by rfl
theorem normalized246 : AdaptiveCoverage.normalize SL cell491 = normal482 := by
  calc
    AdaptiveCoverage.normalize SL cell491 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell491)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell491)).symm
    _ = normal482 := by rfl
theorem left246 : leftChild 9 PR SL normal482 2 6 147456 = cell493 := by
  calc
    leftChild 9 PR SL normal482 2 6 147456 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal482) 2 6 147456).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal482) 2 6 147456).symm
    _ = cell493 := by rfl
theorem right246 : rightChild 9 PR SL normal482 2 6 147456 = cell494 := by
  calc
    rightChild 9 PR SL normal482 2 6 147456 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal482) 2 6 147456).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal482) 2 6 147456).symm
    _ = cell494 := by rfl
theorem normalized247 : AdaptiveCoverage.normalize SL cell494 = normal484 := by
  calc
    AdaptiveCoverage.normalize SL cell494 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell494)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell494)).symm
    _ = normal484 := by rfl
theorem left247 : leftChild 9 PR SL normal484 2 5 114688 = cell495 := by
  calc
    leftChild 9 PR SL normal484 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal484) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal484) 2 5 114688).symm
    _ = cell495 := by rfl
theorem right247 : rightChild 9 PR SL normal484 2 5 114688 = cell496 := by
  calc
    rightChild 9 PR SL normal484 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal484) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal484) 2 5 114688).symm
    _ = cell496 := by rfl

set_option pp.fullNames true
#print axioms normalized240
#print axioms left240
#print axioms right240
#print axioms normalized241
#print axioms left241
#print axioms right241
#print axioms normalized242
#print axioms left242
#print axioms right242
#print axioms normalized243
#print axioms left243
#print axioms right243
#print axioms normalized244
#print axioms left244
#print axioms right244
#print axioms normalized245
#print axioms left245
#print axioms right245
#print axioms normalized246
#print axioms left246
#print axioms right246
#print axioms normalized247
#print axioms left247
#print axioms right247
end StructuralGoal20261016.W10Aux478
end
