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
theorem normalized248 : AdaptiveCoverage.normalize SL cell496 = normal486 := by
  calc
    AdaptiveCoverage.normalize SL cell496 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell496)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell496)).symm
    _ = normal486 := by rfl
theorem left248 : leftChild 9 PR SL normal486 4 7 114688 = cell497 := by
  calc
    leftChild 9 PR SL normal486 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal486) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal486) 4 7 114688).symm
    _ = cell497 := by rfl
theorem right248 : rightChild 9 PR SL normal486 4 7 114688 = cell498 := by
  calc
    rightChild 9 PR SL normal486 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal486) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal486) 4 7 114688).symm
    _ = cell498 := by rfl
theorem normalized249 : AdaptiveCoverage.normalize SL cell412 = normal490 := by
  calc
    AdaptiveCoverage.normalize SL cell412 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell412)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell412)).symm
    _ = normal490 := by rfl
theorem left249 : leftChild 9 PR SL normal490 3 7 131072 = cell499 := by
  calc
    leftChild 9 PR SL normal490 3 7 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal490) 3 7 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal490) 3 7 131072).symm
    _ = cell499 := by rfl
theorem right249 : rightChild 9 PR SL normal490 3 7 131072 = cell500 := by
  calc
    rightChild 9 PR SL normal490 3 7 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal490) 3 7 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal490) 3 7 131072).symm
    _ = cell500 := by rfl
theorem normalized250 : AdaptiveCoverage.normalize SL cell500 = normal492 := by
  calc
    AdaptiveCoverage.normalize SL cell500 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell500)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell500)).symm
    _ = normal492 := by rfl
theorem left250 : leftChild 9 PR SL normal492 0 8 294912 = cell501 := by
  calc
    leftChild 9 PR SL normal492 0 8 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal492) 0 8 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal492) 0 8 294912).symm
    _ = cell501 := by rfl
theorem right250 : rightChild 9 PR SL normal492 0 8 294912 = cell502 := by
  calc
    rightChild 9 PR SL normal492 0 8 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal492) 0 8 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal492) 0 8 294912).symm
    _ = cell502 := by rfl
theorem normalized251 : AdaptiveCoverage.normalize SL cell501 = normal493 := by
  calc
    AdaptiveCoverage.normalize SL cell501 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell501)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell501)).symm
    _ = normal493 := by rfl
theorem left251 : leftChild 9 PR SL normal493 3 5 81920 = cell503 := by
  calc
    leftChild 9 PR SL normal493 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal493) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal493) 3 5 81920).symm
    _ = cell503 := by rfl
theorem right251 : rightChild 9 PR SL normal493 3 5 81920 = cell504 := by
  calc
    rightChild 9 PR SL normal493 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal493) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal493) 3 5 81920).symm
    _ = cell504 := by rfl
theorem normalized252 : AdaptiveCoverage.normalize SL cell503 = normal494 := by
  calc
    AdaptiveCoverage.normalize SL cell503 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell503)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell503)).symm
    _ = normal494 := by rfl
theorem left252 : leftChild 9 PR SL normal494 4 6 81920 = cell505 := by
  calc
    leftChild 9 PR SL normal494 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal494) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal494) 4 6 81920).symm
    _ = cell505 := by rfl
theorem right252 : rightChild 9 PR SL normal494 4 6 81920 = cell506 := by
  calc
    rightChild 9 PR SL normal494 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal494) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal494) 4 6 81920).symm
    _ = cell506 := by rfl
theorem normalized253 : AdaptiveCoverage.normalize SL cell505 = normal495 := by
  calc
    AdaptiveCoverage.normalize SL cell505 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell505)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell505)).symm
    _ = normal495 := by rfl
theorem left253 : leftChild 9 PR SL normal495 0 9 335872 = cell507 := by
  calc
    leftChild 9 PR SL normal495 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal495) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal495) 0 9 335872).symm
    _ = cell507 := by rfl
theorem right253 : rightChild 9 PR SL normal495 0 9 335872 = cell508 := by
  calc
    rightChild 9 PR SL normal495 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal495) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal495) 0 9 335872).symm
    _ = cell508 := by rfl
theorem normalized254 : AdaptiveCoverage.normalize SL cell507 = normal496 := by
  calc
    AdaptiveCoverage.normalize SL cell507 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell507)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell507)).symm
    _ = normal496 := by rfl
theorem left254 : leftChild 9 PR SL normal496 2 5 114688 = cell509 := by
  calc
    leftChild 9 PR SL normal496 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal496) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal496) 2 5 114688).symm
    _ = cell509 := by rfl
theorem right254 : rightChild 9 PR SL normal496 2 5 114688 = cell510 := by
  calc
    rightChild 9 PR SL normal496 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal496) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal496) 2 5 114688).symm
    _ = cell510 := by rfl
theorem normalized255 : AdaptiveCoverage.normalize SL cell502 = normal502 := by
  calc
    AdaptiveCoverage.normalize SL cell502 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell502)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell502)).symm
    _ = normal502 := by rfl
theorem left255 : leftChild 9 PR SL normal502 1 9 294912 = cell511 := by
  calc
    leftChild 9 PR SL normal502 1 9 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal502) 1 9 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal502) 1 9 294912).symm
    _ = cell511 := by rfl
theorem right255 : rightChild 9 PR SL normal502 1 9 294912 = cell512 := by
  calc
    rightChild 9 PR SL normal502 1 9 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal502) 1 9 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal502) 1 9 294912).symm
    _ = cell512 := by rfl

set_option pp.fullNames true
#print axioms normalized248
#print axioms left248
#print axioms right248
#print axioms normalized249
#print axioms left249
#print axioms right249
#print axioms normalized250
#print axioms left250
#print axioms right250
#print axioms normalized251
#print axioms left251
#print axioms right251
#print axioms normalized252
#print axioms left252
#print axioms right252
#print axioms normalized253
#print axioms left253
#print axioms right253
#print axioms normalized254
#print axioms left254
#print axioms right254
#print axioms normalized255
#print axioms left255
#print axioms right255
end StructuralGoal20261016.W10Aux478
end
