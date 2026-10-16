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
theorem normalized216 : AdaptiveCoverage.normalize SL cell416 = normal423 := by
  calc
    AdaptiveCoverage.normalize SL cell416 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell416)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell416)).symm
    _ = normal423 := by rfl
theorem left216 : leftChild 9 PR SL normal423 1 9 294912 = cell433 := by
  calc
    leftChild 9 PR SL normal423 1 9 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal423) 1 9 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal423) 1 9 294912).symm
    _ = cell433 := by rfl
theorem right216 : rightChild 9 PR SL normal423 1 9 294912 = cell434 := by
  calc
    rightChild 9 PR SL normal423 1 9 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal423) 1 9 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal423) 1 9 294912).symm
    _ = cell434 := by rfl
theorem normalized217 : AdaptiveCoverage.normalize SL cell433 = normal424 := by
  calc
    AdaptiveCoverage.normalize SL cell433 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell433)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell433)).symm
    _ = normal424 := by rfl
theorem left217 : leftChild 9 PR SL normal424 3 5 81920 = cell435 := by
  calc
    leftChild 9 PR SL normal424 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal424) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal424) 3 5 81920).symm
    _ = cell435 := by rfl
theorem right217 : rightChild 9 PR SL normal424 3 5 81920 = cell436 := by
  calc
    rightChild 9 PR SL normal424 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal424) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal424) 3 5 81920).symm
    _ = cell436 := by rfl
theorem normalized218 : AdaptiveCoverage.normalize SL cell435 = normal425 := by
  calc
    AdaptiveCoverage.normalize SL cell435 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell435)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell435)).symm
    _ = normal425 := by rfl
theorem left218 : leftChild 9 PR SL normal425 4 6 81920 = cell437 := by
  calc
    leftChild 9 PR SL normal425 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal425) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal425) 4 6 81920).symm
    _ = cell437 := by rfl
theorem right218 : rightChild 9 PR SL normal425 4 6 81920 = cell438 := by
  calc
    rightChild 9 PR SL normal425 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal425) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal425) 4 6 81920).symm
    _ = cell438 := by rfl
theorem normalized219 : AdaptiveCoverage.normalize SL cell437 = normal426 := by
  calc
    AdaptiveCoverage.normalize SL cell437 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell437)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell437)).symm
    _ = normal426 := by rfl
theorem left219 : leftChild 9 PR SL normal426 0 6 229376 = cell439 := by
  calc
    leftChild 9 PR SL normal426 0 6 229376 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal426) 0 6 229376).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal426) 0 6 229376).symm
    _ = cell439 := by rfl
theorem right219 : rightChild 9 PR SL normal426 0 6 229376 = cell440 := by
  calc
    rightChild 9 PR SL normal426 0 6 229376 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal426) 0 6 229376).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal426) 0 6 229376).symm
    _ = cell440 := by rfl
theorem normalized220 : AdaptiveCoverage.normalize SL cell439 = normal427 := by
  calc
    AdaptiveCoverage.normalize SL cell439 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell439)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell439)).symm
    _ = normal427 := by rfl
theorem left220 : leftChild 9 PR SL normal427 0 9 335872 = cell441 := by
  calc
    leftChild 9 PR SL normal427 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal427) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal427) 0 9 335872).symm
    _ = cell441 := by rfl
theorem right220 : rightChild 9 PR SL normal427 0 9 335872 = cell442 := by
  calc
    rightChild 9 PR SL normal427 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal427) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal427) 0 9 335872).symm
    _ = cell442 := by rfl
theorem normalized221 : AdaptiveCoverage.normalize SL cell441 = normal428 := by
  calc
    AdaptiveCoverage.normalize SL cell441 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell441)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell441)).symm
    _ = normal428 := by rfl
theorem left221 : leftChild 9 PR SL normal428 2 5 114688 = cell443 := by
  calc
    leftChild 9 PR SL normal428 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal428) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal428) 2 5 114688).symm
    _ = cell443 := by rfl
theorem right221 : rightChild 9 PR SL normal428 2 5 114688 = cell444 := by
  calc
    rightChild 9 PR SL normal428 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal428) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal428) 2 5 114688).symm
    _ = cell444 := by rfl
theorem normalized222 : AdaptiveCoverage.normalize SL cell444 = normal430 := by
  calc
    AdaptiveCoverage.normalize SL cell444 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell444)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell444)).symm
    _ = normal430 := by rfl
theorem left222 : leftChild 9 PR SL normal430 4 7 98304 = cell445 := by
  calc
    leftChild 9 PR SL normal430 4 7 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal430) 4 7 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal430) 4 7 98304).symm
    _ = cell445 := by rfl
theorem right222 : rightChild 9 PR SL normal430 4 7 98304 = cell446 := by
  calc
    rightChild 9 PR SL normal430 4 7 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal430) 4 7 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal430) 4 7 98304).symm
    _ = cell446 := by rfl
theorem normalized223 : AdaptiveCoverage.normalize SL cell446 = normal432 := by
  calc
    AdaptiveCoverage.normalize SL cell446 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell446)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell446)).symm
    _ = normal432 := by rfl
theorem left223 : leftChild 9 PR SL normal432 2 4 81920 = cell447 := by
  calc
    leftChild 9 PR SL normal432 2 4 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal432) 2 4 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal432) 2 4 81920).symm
    _ = cell447 := by rfl
theorem right223 : rightChild 9 PR SL normal432 2 4 81920 = cell448 := by
  calc
    rightChild 9 PR SL normal432 2 4 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal432) 2 4 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal432) 2 4 81920).symm
    _ = cell448 := by rfl

set_option pp.fullNames true
#print axioms normalized216
#print axioms left216
#print axioms right216
#print axioms normalized217
#print axioms left217
#print axioms right217
#print axioms normalized218
#print axioms left218
#print axioms right218
#print axioms normalized219
#print axioms left219
#print axioms right219
#print axioms normalized220
#print axioms left220
#print axioms right220
#print axioms normalized221
#print axioms left221
#print axioms right221
#print axioms normalized222
#print axioms left222
#print axioms right222
#print axioms normalized223
#print axioms left223
#print axioms right223
end StructuralGoal20261016.W10Aux478
end
