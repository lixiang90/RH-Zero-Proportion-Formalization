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
theorem normalized224 : AdaptiveCoverage.normalize SL cell440 = normal436 := by
  calc
    AdaptiveCoverage.normalize SL cell440 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell440)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell440)).symm
    _ = normal436 := by rfl
theorem left224 : leftChild 9 PR SL normal436 0 9 335872 = cell449 := by
  calc
    leftChild 9 PR SL normal436 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal436) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal436) 0 9 335872).symm
    _ = cell449 := by rfl
theorem right224 : rightChild 9 PR SL normal436 0 9 335872 = cell450 := by
  calc
    rightChild 9 PR SL normal436 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal436) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal436) 0 9 335872).symm
    _ = cell450 := by rfl
theorem normalized225 : AdaptiveCoverage.normalize SL cell449 = normal437 := by
  calc
    AdaptiveCoverage.normalize SL cell449 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell449)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell449)).symm
    _ = normal437 := by rfl
theorem left225 : leftChild 9 PR SL normal437 2 5 114688 = cell451 := by
  calc
    leftChild 9 PR SL normal437 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal437) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal437) 2 5 114688).symm
    _ = cell451 := by rfl
theorem right225 : rightChild 9 PR SL normal437 2 5 114688 = cell452 := by
  calc
    rightChild 9 PR SL normal437 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal437) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal437) 2 5 114688).symm
    _ = cell452 := by rfl
theorem normalized226 : AdaptiveCoverage.normalize SL cell452 = normal439 := by
  calc
    AdaptiveCoverage.normalize SL cell452 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell452)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell452)).symm
    _ = normal439 := by rfl
theorem left226 : leftChild 9 PR SL normal439 3 6 98304 = cell453 := by
  calc
    leftChild 9 PR SL normal439 3 6 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal439) 3 6 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal439) 3 6 98304).symm
    _ = cell453 := by rfl
theorem right226 : rightChild 9 PR SL normal439 3 6 98304 = cell454 := by
  calc
    rightChild 9 PR SL normal439 3 6 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal439) 3 6 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal439) 3 6 98304).symm
    _ = cell454 := by rfl
theorem normalized227 : AdaptiveCoverage.normalize SL cell454 = normal441 := by
  calc
    AdaptiveCoverage.normalize SL cell454 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell454)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell454)).symm
    _ = normal441 := by rfl
theorem left227 : leftChild 9 PR SL normal441 4 7 98304 = cell455 := by
  calc
    leftChild 9 PR SL normal441 4 7 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal441) 4 7 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal441) 4 7 98304).symm
    _ = cell455 := by rfl
theorem right227 : rightChild 9 PR SL normal441 4 7 98304 = cell456 := by
  calc
    rightChild 9 PR SL normal441 4 7 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal441) 4 7 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal441) 4 7 98304).symm
    _ = cell456 := by rfl
theorem normalized228 : AdaptiveCoverage.normalize SL cell456 = normal443 := by
  calc
    AdaptiveCoverage.normalize SL cell456 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell456)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell456)).symm
    _ = normal443 := by rfl
theorem left228 : leftChild 9 PR SL normal443 2 4 81920 = cell457 := by
  calc
    leftChild 9 PR SL normal443 2 4 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal443) 2 4 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal443) 2 4 81920).symm
    _ = cell457 := by rfl
theorem right228 : rightChild 9 PR SL normal443 2 4 81920 = cell458 := by
  calc
    rightChild 9 PR SL normal443 2 4 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal443) 2 4 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal443) 2 4 81920).symm
    _ = cell458 := by rfl
theorem normalized229 : AdaptiveCoverage.normalize SL cell434 = normal449 := by
  calc
    AdaptiveCoverage.normalize SL cell434 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell434)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell434)).symm
    _ = normal449 := by rfl
theorem left229 : leftChild 9 PR SL normal449 2 7 196608 = cell459 := by
  calc
    leftChild 9 PR SL normal449 2 7 196608 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal449) 2 7 196608).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal449) 2 7 196608).symm
    _ = cell459 := by rfl
theorem right229 : rightChild 9 PR SL normal449 2 7 196608 = cell460 := by
  calc
    rightChild 9 PR SL normal449 2 7 196608 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal449) 2 7 196608).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal449) 2 7 196608).symm
    _ = cell460 := by rfl
theorem normalized230 : AdaptiveCoverage.normalize SL cell459 = normal450 := by
  calc
    AdaptiveCoverage.normalize SL cell459 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell459)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell459)).symm
    _ = normal450 := by rfl
theorem left230 : leftChild 9 PR SL normal450 1 8 262144 = cell461 := by
  calc
    leftChild 9 PR SL normal450 1 8 262144 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal450) 1 8 262144).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal450) 1 8 262144).symm
    _ = cell461 := by rfl
theorem right230 : rightChild 9 PR SL normal450 1 8 262144 = cell462 := by
  calc
    rightChild 9 PR SL normal450 1 8 262144 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal450) 1 8 262144).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal450) 1 8 262144).symm
    _ = cell462 := by rfl
theorem normalized231 : AdaptiveCoverage.normalize SL cell461 = normal451 := by
  calc
    AdaptiveCoverage.normalize SL cell461 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell461)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell461)).symm
    _ = normal451 := by rfl
theorem left231 : leftChild 9 PR SL normal451 0 9 335872 = cell463 := by
  calc
    leftChild 9 PR SL normal451 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal451) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal451) 0 9 335872).symm
    _ = cell463 := by rfl
theorem right231 : rightChild 9 PR SL normal451 0 9 335872 = cell464 := by
  calc
    rightChild 9 PR SL normal451 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal451) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal451) 0 9 335872).symm
    _ = cell464 := by rfl

set_option pp.fullNames true
#print axioms normalized224
#print axioms left224
#print axioms right224
#print axioms normalized225
#print axioms left225
#print axioms right225
#print axioms normalized226
#print axioms left226
#print axioms right226
#print axioms normalized227
#print axioms left227
#print axioms right227
#print axioms normalized228
#print axioms left228
#print axioms right228
#print axioms normalized229
#print axioms left229
#print axioms right229
#print axioms normalized230
#print axioms left230
#print axioms right230
#print axioms normalized231
#print axioms left231
#print axioms right231
end StructuralGoal20261016.W10Aux478
end
