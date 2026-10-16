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
theorem normalized168 : AdaptiveCoverage.normalize SL cell336 = normal325 := by
  calc
    AdaptiveCoverage.normalize SL cell336 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell336)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell336)).symm
    _ = normal325 := by rfl
theorem left168 : leftChild 9 PR SL normal325 2 4 81920 = cell337 := by
  calc
    leftChild 9 PR SL normal325 2 4 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal325) 2 4 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal325) 2 4 81920).symm
    _ = cell337 := by rfl
theorem right168 : rightChild 9 PR SL normal325 2 4 81920 = cell338 := by
  calc
    rightChild 9 PR SL normal325 2 4 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal325) 2 4 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal325) 2 4 81920).symm
    _ = cell338 := by rfl
theorem normalized169 : AdaptiveCoverage.normalize SL cell337 = normal326 := by
  calc
    AdaptiveCoverage.normalize SL cell337 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell337)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell337)).symm
    _ = normal326 := by rfl
theorem left169 : leftChild 9 PR SL normal326 1 9 294912 = cell339 := by
  calc
    leftChild 9 PR SL normal326 1 9 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal326) 1 9 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal326) 1 9 294912).symm
    _ = cell339 := by rfl
theorem right169 : rightChild 9 PR SL normal326 1 9 294912 = cell340 := by
  calc
    rightChild 9 PR SL normal326 1 9 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal326) 1 9 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal326) 1 9 294912).symm
    _ = cell340 := by rfl
theorem normalized170 : AdaptiveCoverage.normalize SL cell340 = normal328 := by
  calc
    AdaptiveCoverage.normalize SL cell340 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell340)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell340)).symm
    _ = normal328 := by rfl
theorem left170 : leftChild 9 PR SL normal328 2 6 147456 = cell341 := by
  calc
    leftChild 9 PR SL normal328 2 6 147456 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal328) 2 6 147456).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal328) 2 6 147456).symm
    _ = cell341 := by rfl
theorem right170 : rightChild 9 PR SL normal328 2 6 147456 = cell342 := by
  calc
    rightChild 9 PR SL normal328 2 6 147456 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal328) 2 6 147456).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal328) 2 6 147456).symm
    _ = cell342 := by rfl
theorem normalized171 : AdaptiveCoverage.normalize SL cell328 = normal332 := by
  calc
    AdaptiveCoverage.normalize SL cell328 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell328)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell328)).symm
    _ = normal332 := by rfl
theorem left171 : leftChild 9 PR SL normal332 1 9 294912 = cell343 := by
  calc
    leftChild 9 PR SL normal332 1 9 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal332) 1 9 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal332) 1 9 294912).symm
    _ = cell343 := by rfl
theorem right171 : rightChild 9 PR SL normal332 1 9 294912 = cell344 := by
  calc
    rightChild 9 PR SL normal332 1 9 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal332) 1 9 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal332) 1 9 294912).symm
    _ = cell344 := by rfl
theorem normalized172 : AdaptiveCoverage.normalize SL cell344 = normal334 := by
  calc
    AdaptiveCoverage.normalize SL cell344 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell344)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell344)).symm
    _ = normal334 := by rfl
theorem left172 : leftChild 9 PR SL normal334 4 7 114688 = cell345 := by
  calc
    leftChild 9 PR SL normal334 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal334) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal334) 4 7 114688).symm
    _ = cell345 := by rfl
theorem right172 : rightChild 9 PR SL normal334 4 7 114688 = cell346 := by
  calc
    rightChild 9 PR SL normal334 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal334) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal334) 4 7 114688).symm
    _ = cell346 := by rfl
theorem normalized173 : AdaptiveCoverage.normalize SL cell346 = normal336 := by
  calc
    AdaptiveCoverage.normalize SL cell346 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell346)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell346)).symm
    _ = normal336 := by rfl
theorem left173 : leftChild 9 PR SL normal336 3 6 98304 = cell347 := by
  calc
    leftChild 9 PR SL normal336 3 6 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal336) 3 6 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal336) 3 6 98304).symm
    _ = cell347 := by rfl
theorem right173 : rightChild 9 PR SL normal336 3 6 98304 = cell348 := by
  calc
    rightChild 9 PR SL normal336 3 6 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal336) 3 6 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal336) 3 6 98304).symm
    _ = cell348 := by rfl
theorem normalized174 : AdaptiveCoverage.normalize SL cell348 = normal338 := by
  calc
    AdaptiveCoverage.normalize SL cell348 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell348)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell348)).symm
    _ = normal338 := by rfl
theorem left174 : leftChild 9 PR SL normal338 2 5 98304 = cell349 := by
  calc
    leftChild 9 PR SL normal338 2 5 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal338) 2 5 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal338) 2 5 98304).symm
    _ = cell349 := by rfl
theorem right174 : rightChild 9 PR SL normal338 2 5 98304 = cell350 := by
  calc
    rightChild 9 PR SL normal338 2 5 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal338) 2 5 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal338) 2 5 98304).symm
    _ = cell350 := by rfl
theorem normalized175 : AdaptiveCoverage.normalize SL cell350 = normal340 := by
  calc
    AdaptiveCoverage.normalize SL cell350 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell350)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell350)).symm
    _ = normal340 := by rfl
theorem left175 : leftChild 9 PR SL normal340 5 7 81920 = cell351 := by
  calc
    leftChild 9 PR SL normal340 5 7 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal340) 5 7 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal340) 5 7 81920).symm
    _ = cell351 := by rfl
theorem right175 : rightChild 9 PR SL normal340 5 7 81920 = cell352 := by
  calc
    rightChild 9 PR SL normal340 5 7 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal340) 5 7 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal340) 5 7 81920).symm
    _ = cell352 := by rfl

set_option pp.fullNames true
#print axioms normalized168
#print axioms left168
#print axioms right168
#print axioms normalized169
#print axioms left169
#print axioms right169
#print axioms normalized170
#print axioms left170
#print axioms right170
#print axioms normalized171
#print axioms left171
#print axioms right171
#print axioms normalized172
#print axioms left172
#print axioms right172
#print axioms normalized173
#print axioms left173
#print axioms right173
#print axioms normalized174
#print axioms left174
#print axioms right174
#print axioms normalized175
#print axioms left175
#print axioms right175
end StructuralGoal20261016.W10Aux478
end
