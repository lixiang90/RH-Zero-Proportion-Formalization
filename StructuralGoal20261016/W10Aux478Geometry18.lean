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
theorem normalized144 : AdaptiveCoverage.normalize SL cell287 = normal276 := by
  calc
    AdaptiveCoverage.normalize SL cell287 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell287)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell287)).symm
    _ = normal276 := by rfl
theorem left144 : leftChild 9 PR SL normal276 4 7 114688 = cell289 := by
  calc
    leftChild 9 PR SL normal276 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal276) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal276) 4 7 114688).symm
    _ = cell289 := by rfl
theorem right144 : rightChild 9 PR SL normal276 4 7 114688 = cell290 := by
  calc
    rightChild 9 PR SL normal276 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal276) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal276) 4 7 114688).symm
    _ = cell290 := by rfl
theorem normalized145 : AdaptiveCoverage.normalize SL cell290 = normal278 := by
  calc
    AdaptiveCoverage.normalize SL cell290 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell290)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell290)).symm
    _ = normal278 := by rfl
theorem left145 : leftChild 9 PR SL normal278 2 5 98304 = cell291 := by
  calc
    leftChild 9 PR SL normal278 2 5 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal278) 2 5 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal278) 2 5 98304).symm
    _ = cell291 := by rfl
theorem right145 : rightChild 9 PR SL normal278 2 5 98304 = cell292 := by
  calc
    rightChild 9 PR SL normal278 2 5 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal278) 2 5 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal278) 2 5 98304).symm
    _ = cell292 := by rfl
theorem normalized146 : AdaptiveCoverage.normalize SL cell292 = normal280 := by
  calc
    AdaptiveCoverage.normalize SL cell292 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell292)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell292)).symm
    _ = normal280 := by rfl
theorem left146 : leftChild 9 PR SL normal280 5 7 81920 = cell293 := by
  calc
    leftChild 9 PR SL normal280 5 7 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal280) 5 7 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal280) 5 7 81920).symm
    _ = cell293 := by rfl
theorem right146 : rightChild 9 PR SL normal280 5 7 81920 = cell294 := by
  calc
    rightChild 9 PR SL normal280 5 7 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal280) 5 7 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal280) 5 7 81920).symm
    _ = cell294 := by rfl
theorem normalized147 : AdaptiveCoverage.normalize SL cell294 = normal282 := by
  calc
    AdaptiveCoverage.normalize SL cell294 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell294)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell294)).symm
    _ = normal282 := by rfl
theorem left147 : leftChild 9 PR SL normal282 2 4 81920 = cell295 := by
  calc
    leftChild 9 PR SL normal282 2 4 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal282) 2 4 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal282) 2 4 81920).symm
    _ = cell295 := by rfl
theorem right147 : rightChild 9 PR SL normal282 2 4 81920 = cell296 := by
  calc
    rightChild 9 PR SL normal282 2 4 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal282) 2 4 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal282) 2 4 81920).symm
    _ = cell296 := by rfl
theorem normalized148 : AdaptiveCoverage.normalize SL cell295 = normal283 := by
  calc
    AdaptiveCoverage.normalize SL cell295 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell295)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell295)).symm
    _ = normal283 := by rfl
theorem left148 : leftChild 9 PR SL normal283 1 9 294912 = cell297 := by
  calc
    leftChild 9 PR SL normal283 1 9 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal283) 1 9 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal283) 1 9 294912).symm
    _ = cell297 := by rfl
theorem right148 : rightChild 9 PR SL normal283 1 9 294912 = cell298 := by
  calc
    rightChild 9 PR SL normal283 1 9 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal283) 1 9 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal283) 1 9 294912).symm
    _ = cell298 := by rfl
theorem normalized149 : AdaptiveCoverage.normalize SL cell298 = normal285 := by
  calc
    AdaptiveCoverage.normalize SL cell298 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell298)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell298)).symm
    _ = normal285 := by rfl
theorem left149 : leftChild 9 PR SL normal285 6 7 49152 = cell299 := by
  calc
    leftChild 9 PR SL normal285 6 7 49152 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal285) 6 7 49152).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal285) 6 7 49152).symm
    _ = cell299 := by rfl
theorem right149 : rightChild 9 PR SL normal285 6 7 49152 = cell300 := by
  calc
    rightChild 9 PR SL normal285 6 7 49152 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal285) 6 7 49152).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal285) 6 7 49152).symm
    _ = cell300 := by rfl
theorem normalized150 : AdaptiveCoverage.normalize SL cell288 = normal289 := by
  calc
    AdaptiveCoverage.normalize SL cell288 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell288)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell288)).symm
    _ = normal289 := by rfl
theorem left150 : leftChild 9 PR SL normal289 1 9 294912 = cell301 := by
  calc
    leftChild 9 PR SL normal289 1 9 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal289) 1 9 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal289) 1 9 294912).symm
    _ = cell301 := by rfl
theorem right150 : rightChild 9 PR SL normal289 1 9 294912 = cell302 := by
  calc
    rightChild 9 PR SL normal289 1 9 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal289) 1 9 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal289) 1 9 294912).symm
    _ = cell302 := by rfl
theorem normalized151 : AdaptiveCoverage.normalize SL cell302 = normal291 := by
  calc
    AdaptiveCoverage.normalize SL cell302 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell302)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell302)).symm
    _ = normal291 := by rfl
theorem left151 : leftChild 9 PR SL normal291 4 7 114688 = cell303 := by
  calc
    leftChild 9 PR SL normal291 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal291) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal291) 4 7 114688).symm
    _ = cell303 := by rfl
theorem right151 : rightChild 9 PR SL normal291 4 7 114688 = cell304 := by
  calc
    rightChild 9 PR SL normal291 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal291) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal291) 4 7 114688).symm
    _ = cell304 := by rfl

set_option pp.fullNames true
#print axioms normalized144
#print axioms left144
#print axioms right144
#print axioms normalized145
#print axioms left145
#print axioms right145
#print axioms normalized146
#print axioms left146
#print axioms right146
#print axioms normalized147
#print axioms left147
#print axioms right147
#print axioms normalized148
#print axioms left148
#print axioms right148
#print axioms normalized149
#print axioms left149
#print axioms right149
#print axioms normalized150
#print axioms left150
#print axioms right150
#print axioms normalized151
#print axioms left151
#print axioms right151
end StructuralGoal20261016.W10Aux478
end
