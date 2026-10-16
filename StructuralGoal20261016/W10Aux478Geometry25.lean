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
theorem normalized200 : AdaptiveCoverage.normalize SL cell399 = normal386 := by
  calc
    AdaptiveCoverage.normalize SL cell399 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell399)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell399)).symm
    _ = normal386 := by rfl
theorem left200 : leftChild 9 PR SL normal386 0 9 335872 = cell401 := by
  calc
    leftChild 9 PR SL normal386 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal386) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal386) 0 9 335872).symm
    _ = cell401 := by rfl
theorem right200 : rightChild 9 PR SL normal386 0 9 335872 = cell402 := by
  calc
    rightChild 9 PR SL normal386 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal386) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal386) 0 9 335872).symm
    _ = cell402 := by rfl
theorem normalized201 : AdaptiveCoverage.normalize SL cell368 = normal393 := by
  calc
    AdaptiveCoverage.normalize SL cell368 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell368)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell368)).symm
    _ = normal393 := by rfl
theorem left201 : leftChild 9 PR SL normal393 3 7 131072 = cell403 := by
  calc
    leftChild 9 PR SL normal393 3 7 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal393) 3 7 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal393) 3 7 131072).symm
    _ = cell403 := by rfl
theorem right201 : rightChild 9 PR SL normal393 3 7 131072 = cell404 := by
  calc
    rightChild 9 PR SL normal393 3 7 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal393) 3 7 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal393) 3 7 131072).symm
    _ = cell404 := by rfl
theorem normalized202 : AdaptiveCoverage.normalize SL cell404 = normal395 := by
  calc
    AdaptiveCoverage.normalize SL cell404 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell404)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell404)).symm
    _ = normal395 := by rfl
theorem left202 : leftChild 9 PR SL normal395 0 8 294912 = cell405 := by
  calc
    leftChild 9 PR SL normal395 0 8 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal395) 0 8 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal395) 0 8 294912).symm
    _ = cell405 := by rfl
theorem right202 : rightChild 9 PR SL normal395 0 8 294912 = cell406 := by
  calc
    rightChild 9 PR SL normal395 0 8 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal395) 0 8 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal395) 0 8 294912).symm
    _ = cell406 := by rfl
theorem normalized203 : AdaptiveCoverage.normalize SL cell406 = normal397 := by
  calc
    AdaptiveCoverage.normalize SL cell406 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell406)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell406)).symm
    _ = normal397 := by rfl
theorem left203 : leftChild 9 PR SL normal397 1 9 294912 = cell407 := by
  calc
    leftChild 9 PR SL normal397 1 9 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal397) 1 9 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal397) 1 9 294912).symm
    _ = cell407 := by rfl
theorem right203 : rightChild 9 PR SL normal397 1 9 294912 = cell408 := by
  calc
    rightChild 9 PR SL normal397 1 9 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal397) 1 9 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal397) 1 9 294912).symm
    _ = cell408 := by rfl
theorem normalized204 : AdaptiveCoverage.normalize SL cell408 = normal399 := by
  calc
    AdaptiveCoverage.normalize SL cell408 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell408)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell408)).symm
    _ = normal399 := by rfl
theorem left204 : leftChild 9 PR SL normal399 3 5 81920 = cell409 := by
  calc
    leftChild 9 PR SL normal399 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal399) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal399) 3 5 81920).symm
    _ = cell409 := by rfl
theorem right204 : rightChild 9 PR SL normal399 3 5 81920 = cell410 := by
  calc
    rightChild 9 PR SL normal399 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal399) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal399) 3 5 81920).symm
    _ = cell410 := by rfl
theorem normalized205 : AdaptiveCoverage.normalize SL cell366 = normal402 := by
  calc
    AdaptiveCoverage.normalize SL cell366 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell366)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell366)).symm
    _ = normal402 := by rfl
theorem left205 : leftChild 9 PR SL normal402 1 6 196608 = cell411 := by
  calc
    leftChild 9 PR SL normal402 1 6 196608 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal402) 1 6 196608).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal402) 1 6 196608).symm
    _ = cell411 := by rfl
theorem right205 : rightChild 9 PR SL normal402 1 6 196608 = cell412 := by
  calc
    rightChild 9 PR SL normal402 1 6 196608 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal402) 1 6 196608).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal402) 1 6 196608).symm
    _ = cell412 := by rfl
theorem normalized206 : AdaptiveCoverage.normalize SL cell411 = normal403 := by
  calc
    AdaptiveCoverage.normalize SL cell411 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell411)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell411)).symm
    _ = normal403 := by rfl
theorem left206 : leftChild 9 PR SL normal403 3 7 131072 = cell413 := by
  calc
    leftChild 9 PR SL normal403 3 7 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal403) 3 7 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal403) 3 7 131072).symm
    _ = cell413 := by rfl
theorem right206 : rightChild 9 PR SL normal403 3 7 131072 = cell414 := by
  calc
    rightChild 9 PR SL normal403 3 7 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal403) 3 7 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal403) 3 7 131072).symm
    _ = cell414 := by rfl
theorem normalized207 : AdaptiveCoverage.normalize SL cell414 = normal405 := by
  calc
    AdaptiveCoverage.normalize SL cell414 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell414)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell414)).symm
    _ = normal405 := by rfl
theorem left207 : leftChild 9 PR SL normal405 0 8 294912 = cell415 := by
  calc
    leftChild 9 PR SL normal405 0 8 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal405) 0 8 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal405) 0 8 294912).symm
    _ = cell415 := by rfl
theorem right207 : rightChild 9 PR SL normal405 0 8 294912 = cell416 := by
  calc
    rightChild 9 PR SL normal405 0 8 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal405) 0 8 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal405) 0 8 294912).symm
    _ = cell416 := by rfl

set_option pp.fullNames true
#print axioms normalized200
#print axioms left200
#print axioms right200
#print axioms normalized201
#print axioms left201
#print axioms right201
#print axioms normalized202
#print axioms left202
#print axioms right202
#print axioms normalized203
#print axioms left203
#print axioms right203
#print axioms normalized204
#print axioms left204
#print axioms right204
#print axioms normalized205
#print axioms left205
#print axioms right205
#print axioms normalized206
#print axioms left206
#print axioms right206
#print axioms normalized207
#print axioms left207
#print axioms right207
end StructuralGoal20261016.W10Aux478
end
