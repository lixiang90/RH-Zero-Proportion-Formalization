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
theorem normalized304 : AdaptiveCoverage.normalize SL cell607 = normal595 := by
  calc
    AdaptiveCoverage.normalize SL cell607 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell607)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell607)).symm
    _ = normal595 := by rfl
theorem left304 : leftChild 9 PR SL normal595 0 9 335872 = cell609 := by
  calc
    leftChild 9 PR SL normal595 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal595) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal595) 0 9 335872).symm
    _ = cell609 := by rfl
theorem right304 : rightChild 9 PR SL normal595 0 9 335872 = cell610 := by
  calc
    rightChild 9 PR SL normal595 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal595) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal595) 0 9 335872).symm
    _ = cell610 := by rfl
theorem normalized305 : AdaptiveCoverage.normalize SL cell609 = normal596 := by
  calc
    AdaptiveCoverage.normalize SL cell609 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell609)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell609)).symm
    _ = normal596 := by rfl
theorem left305 : leftChild 9 PR SL normal596 5 7 81920 = cell611 := by
  calc
    leftChild 9 PR SL normal596 5 7 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal596) 5 7 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal596) 5 7 81920).symm
    _ = cell611 := by rfl
theorem right305 : rightChild 9 PR SL normal596 5 7 81920 = cell612 := by
  calc
    rightChild 9 PR SL normal596 5 7 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal596) 5 7 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal596) 5 7 81920).symm
    _ = cell612 := by rfl
theorem normalized306 : AdaptiveCoverage.normalize SL cell608 = normal600 := by
  calc
    AdaptiveCoverage.normalize SL cell608 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell608)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell608)).symm
    _ = normal600 := by rfl
theorem left306 : leftChild 9 PR SL normal600 5 6 49152 = cell613 := by
  calc
    leftChild 9 PR SL normal600 5 6 49152 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal600) 5 6 49152).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal600) 5 6 49152).symm
    _ = cell613 := by rfl
theorem right306 : rightChild 9 PR SL normal600 5 6 49152 = cell614 := by
  calc
    rightChild 9 PR SL normal600 5 6 49152 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal600) 5 6 49152).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal600) 5 6 49152).symm
    _ = cell614 := by rfl
theorem normalized307 : AdaptiveCoverage.normalize SL cell600 = normal604 := by
  calc
    AdaptiveCoverage.normalize SL cell600 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell600)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell600)).symm
    _ = normal604 := by rfl
theorem left307 : leftChild 9 PR SL normal604 1 9 294912 = cell615 := by
  calc
    leftChild 9 PR SL normal604 1 9 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal604) 1 9 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal604) 1 9 294912).symm
    _ = cell615 := by rfl
theorem right307 : rightChild 9 PR SL normal604 1 9 294912 = cell616 := by
  calc
    rightChild 9 PR SL normal604 1 9 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal604) 1 9 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal604) 1 9 294912).symm
    _ = cell616 := by rfl
theorem normalized308 : AdaptiveCoverage.normalize SL cell615 = normal605 := by
  calc
    AdaptiveCoverage.normalize SL cell615 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell615)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell615)).symm
    _ = normal605 := by rfl
theorem left308 : leftChild 9 PR SL normal605 2 5 114688 = cell617 := by
  calc
    leftChild 9 PR SL normal605 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal605) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal605) 2 5 114688).symm
    _ = cell617 := by rfl
theorem right308 : rightChild 9 PR SL normal605 2 5 114688 = cell618 := by
  calc
    rightChild 9 PR SL normal605 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal605) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal605) 2 5 114688).symm
    _ = cell618 := by rfl
theorem normalized309 : AdaptiveCoverage.normalize SL cell617 = normal606 := by
  calc
    AdaptiveCoverage.normalize SL cell617 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell617)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell617)).symm
    _ = normal606 := by rfl
theorem left309 : leftChild 9 PR SL normal606 0 6 229376 = cell619 := by
  calc
    leftChild 9 PR SL normal606 0 6 229376 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal606) 0 6 229376).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal606) 0 6 229376).symm
    _ = cell619 := by rfl
theorem right309 : rightChild 9 PR SL normal606 0 6 229376 = cell620 := by
  calc
    rightChild 9 PR SL normal606 0 6 229376 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal606) 0 6 229376).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal606) 0 6 229376).symm
    _ = cell620 := by rfl
theorem normalized310 : AdaptiveCoverage.normalize SL cell619 = normal607 := by
  calc
    AdaptiveCoverage.normalize SL cell619 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell619)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell619)).symm
    _ = normal607 := by rfl
theorem left310 : leftChild 9 PR SL normal607 0 9 335872 = cell621 := by
  calc
    leftChild 9 PR SL normal607 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal607) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal607) 0 9 335872).symm
    _ = cell621 := by rfl
theorem right310 : rightChild 9 PR SL normal607 0 9 335872 = cell622 := by
  calc
    rightChild 9 PR SL normal607 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal607) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal607) 0 9 335872).symm
    _ = cell622 := by rfl
theorem normalized311 : AdaptiveCoverage.normalize SL cell621 = normal608 := by
  calc
    AdaptiveCoverage.normalize SL cell621 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell621)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell621)).symm
    _ = normal608 := by rfl
theorem left311 : leftChild 9 PR SL normal608 5 7 81920 = cell623 := by
  calc
    leftChild 9 PR SL normal608 5 7 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal608) 5 7 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal608) 5 7 81920).symm
    _ = cell623 := by rfl
theorem right311 : rightChild 9 PR SL normal608 5 7 81920 = cell624 := by
  calc
    rightChild 9 PR SL normal608 5 7 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal608) 5 7 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal608) 5 7 81920).symm
    _ = cell624 := by rfl

set_option pp.fullNames true
#print axioms normalized304
#print axioms left304
#print axioms right304
#print axioms normalized305
#print axioms left305
#print axioms right305
#print axioms normalized306
#print axioms left306
#print axioms right306
#print axioms normalized307
#print axioms left307
#print axioms right307
#print axioms normalized308
#print axioms left308
#print axioms right308
#print axioms normalized309
#print axioms left309
#print axioms right309
#print axioms normalized310
#print axioms left310
#print axioms right310
#print axioms normalized311
#print axioms left311
#print axioms right311
end StructuralGoal20261016.W10Aux478
end
