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
theorem normalized056 : AdaptiveCoverage.normalize SL cell111 = normal096 := by
  calc
    AdaptiveCoverage.normalize SL cell111 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell111)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell111)).symm
    _ = normal096 := by rfl
theorem left056 : leftChild 9 PR SL normal096 3 6 98304 = cell113 := by
  calc
    leftChild 9 PR SL normal096 3 6 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal096) 3 6 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal096) 3 6 98304).symm
    _ = cell113 := by rfl
theorem right056 : rightChild 9 PR SL normal096 3 6 98304 = cell114 := by
  calc
    rightChild 9 PR SL normal096 3 6 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal096) 3 6 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal096) 3 6 98304).symm
    _ = cell114 := by rfl
theorem normalized057 : AdaptiveCoverage.normalize SL cell114 = normal098 := by
  calc
    AdaptiveCoverage.normalize SL cell114 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell114)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell114)).symm
    _ = normal098 := by rfl
theorem left057 : leftChild 9 PR SL normal098 2 5 98304 = cell115 := by
  calc
    leftChild 9 PR SL normal098 2 5 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal098) 2 5 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal098) 2 5 98304).symm
    _ = cell115 := by rfl
theorem right057 : rightChild 9 PR SL normal098 2 5 98304 = cell116 := by
  calc
    rightChild 9 PR SL normal098 2 5 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal098) 2 5 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal098) 2 5 98304).symm
    _ = cell116 := by rfl
theorem normalized058 : AdaptiveCoverage.normalize SL cell116 = normal100 := by
  calc
    AdaptiveCoverage.normalize SL cell116 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell116)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell116)).symm
    _ = normal100 := by rfl
theorem left058 : leftChild 9 PR SL normal100 3 7 147456 = cell117 := by
  calc
    leftChild 9 PR SL normal100 3 7 147456 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal100) 3 7 147456).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal100) 3 7 147456).symm
    _ = cell117 := by rfl
theorem right058 : rightChild 9 PR SL normal100 3 7 147456 = cell118 := by
  calc
    rightChild 9 PR SL normal100 3 7 147456 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal100) 3 7 147456).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal100) 3 7 147456).symm
    _ = cell118 := by rfl
theorem normalized059 : AdaptiveCoverage.normalize SL cell100 = normal108 := by
  calc
    AdaptiveCoverage.normalize SL cell100 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell100)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell100)).symm
    _ = normal108 := by rfl
theorem left059 : leftChild 9 PR SL normal108 3 5 81920 = cell119 := by
  calc
    leftChild 9 PR SL normal108 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal108) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal108) 3 5 81920).symm
    _ = cell119 := by rfl
theorem right059 : rightChild 9 PR SL normal108 3 5 81920 = cell120 := by
  calc
    rightChild 9 PR SL normal108 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal108) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal108) 3 5 81920).symm
    _ = cell120 := by rfl
theorem normalized060 : AdaptiveCoverage.normalize SL cell119 = normal109 := by
  calc
    AdaptiveCoverage.normalize SL cell119 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell119)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell119)).symm
    _ = normal109 := by rfl
theorem left060 : leftChild 9 PR SL normal109 4 6 81920 = cell121 := by
  calc
    leftChild 9 PR SL normal109 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal109) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal109) 4 6 81920).symm
    _ = cell121 := by rfl
theorem right060 : rightChild 9 PR SL normal109 4 6 81920 = cell122 := by
  calc
    rightChild 9 PR SL normal109 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal109) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal109) 4 6 81920).symm
    _ = cell122 := by rfl
theorem normalized061 : AdaptiveCoverage.normalize SL cell121 = normal110 := by
  calc
    AdaptiveCoverage.normalize SL cell121 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell121)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell121)).symm
    _ = normal110 := by rfl
theorem left061 : leftChild 9 PR SL normal110 0 8 294912 = cell123 := by
  calc
    leftChild 9 PR SL normal110 0 8 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal110) 0 8 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal110) 0 8 294912).symm
    _ = cell123 := by rfl
theorem right061 : rightChild 9 PR SL normal110 0 8 294912 = cell124 := by
  calc
    rightChild 9 PR SL normal110 0 8 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal110) 0 8 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal110) 0 8 294912).symm
    _ = cell124 := by rfl
theorem normalized062 : AdaptiveCoverage.normalize SL cell123 = normal111 := by
  calc
    AdaptiveCoverage.normalize SL cell123 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell123)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell123)).symm
    _ = normal111 := by rfl
theorem left062 : leftChild 9 PR SL normal111 3 9 229376 = cell125 := by
  calc
    leftChild 9 PR SL normal111 3 9 229376 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal111) 3 9 229376).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal111) 3 9 229376).symm
    _ = cell125 := by rfl
theorem right062 : rightChild 9 PR SL normal111 3 9 229376 = cell126 := by
  calc
    rightChild 9 PR SL normal111 3 9 229376 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal111) 3 9 229376).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal111) 3 9 229376).symm
    _ = cell126 := by rfl
theorem normalized063 : AdaptiveCoverage.normalize SL cell125 = normal112 := by
  calc
    AdaptiveCoverage.normalize SL cell125 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell125)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell125)).symm
    _ = normal112 := by rfl
theorem left063 : leftChild 9 PR SL normal112 0 9 335872 = cell127 := by
  calc
    leftChild 9 PR SL normal112 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal112) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal112) 0 9 335872).symm
    _ = cell127 := by rfl
theorem right063 : rightChild 9 PR SL normal112 0 9 335872 = cell128 := by
  calc
    rightChild 9 PR SL normal112 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal112) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal112) 0 9 335872).symm
    _ = cell128 := by rfl

set_option pp.fullNames true
#print axioms normalized056
#print axioms left056
#print axioms right056
#print axioms normalized057
#print axioms left057
#print axioms right057
#print axioms normalized058
#print axioms left058
#print axioms right058
#print axioms normalized059
#print axioms left059
#print axioms right059
#print axioms normalized060
#print axioms left060
#print axioms right060
#print axioms normalized061
#print axioms left061
#print axioms right061
#print axioms normalized062
#print axioms left062
#print axioms right062
#print axioms normalized063
#print axioms left063
#print axioms right063
end StructuralGoal20261016.W10Aux478
end
