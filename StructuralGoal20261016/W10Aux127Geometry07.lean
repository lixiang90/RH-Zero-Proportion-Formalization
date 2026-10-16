/- Frozen 127-leaf W10 subtree; complete global coverage is not asserted. -/
import StructuralGoal20261016.W10Aux127Data
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
namespace StructuralGoal20261016.W10Aux127
theorem normalized056 : AdaptiveCoverage.normalize SL cell111 = normal105 := by
  calc
    AdaptiveCoverage.normalize SL cell111 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell111)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell111)).symm
    _ = normal105 := by rfl
theorem left056 : leftChild 9 PR SL normal105 0 8 278528 = cell113 := by
  calc
    leftChild 9 PR SL normal105 0 8 278528 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal105) 0 8 278528).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal105) 0 8 278528).symm
    _ = cell113 := by rfl
theorem right056 : rightChild 9 PR SL normal105 0 8 278528 = cell114 := by
  calc
    rightChild 9 PR SL normal105 0 8 278528 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal105) 0 8 278528).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal105) 0 8 278528).symm
    _ = cell114 := by rfl
theorem normalized057 : AdaptiveCoverage.normalize SL cell114 = normal107 := by
  calc
    AdaptiveCoverage.normalize SL cell114 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell114)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell114)).symm
    _ = normal107 := by rfl
theorem left057 : leftChild 9 PR SL normal107 1 9 278528 = cell115 := by
  calc
    leftChild 9 PR SL normal107 1 9 278528 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal107) 1 9 278528).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal107) 1 9 278528).symm
    _ = cell115 := by rfl
theorem right057 : rightChild 9 PR SL normal107 1 9 278528 = cell116 := by
  calc
    rightChild 9 PR SL normal107 1 9 278528 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal107) 1 9 278528).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal107) 1 9 278528).symm
    _ = cell116 := by rfl
theorem normalized058 : AdaptiveCoverage.normalize SL cell116 = normal109 := by
  calc
    AdaptiveCoverage.normalize SL cell116 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell116)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell116)).symm
    _ = normal109 := by rfl
theorem left058 : leftChild 9 PR SL normal109 2 6 163840 = cell117 := by
  calc
    leftChild 9 PR SL normal109 2 6 163840 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal109) 2 6 163840).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal109) 2 6 163840).symm
    _ = cell117 := by rfl
theorem right058 : rightChild 9 PR SL normal109 2 6 163840 = cell118 := by
  calc
    rightChild 9 PR SL normal109 2 6 163840 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal109) 2 6 163840).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal109) 2 6 163840).symm
    _ = cell118 := by rfl
theorem normalized059 : AdaptiveCoverage.normalize SL cell117 = normal110 := by
  calc
    AdaptiveCoverage.normalize SL cell117 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell117)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell117)).symm
    _ = normal110 := by rfl
theorem left059 : leftChild 9 PR SL normal110 3 9 196608 = cell119 := by
  calc
    leftChild 9 PR SL normal110 3 9 196608 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal110) 3 9 196608).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal110) 3 9 196608).symm
    _ = cell119 := by rfl
theorem right059 : rightChild 9 PR SL normal110 3 9 196608 = cell120 := by
  calc
    rightChild 9 PR SL normal110 3 9 196608 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal110) 3 9 196608).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal110) 3 9 196608).symm
    _ = cell120 := by rfl
theorem normalized060 : AdaptiveCoverage.normalize SL cell120 = normal112 := by
  calc
    AdaptiveCoverage.normalize SL cell120 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell120)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell120)).symm
    _ = normal112 := by rfl
theorem left060 : leftChild 9 PR SL normal112 0 9 319488 = cell121 := by
  calc
    leftChild 9 PR SL normal112 0 9 319488 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal112) 0 9 319488).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal112) 0 9 319488).symm
    _ = cell121 := by rfl
theorem right060 : rightChild 9 PR SL normal112 0 9 319488 = cell122 := by
  calc
    rightChild 9 PR SL normal112 0 9 319488 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal112) 0 9 319488).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal112) 0 9 319488).symm
    _ = cell122 := by rfl
theorem normalized061 : AdaptiveCoverage.normalize SL cell122 = normal114 := by
  calc
    AdaptiveCoverage.normalize SL cell122 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell122)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell122)).symm
    _ = normal114 := by rfl
theorem left061 : leftChild 9 PR SL normal114 1 8 245760 = cell123 := by
  calc
    leftChild 9 PR SL normal114 1 8 245760 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal114) 1 8 245760).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal114) 1 8 245760).symm
    _ = cell123 := by rfl
theorem right061 : rightChild 9 PR SL normal114 1 8 245760 = cell124 := by
  calc
    rightChild 9 PR SL normal114 1 8 245760 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal114) 1 8 245760).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal114) 1 8 245760).symm
    _ = cell124 := by rfl
theorem normalized062 : AdaptiveCoverage.normalize SL cell124 = normal116 := by
  calc
    AdaptiveCoverage.normalize SL cell124 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell124)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell124)).symm
    _ = normal116 := by rfl
theorem left062 : leftChild 9 PR SL normal116 3 7 131072 = cell125 := by
  calc
    leftChild 9 PR SL normal116 3 7 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal116) 3 7 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal116) 3 7 131072).symm
    _ = cell125 := by rfl
theorem right062 : rightChild 9 PR SL normal116 3 7 131072 = cell126 := by
  calc
    rightChild 9 PR SL normal116 3 7 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal116) 3 7 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal116) 3 7 131072).symm
    _ = cell126 := by rfl
theorem normalized063 : AdaptiveCoverage.normalize SL cell126 = normal118 := by
  calc
    AdaptiveCoverage.normalize SL cell126 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell126)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell126)).symm
    _ = normal118 := by rfl
theorem left063 : leftChild 9 PR SL normal118 3 5 65536 = cell127 := by
  calc
    leftChild 9 PR SL normal118 3 5 65536 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal118) 3 5 65536).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal118) 3 5 65536).symm
    _ = cell127 := by rfl
theorem right063 : rightChild 9 PR SL normal118 3 5 65536 = cell128 := by
  calc
    rightChild 9 PR SL normal118 3 5 65536 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal118) 3 5 65536).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal118) 3 5 65536).symm
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
end StructuralGoal20261016.W10Aux127
end
