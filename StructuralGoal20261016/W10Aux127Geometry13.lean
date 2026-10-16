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
theorem normalized104 : AdaptiveCoverage.normalize SL cell168 = normal202 := by
  calc
    AdaptiveCoverage.normalize SL cell168 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell168)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell168)).symm
    _ = normal202 := by rfl
theorem left104 : leftChild 9 PR SL normal202 0 8 278528 = cell209 := by
  calc
    leftChild 9 PR SL normal202 0 8 278528 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal202) 0 8 278528).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal202) 0 8 278528).symm
    _ = cell209 := by rfl
theorem right104 : rightChild 9 PR SL normal202 0 8 278528 = cell210 := by
  calc
    rightChild 9 PR SL normal202 0 8 278528 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal202) 0 8 278528).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal202) 0 8 278528).symm
    _ = cell210 := by rfl
theorem normalized105 : AdaptiveCoverage.normalize SL cell210 = normal204 := by
  calc
    AdaptiveCoverage.normalize SL cell210 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell210)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell210)).symm
    _ = normal204 := by rfl
theorem left105 : leftChild 9 PR SL normal204 1 9 278528 = cell211 := by
  calc
    leftChild 9 PR SL normal204 1 9 278528 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal204) 1 9 278528).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal204) 1 9 278528).symm
    _ = cell211 := by rfl
theorem right105 : rightChild 9 PR SL normal204 1 9 278528 = cell212 := by
  calc
    rightChild 9 PR SL normal204 1 9 278528 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal204) 1 9 278528).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal204) 1 9 278528).symm
    _ = cell212 := by rfl
theorem normalized106 : AdaptiveCoverage.normalize SL cell212 = normal206 := by
  calc
    AdaptiveCoverage.normalize SL cell212 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell212)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell212)).symm
    _ = normal206 := by rfl
theorem left106 : leftChild 9 PR SL normal206 2 6 163840 = cell213 := by
  calc
    leftChild 9 PR SL normal206 2 6 163840 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal206) 2 6 163840).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal206) 2 6 163840).symm
    _ = cell213 := by rfl
theorem right106 : rightChild 9 PR SL normal206 2 6 163840 = cell214 := by
  calc
    rightChild 9 PR SL normal206 2 6 163840 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal206) 2 6 163840).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal206) 2 6 163840).symm
    _ = cell214 := by rfl
theorem normalized107 : AdaptiveCoverage.normalize SL cell213 = normal207 := by
  calc
    AdaptiveCoverage.normalize SL cell213 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell213)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell213)).symm
    _ = normal207 := by rfl
theorem left107 : leftChild 9 PR SL normal207 3 7 163840 = cell215 := by
  calc
    leftChild 9 PR SL normal207 3 7 163840 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal207) 3 7 163840).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal207) 3 7 163840).symm
    _ = cell215 := by rfl
theorem right107 : rightChild 9 PR SL normal207 3 7 163840 = cell216 := by
  calc
    rightChild 9 PR SL normal207 3 7 163840 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal207) 3 7 163840).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal207) 3 7 163840).symm
    _ = cell216 := by rfl
theorem normalized108 : AdaptiveCoverage.normalize SL cell215 = normal208 := by
  calc
    AdaptiveCoverage.normalize SL cell215 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell215)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell215)).symm
    _ = normal208 := by rfl
theorem left108 : leftChild 9 PR SL normal208 0 9 319488 = cell217 := by
  calc
    leftChild 9 PR SL normal208 0 9 319488 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal208) 0 9 319488).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal208) 0 9 319488).symm
    _ = cell217 := by rfl
theorem right108 : rightChild 9 PR SL normal208 0 9 319488 = cell218 := by
  calc
    rightChild 9 PR SL normal208 0 9 319488 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal208) 0 9 319488).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal208) 0 9 319488).symm
    _ = cell218 := by rfl
theorem normalized109 : AdaptiveCoverage.normalize SL cell218 = normal210 := by
  calc
    AdaptiveCoverage.normalize SL cell218 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell218)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell218)).symm
    _ = normal210 := by rfl
theorem left109 : leftChild 9 PR SL normal210 1 8 245760 = cell219 := by
  calc
    leftChild 9 PR SL normal210 1 8 245760 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal210) 1 8 245760).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal210) 1 8 245760).symm
    _ = cell219 := by rfl
theorem right109 : rightChild 9 PR SL normal210 1 8 245760 = cell220 := by
  calc
    rightChild 9 PR SL normal210 1 8 245760 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal210) 1 8 245760).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal210) 1 8 245760).symm
    _ = cell220 := by rfl
theorem normalized110 : AdaptiveCoverage.normalize SL cell220 = normal212 := by
  calc
    AdaptiveCoverage.normalize SL cell220 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell220)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell220)).symm
    _ = normal212 := by rfl
theorem left110 : leftChild 9 PR SL normal212 0 6 229376 = cell221 := by
  calc
    leftChild 9 PR SL normal212 0 6 229376 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal212) 0 6 229376).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal212) 0 6 229376).symm
    _ = cell221 := by rfl
theorem right110 : rightChild 9 PR SL normal212 0 6 229376 = cell222 := by
  calc
    rightChild 9 PR SL normal212 0 6 229376 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal212) 0 6 229376).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal212) 0 6 229376).symm
    _ = cell222 := by rfl
theorem normalized111 : AdaptiveCoverage.normalize SL cell221 = normal213 := by
  calc
    AdaptiveCoverage.normalize SL cell221 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell221)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell221)).symm
    _ = normal213 := by rfl
theorem left111 : leftChild 9 PR SL normal213 0 7 245760 = cell223 := by
  calc
    leftChild 9 PR SL normal213 0 7 245760 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal213) 0 7 245760).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal213) 0 7 245760).symm
    _ = cell223 := by rfl
theorem right111 : rightChild 9 PR SL normal213 0 7 245760 = cell224 := by
  calc
    rightChild 9 PR SL normal213 0 7 245760 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal213) 0 7 245760).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal213) 0 7 245760).symm
    _ = cell224 := by rfl

set_option pp.fullNames true
#print axioms normalized104
#print axioms left104
#print axioms right104
#print axioms normalized105
#print axioms left105
#print axioms right105
#print axioms normalized106
#print axioms left106
#print axioms right106
#print axioms normalized107
#print axioms left107
#print axioms right107
#print axioms normalized108
#print axioms left108
#print axioms right108
#print axioms normalized109
#print axioms left109
#print axioms right109
#print axioms normalized110
#print axioms left110
#print axioms right110
#print axioms normalized111
#print axioms left111
#print axioms right111
end StructuralGoal20261016.W10Aux127
end
