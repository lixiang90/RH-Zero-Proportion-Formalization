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
theorem normalized152 : AdaptiveCoverage.normalize SL cell262 = normal296 := by
  calc
    AdaptiveCoverage.normalize SL cell262 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell262)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell262)).symm
    _ = normal296 := by rfl
theorem left152 : leftChild 9 PR SL normal296 2 6 131072 = cell305 := by
  calc
    leftChild 9 PR SL normal296 2 6 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal296) 2 6 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal296) 2 6 131072).symm
    _ = cell305 := by rfl
theorem right152 : rightChild 9 PR SL normal296 2 6 131072 = cell306 := by
  calc
    rightChild 9 PR SL normal296 2 6 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal296) 2 6 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal296) 2 6 131072).symm
    _ = cell306 := by rfl
theorem normalized153 : AdaptiveCoverage.normalize SL cell306 = normal298 := by
  calc
    AdaptiveCoverage.normalize SL cell306 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell306)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell306)).symm
    _ = normal298 := by rfl
theorem left153 : leftChild 9 PR SL normal298 0 8 294912 = cell307 := by
  calc
    leftChild 9 PR SL normal298 0 8 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal298) 0 8 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal298) 0 8 294912).symm
    _ = cell307 := by rfl
theorem right153 : rightChild 9 PR SL normal298 0 8 294912 = cell308 := by
  calc
    rightChild 9 PR SL normal298 0 8 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal298) 0 8 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal298) 0 8 294912).symm
    _ = cell308 := by rfl
theorem normalized154 : AdaptiveCoverage.normalize SL cell307 = normal299 := by
  calc
    AdaptiveCoverage.normalize SL cell307 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell307)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell307)).symm
    _ = normal299 := by rfl
theorem left154 : leftChild 9 PR SL normal299 3 5 81920 = cell309 := by
  calc
    leftChild 9 PR SL normal299 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal299) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal299) 3 5 81920).symm
    _ = cell309 := by rfl
theorem right154 : rightChild 9 PR SL normal299 3 5 81920 = cell310 := by
  calc
    rightChild 9 PR SL normal299 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal299) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal299) 3 5 81920).symm
    _ = cell310 := by rfl
theorem normalized155 : AdaptiveCoverage.normalize SL cell309 = normal300 := by
  calc
    AdaptiveCoverage.normalize SL cell309 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell309)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell309)).symm
    _ = normal300 := by rfl
theorem left155 : leftChild 9 PR SL normal300 4 6 81920 = cell311 := by
  calc
    leftChild 9 PR SL normal300 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal300) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal300) 4 6 81920).symm
    _ = cell311 := by rfl
theorem right155 : rightChild 9 PR SL normal300 4 6 81920 = cell312 := by
  calc
    rightChild 9 PR SL normal300 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal300) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal300) 4 6 81920).symm
    _ = cell312 := by rfl
theorem normalized156 : AdaptiveCoverage.normalize SL cell311 = normal301 := by
  calc
    AdaptiveCoverage.normalize SL cell311 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell311)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell311)).symm
    _ = normal301 := by rfl
theorem left156 : leftChild 9 PR SL normal301 0 9 335872 = cell313 := by
  calc
    leftChild 9 PR SL normal301 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal301) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal301) 0 9 335872).symm
    _ = cell313 := by rfl
theorem right156 : rightChild 9 PR SL normal301 0 9 335872 = cell314 := by
  calc
    rightChild 9 PR SL normal301 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal301) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal301) 0 9 335872).symm
    _ = cell314 := by rfl
theorem normalized157 : AdaptiveCoverage.normalize SL cell313 = normal302 := by
  calc
    AdaptiveCoverage.normalize SL cell313 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell313)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell313)).symm
    _ = normal302 := by rfl
theorem left157 : leftChild 9 PR SL normal302 4 7 114688 = cell315 := by
  calc
    leftChild 9 PR SL normal302 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal302) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal302) 4 7 114688).symm
    _ = cell315 := by rfl
theorem right157 : rightChild 9 PR SL normal302 4 7 114688 = cell316 := by
  calc
    rightChild 9 PR SL normal302 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal302) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal302) 4 7 114688).symm
    _ = cell316 := by rfl
theorem normalized158 : AdaptiveCoverage.normalize SL cell316 = normal304 := by
  calc
    AdaptiveCoverage.normalize SL cell316 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell316)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell316)).symm
    _ = normal304 := by rfl
theorem left158 : leftChild 9 PR SL normal304 3 6 114688 = cell317 := by
  calc
    leftChild 9 PR SL normal304 3 6 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal304) 3 6 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal304) 3 6 114688).symm
    _ = cell317 := by rfl
theorem right158 : rightChild 9 PR SL normal304 3 6 114688 = cell318 := by
  calc
    rightChild 9 PR SL normal304 3 6 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal304) 3 6 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal304) 3 6 114688).symm
    _ = cell318 := by rfl
theorem normalized159 : AdaptiveCoverage.normalize SL cell317 = normal305 := by
  calc
    AdaptiveCoverage.normalize SL cell317 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell317)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell317)).symm
    _ = normal305 := by rfl
theorem left159 : leftChild 9 PR SL normal305 2 5 98304 = cell319 := by
  calc
    leftChild 9 PR SL normal305 2 5 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal305) 2 5 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal305) 2 5 98304).symm
    _ = cell319 := by rfl
theorem right159 : rightChild 9 PR SL normal305 2 5 98304 = cell320 := by
  calc
    rightChild 9 PR SL normal305 2 5 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal305) 2 5 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal305) 2 5 98304).symm
    _ = cell320 := by rfl

set_option pp.fullNames true
#print axioms normalized152
#print axioms left152
#print axioms right152
#print axioms normalized153
#print axioms left153
#print axioms right153
#print axioms normalized154
#print axioms left154
#print axioms right154
#print axioms normalized155
#print axioms left155
#print axioms right155
#print axioms normalized156
#print axioms left156
#print axioms right156
#print axioms normalized157
#print axioms left157
#print axioms right157
#print axioms normalized158
#print axioms left158
#print axioms right158
#print axioms normalized159
#print axioms left159
#print axioms right159
end StructuralGoal20261016.W10Aux478
end
