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
theorem normalized120 : AdaptiveCoverage.normalize SL cell239 = normal233 := by
  calc
    AdaptiveCoverage.normalize SL cell239 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell239)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell239)).symm
    _ = normal233 := by rfl
theorem left120 : leftChild 9 PR SL normal233 3 5 81920 = cell241 := by
  calc
    leftChild 9 PR SL normal233 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal233) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal233) 3 5 81920).symm
    _ = cell241 := by rfl
theorem right120 : rightChild 9 PR SL normal233 3 5 81920 = cell242 := by
  calc
    rightChild 9 PR SL normal233 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal233) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal233) 3 5 81920).symm
    _ = cell242 := by rfl
theorem normalized121 : AdaptiveCoverage.normalize SL cell242 = normal235 := by
  calc
    AdaptiveCoverage.normalize SL cell242 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell242)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell242)).symm
    _ = normal235 := by rfl
theorem left121 : leftChild 9 PR SL normal235 0 9 319488 = cell243 := by
  calc
    leftChild 9 PR SL normal235 0 9 319488 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal235) 0 9 319488).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal235) 0 9 319488).symm
    _ = cell243 := by rfl
theorem right121 : rightChild 9 PR SL normal235 0 9 319488 = cell244 := by
  calc
    rightChild 9 PR SL normal235 0 9 319488 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal235) 0 9 319488).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal235) 0 9 319488).symm
    _ = cell244 := by rfl
theorem normalized122 : AdaptiveCoverage.normalize SL cell244 = normal237 := by
  calc
    AdaptiveCoverage.normalize SL cell244 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell244)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell244)).symm
    _ = normal237 := by rfl
theorem left122 : leftChild 9 PR SL normal237 2 5 131072 = cell245 := by
  calc
    leftChild 9 PR SL normal237 2 5 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal237) 2 5 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal237) 2 5 131072).symm
    _ = cell245 := by rfl
theorem right122 : rightChild 9 PR SL normal237 2 5 131072 = cell246 := by
  calc
    rightChild 9 PR SL normal237 2 5 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal237) 2 5 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal237) 2 5 131072).symm
    _ = cell246 := by rfl
theorem normalized123 : AdaptiveCoverage.normalize SL cell245 = normal238 := by
  calc
    AdaptiveCoverage.normalize SL cell245 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell245)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell245)).symm
    _ = normal238 := by rfl
theorem left123 : leftChild 9 PR SL normal238 3 9 229376 = cell247 := by
  calc
    leftChild 9 PR SL normal238 3 9 229376 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal238) 3 9 229376).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal238) 3 9 229376).symm
    _ = cell247 := by rfl
theorem right123 : rightChild 9 PR SL normal238 3 9 229376 = cell248 := by
  calc
    rightChild 9 PR SL normal238 3 9 229376 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal238) 3 9 229376).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal238) 3 9 229376).symm
    _ = cell248 := by rfl
theorem normalized124 : AdaptiveCoverage.normalize SL cell247 = normal239 := by
  calc
    AdaptiveCoverage.normalize SL cell247 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell247)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell247)).symm
    _ = normal239 := by rfl
theorem left124 : leftChild 9 PR SL normal239 4 6 81920 = cell249 := by
  calc
    leftChild 9 PR SL normal239 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal239) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal239) 4 6 81920).symm
    _ = cell249 := by rfl
theorem right124 : rightChild 9 PR SL normal239 4 6 81920 = cell250 := by
  calc
    rightChild 9 PR SL normal239 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal239) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal239) 4 6 81920).symm
    _ = cell250 := by rfl
theorem normalized125 : AdaptiveCoverage.normalize SL cell240 = normal244 := by
  calc
    AdaptiveCoverage.normalize SL cell240 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell240)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell240)).symm
    _ = normal244 := by rfl
theorem left125 : leftChild 9 PR SL normal244 0 9 319488 = cell251 := by
  calc
    leftChild 9 PR SL normal244 0 9 319488 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal244) 0 9 319488).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal244) 0 9 319488).symm
    _ = cell251 := by rfl
theorem right125 : rightChild 9 PR SL normal244 0 9 319488 = cell252 := by
  calc
    rightChild 9 PR SL normal244 0 9 319488 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal244) 0 9 319488).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal244) 0 9 319488).symm
    _ = cell252 := by rfl
theorem normalized126 : AdaptiveCoverage.normalize SL cell252 = normal246 := by
  calc
    AdaptiveCoverage.normalize SL cell252 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell252)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell252)).symm
    _ = normal246 := by rfl
theorem left126 : leftChild 9 PR SL normal246 3 6 131072 = cell253 := by
  calc
    leftChild 9 PR SL normal246 3 6 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal246) 3 6 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal246) 3 6 131072).symm
    _ = cell253 := by rfl
theorem right126 : rightChild 9 PR SL normal246 3 6 131072 = cell254 := by
  calc
    rightChild 9 PR SL normal246 3 6 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal246) 3 6 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal246) 3 6 131072).symm
    _ = cell254 := by rfl
theorem normalized127 : AdaptiveCoverage.normalize SL cell253 = normal247 := by
  calc
    AdaptiveCoverage.normalize SL cell253 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell253)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell253)).symm
    _ = normal247 := by rfl
theorem left127 : leftChild 9 PR SL normal247 3 5 81920 = cell255 := by
  calc
    leftChild 9 PR SL normal247 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal247) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal247) 3 5 81920).symm
    _ = cell255 := by rfl
theorem right127 : rightChild 9 PR SL normal247 3 5 81920 = cell256 := by
  calc
    rightChild 9 PR SL normal247 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal247) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal247) 3 5 81920).symm
    _ = cell256 := by rfl

set_option pp.fullNames true
#print axioms normalized120
#print axioms left120
#print axioms right120
#print axioms normalized121
#print axioms left121
#print axioms right121
#print axioms normalized122
#print axioms left122
#print axioms right122
#print axioms normalized123
#print axioms left123
#print axioms right123
#print axioms normalized124
#print axioms left124
#print axioms right124
#print axioms normalized125
#print axioms left125
#print axioms right125
#print axioms normalized126
#print axioms left126
#print axioms right126
#print axioms normalized127
#print axioms left127
#print axioms right127
end StructuralGoal20261016.W10Aux127
end
