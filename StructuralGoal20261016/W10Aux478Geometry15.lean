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
theorem normalized120 : AdaptiveCoverage.normalize SL cell239 = normal230 := by
  calc
    AdaptiveCoverage.normalize SL cell239 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell239)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell239)).symm
    _ = normal230 := by rfl
theorem left120 : leftChild 9 PR SL normal230 1 8 262144 = cell241 := by
  calc
    leftChild 9 PR SL normal230 1 8 262144 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal230) 1 8 262144).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal230) 1 8 262144).symm
    _ = cell241 := by rfl
theorem right120 : rightChild 9 PR SL normal230 1 8 262144 = cell242 := by
  calc
    rightChild 9 PR SL normal230 1 8 262144 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal230) 1 8 262144).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal230) 1 8 262144).symm
    _ = cell242 := by rfl
theorem normalized121 : AdaptiveCoverage.normalize SL cell241 = normal231 := by
  calc
    AdaptiveCoverage.normalize SL cell241 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell241)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell241)).symm
    _ = normal231 := by rfl
theorem left121 : leftChild 9 PR SL normal231 0 9 335872 = cell243 := by
  calc
    leftChild 9 PR SL normal231 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal231) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal231) 0 9 335872).symm
    _ = cell243 := by rfl
theorem right121 : rightChild 9 PR SL normal231 0 9 335872 = cell244 := by
  calc
    rightChild 9 PR SL normal231 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal231) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal231) 0 9 335872).symm
    _ = cell244 := by rfl
theorem normalized122 : AdaptiveCoverage.normalize SL cell243 = normal232 := by
  calc
    AdaptiveCoverage.normalize SL cell243 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell243)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell243)).symm
    _ = normal232 := by rfl
theorem left122 : leftChild 9 PR SL normal232 4 7 114688 = cell245 := by
  calc
    leftChild 9 PR SL normal232 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal232) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal232) 4 7 114688).symm
    _ = cell245 := by rfl
theorem right122 : rightChild 9 PR SL normal232 4 7 114688 = cell246 := by
  calc
    rightChild 9 PR SL normal232 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal232) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal232) 4 7 114688).symm
    _ = cell246 := by rfl
theorem normalized123 : AdaptiveCoverage.normalize SL cell246 = normal234 := by
  calc
    AdaptiveCoverage.normalize SL cell246 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell246)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell246)).symm
    _ = normal234 := by rfl
theorem left123 : leftChild 9 PR SL normal234 5 7 81920 = cell247 := by
  calc
    leftChild 9 PR SL normal234 5 7 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal234) 5 7 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal234) 5 7 81920).symm
    _ = cell247 := by rfl
theorem right123 : rightChild 9 PR SL normal234 5 7 81920 = cell248 := by
  calc
    rightChild 9 PR SL normal234 5 7 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal234) 5 7 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal234) 5 7 81920).symm
    _ = cell248 := by rfl
theorem normalized124 : AdaptiveCoverage.normalize SL cell242 = normal238 := by
  calc
    AdaptiveCoverage.normalize SL cell242 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell242)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell242)).symm
    _ = normal238 := by rfl
theorem left124 : leftChild 9 PR SL normal238 0 9 335872 = cell249 := by
  calc
    leftChild 9 PR SL normal238 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal238) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal238) 0 9 335872).symm
    _ = cell249 := by rfl
theorem right124 : rightChild 9 PR SL normal238 0 9 335872 = cell250 := by
  calc
    rightChild 9 PR SL normal238 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal238) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal238) 0 9 335872).symm
    _ = cell250 := by rfl
theorem normalized125 : AdaptiveCoverage.normalize SL cell249 = normal239 := by
  calc
    AdaptiveCoverage.normalize SL cell249 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell249)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell249)).symm
    _ = normal239 := by rfl
theorem left125 : leftChild 9 PR SL normal239 4 7 114688 = cell251 := by
  calc
    leftChild 9 PR SL normal239 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal239) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal239) 4 7 114688).symm
    _ = cell251 := by rfl
theorem right125 : rightChild 9 PR SL normal239 4 7 114688 = cell252 := by
  calc
    rightChild 9 PR SL normal239 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal239) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal239) 4 7 114688).symm
    _ = cell252 := by rfl
theorem normalized126 : AdaptiveCoverage.normalize SL cell252 = normal241 := by
  calc
    AdaptiveCoverage.normalize SL cell252 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell252)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell252)).symm
    _ = normal241 := by rfl
theorem left126 : leftChild 9 PR SL normal241 5 7 81920 = cell253 := by
  calc
    leftChild 9 PR SL normal241 5 7 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal241) 5 7 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal241) 5 7 81920).symm
    _ = cell253 := by rfl
theorem right126 : rightChild 9 PR SL normal241 5 7 81920 = cell254 := by
  calc
    rightChild 9 PR SL normal241 5 7 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal241) 5 7 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal241) 5 7 81920).symm
    _ = cell254 := by rfl
theorem normalized127 : AdaptiveCoverage.normalize SL cell240 = normal245 := by
  calc
    AdaptiveCoverage.normalize SL cell240 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell240)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell240)).symm
    _ = normal245 := by rfl
theorem left127 : leftChild 9 PR SL normal245 0 9 335872 = cell255 := by
  calc
    leftChild 9 PR SL normal245 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal245) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal245) 0 9 335872).symm
    _ = cell255 := by rfl
theorem right127 : rightChild 9 PR SL normal245 0 9 335872 = cell256 := by
  calc
    rightChild 9 PR SL normal245 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal245) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal245) 0 9 335872).symm
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
end StructuralGoal20261016.W10Aux478
end
