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
theorem normalized112 : AdaptiveCoverage.normalize SL cell224 = normal213 := by
  calc
    AdaptiveCoverage.normalize SL cell224 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell224)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell224)).symm
    _ = normal213 := by rfl
theorem left112 : leftChild 9 PR SL normal213 5 7 81920 = cell225 := by
  calc
    leftChild 9 PR SL normal213 5 7 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal213) 5 7 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal213) 5 7 81920).symm
    _ = cell225 := by rfl
theorem right112 : rightChild 9 PR SL normal213 5 7 81920 = cell226 := by
  calc
    rightChild 9 PR SL normal213 5 7 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal213) 5 7 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal213) 5 7 81920).symm
    _ = cell226 := by rfl
theorem normalized113 : AdaptiveCoverage.normalize SL cell182 = normal217 := by
  calc
    AdaptiveCoverage.normalize SL cell182 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell182)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell182)).symm
    _ = normal217 := by rfl
theorem left113 : leftChild 9 PR SL normal217 0 8 294912 = cell227 := by
  calc
    leftChild 9 PR SL normal217 0 8 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal217) 0 8 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal217) 0 8 294912).symm
    _ = cell227 := by rfl
theorem right113 : rightChild 9 PR SL normal217 0 8 294912 = cell228 := by
  calc
    rightChild 9 PR SL normal217 0 8 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal217) 0 8 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal217) 0 8 294912).symm
    _ = cell228 := by rfl
theorem normalized114 : AdaptiveCoverage.normalize SL cell227 = normal218 := by
  calc
    AdaptiveCoverage.normalize SL cell227 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell227)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell227)).symm
    _ = normal218 := by rfl
theorem left114 : leftChild 9 PR SL normal218 2 6 131072 = cell229 := by
  calc
    leftChild 9 PR SL normal218 2 6 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal218) 2 6 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal218) 2 6 131072).symm
    _ = cell229 := by rfl
theorem right114 : rightChild 9 PR SL normal218 2 6 131072 = cell230 := by
  calc
    rightChild 9 PR SL normal218 2 6 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal218) 2 6 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal218) 2 6 131072).symm
    _ = cell230 := by rfl
theorem normalized115 : AdaptiveCoverage.normalize SL cell230 = normal220 := by
  calc
    AdaptiveCoverage.normalize SL cell230 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell230)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell230)).symm
    _ = normal220 := by rfl
theorem left115 : leftChild 9 PR SL normal220 0 9 335872 = cell231 := by
  calc
    leftChild 9 PR SL normal220 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal220) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal220) 0 9 335872).symm
    _ = cell231 := by rfl
theorem right115 : rightChild 9 PR SL normal220 0 9 335872 = cell232 := by
  calc
    rightChild 9 PR SL normal220 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal220) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal220) 0 9 335872).symm
    _ = cell232 := by rfl
theorem normalized116 : AdaptiveCoverage.normalize SL cell231 = normal221 := by
  calc
    AdaptiveCoverage.normalize SL cell231 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell231)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell231)).symm
    _ = normal221 := by rfl
theorem left116 : leftChild 9 PR SL normal221 4 7 114688 = cell233 := by
  calc
    leftChild 9 PR SL normal221 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal221) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal221) 4 7 114688).symm
    _ = cell233 := by rfl
theorem right116 : rightChild 9 PR SL normal221 4 7 114688 = cell234 := by
  calc
    rightChild 9 PR SL normal221 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal221) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal221) 4 7 114688).symm
    _ = cell234 := by rfl
theorem normalized117 : AdaptiveCoverage.normalize SL cell234 = normal223 := by
  calc
    AdaptiveCoverage.normalize SL cell234 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell234)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell234)).symm
    _ = normal223 := by rfl
theorem left117 : leftChild 9 PR SL normal223 5 7 81920 = cell235 := by
  calc
    leftChild 9 PR SL normal223 5 7 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal223) 5 7 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal223) 5 7 81920).symm
    _ = cell235 := by rfl
theorem right117 : rightChild 9 PR SL normal223 5 7 81920 = cell236 := by
  calc
    rightChild 9 PR SL normal223 5 7 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal223) 5 7 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal223) 5 7 81920).symm
    _ = cell236 := by rfl
theorem normalized118 : AdaptiveCoverage.normalize SL cell228 = normal227 := by
  calc
    AdaptiveCoverage.normalize SL cell228 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell228)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell228)).symm
    _ = normal227 := by rfl
theorem left118 : leftChild 9 PR SL normal227 2 6 131072 = cell237 := by
  calc
    leftChild 9 PR SL normal227 2 6 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal227) 2 6 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal227) 2 6 131072).symm
    _ = cell237 := by rfl
theorem right118 : rightChild 9 PR SL normal227 2 6 131072 = cell238 := by
  calc
    rightChild 9 PR SL normal227 2 6 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal227) 2 6 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal227) 2 6 131072).symm
    _ = cell238 := by rfl
theorem normalized119 : AdaptiveCoverage.normalize SL cell238 = normal229 := by
  calc
    AdaptiveCoverage.normalize SL cell238 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell238)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell238)).symm
    _ = normal229 := by rfl
theorem left119 : leftChild 9 PR SL normal229 2 7 196608 = cell239 := by
  calc
    leftChild 9 PR SL normal229 2 7 196608 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal229) 2 7 196608).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal229) 2 7 196608).symm
    _ = cell239 := by rfl
theorem right119 : rightChild 9 PR SL normal229 2 7 196608 = cell240 := by
  calc
    rightChild 9 PR SL normal229 2 7 196608 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal229) 2 7 196608).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal229) 2 7 196608).symm
    _ = cell240 := by rfl

set_option pp.fullNames true
#print axioms normalized112
#print axioms left112
#print axioms right112
#print axioms normalized113
#print axioms left113
#print axioms right113
#print axioms normalized114
#print axioms left114
#print axioms right114
#print axioms normalized115
#print axioms left115
#print axioms right115
#print axioms normalized116
#print axioms left116
#print axioms right116
#print axioms normalized117
#print axioms left117
#print axioms right117
#print axioms normalized118
#print axioms left118
#print axioms right118
#print axioms normalized119
#print axioms left119
#print axioms right119
end StructuralGoal20261016.W10Aux478
end
