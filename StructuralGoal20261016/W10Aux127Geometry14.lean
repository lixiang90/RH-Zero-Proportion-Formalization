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
theorem normalized112 : AdaptiveCoverage.normalize SL cell224 = normal215 := by
  calc
    AdaptiveCoverage.normalize SL cell224 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell224)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell224)).symm
    _ = normal215 := by rfl
theorem left112 : leftChild 9 PR SL normal215 4 5 49152 = cell225 := by
  calc
    leftChild 9 PR SL normal215 4 5 49152 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal215) 4 5 49152).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal215) 4 5 49152).symm
    _ = cell225 := by rfl
theorem right112 : rightChild 9 PR SL normal215 4 5 49152 = cell226 := by
  calc
    rightChild 9 PR SL normal215 4 5 49152 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal215) 4 5 49152).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal215) 4 5 49152).symm
    _ = cell226 := by rfl
theorem normalized113 : AdaptiveCoverage.normalize SL cell222 = normal218 := by
  calc
    AdaptiveCoverage.normalize SL cell222 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell222)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell222)).symm
    _ = normal218 := by rfl
theorem left113 : leftChild 9 PR SL normal218 4 5 49152 = cell227 := by
  calc
    leftChild 9 PR SL normal218 4 5 49152 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal218) 4 5 49152).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal218) 4 5 49152).symm
    _ = cell227 := by rfl
theorem right113 : rightChild 9 PR SL normal218 4 5 49152 = cell228 := by
  calc
    rightChild 9 PR SL normal218 4 5 49152 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal218) 4 5 49152).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal218) 4 5 49152).symm
    _ = cell228 := by rfl
theorem normalized114 : AdaptiveCoverage.normalize SL cell216 = normal221 := by
  calc
    AdaptiveCoverage.normalize SL cell216 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell216)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell216)).symm
    _ = normal221 := by rfl
theorem left114 : leftChild 9 PR SL normal221 4 6 81920 = cell229 := by
  calc
    leftChild 9 PR SL normal221 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal221) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal221) 4 6 81920).symm
    _ = cell229 := by rfl
theorem right114 : rightChild 9 PR SL normal221 4 6 81920 = cell230 := by
  calc
    rightChild 9 PR SL normal221 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal221) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal221) 4 6 81920).symm
    _ = cell230 := by rfl
theorem normalized115 : AdaptiveCoverage.normalize SL cell230 = normal223 := by
  calc
    AdaptiveCoverage.normalize SL cell230 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell230)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell230)).symm
    _ = normal223 := by rfl
theorem left115 : leftChild 9 PR SL normal223 0 9 319488 = cell231 := by
  calc
    leftChild 9 PR SL normal223 0 9 319488 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal223) 0 9 319488).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal223) 0 9 319488).symm
    _ = cell231 := by rfl
theorem right115 : rightChild 9 PR SL normal223 0 9 319488 = cell232 := by
  calc
    rightChild 9 PR SL normal223 0 9 319488 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal223) 0 9 319488).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal223) 0 9 319488).symm
    _ = cell232 := by rfl
theorem normalized116 : AdaptiveCoverage.normalize SL cell232 = normal225 := by
  calc
    AdaptiveCoverage.normalize SL cell232 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell232)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell232)).symm
    _ = normal225 := by rfl
theorem left116 : leftChild 9 PR SL normal225 4 7 131072 = cell233 := by
  calc
    leftChild 9 PR SL normal225 4 7 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal225) 4 7 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal225) 4 7 131072).symm
    _ = cell233 := by rfl
theorem right116 : rightChild 9 PR SL normal225 4 7 131072 = cell234 := by
  calc
    rightChild 9 PR SL normal225 4 7 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal225) 4 7 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal225) 4 7 131072).symm
    _ = cell234 := by rfl
theorem normalized117 : AdaptiveCoverage.normalize SL cell233 = normal226 := by
  calc
    AdaptiveCoverage.normalize SL cell233 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell233)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell233)).symm
    _ = normal226 := by rfl
theorem left117 : leftChild 9 PR SL normal226 0 6 229376 = cell235 := by
  calc
    leftChild 9 PR SL normal226 0 6 229376 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal226) 0 6 229376).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal226) 0 6 229376).symm
    _ = cell235 := by rfl
theorem right117 : rightChild 9 PR SL normal226 0 6 229376 = cell236 := by
  calc
    rightChild 9 PR SL normal226 0 6 229376 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal226) 0 6 229376).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal226) 0 6 229376).symm
    _ = cell236 := by rfl
theorem normalized118 : AdaptiveCoverage.normalize SL cell235 = normal227 := by
  calc
    AdaptiveCoverage.normalize SL cell235 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell235)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell235)).symm
    _ = normal227 := by rfl
theorem left118 : leftChild 9 PR SL normal227 3 5 81920 = cell237 := by
  calc
    leftChild 9 PR SL normal227 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal227) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal227) 3 5 81920).symm
    _ = cell237 := by rfl
theorem right118 : rightChild 9 PR SL normal227 3 5 81920 = cell238 := by
  calc
    rightChild 9 PR SL normal227 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal227) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal227) 3 5 81920).symm
    _ = cell238 := by rfl
theorem normalized119 : AdaptiveCoverage.normalize SL cell214 = normal232 := by
  calc
    AdaptiveCoverage.normalize SL cell214 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell214)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell214)).symm
    _ = normal232 := by rfl
theorem left119 : leftChild 9 PR SL normal232 3 7 163840 = cell239 := by
  calc
    leftChild 9 PR SL normal232 3 7 163840 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal232) 3 7 163840).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal232) 3 7 163840).symm
    _ = cell239 := by rfl
theorem right119 : rightChild 9 PR SL normal232 3 7 163840 = cell240 := by
  calc
    rightChild 9 PR SL normal232 3 7 163840 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal232) 3 7 163840).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal232) 3 7 163840).symm
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
end StructuralGoal20261016.W10Aux127
end
