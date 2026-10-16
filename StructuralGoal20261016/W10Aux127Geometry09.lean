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
theorem normalized072 : AdaptiveCoverage.normalize SL cell143 = normal136 := by
  calc
    AdaptiveCoverage.normalize SL cell143 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell143)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell143)).symm
    _ = normal136 := by rfl
theorem left072 : leftChild 9 PR SL normal136 0 8 278528 = cell145 := by
  calc
    leftChild 9 PR SL normal136 0 8 278528 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal136) 0 8 278528).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal136) 0 8 278528).symm
    _ = cell145 := by rfl
theorem right072 : rightChild 9 PR SL normal136 0 8 278528 = cell146 := by
  calc
    rightChild 9 PR SL normal136 0 8 278528 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal136) 0 8 278528).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal136) 0 8 278528).symm
    _ = cell146 := by rfl
theorem normalized073 : AdaptiveCoverage.normalize SL cell146 = normal138 := by
  calc
    AdaptiveCoverage.normalize SL cell146 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell146)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell146)).symm
    _ = normal138 := by rfl
theorem left073 : leftChild 9 PR SL normal138 1 9 278528 = cell147 := by
  calc
    leftChild 9 PR SL normal138 1 9 278528 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal138) 1 9 278528).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal138) 1 9 278528).symm
    _ = cell147 := by rfl
theorem right073 : rightChild 9 PR SL normal138 1 9 278528 = cell148 := by
  calc
    rightChild 9 PR SL normal138 1 9 278528 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal138) 1 9 278528).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal138) 1 9 278528).symm
    _ = cell148 := by rfl
theorem normalized074 : AdaptiveCoverage.normalize SL cell148 = normal140 := by
  calc
    AdaptiveCoverage.normalize SL cell148 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell148)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell148)).symm
    _ = normal140 := by rfl
theorem left074 : leftChild 9 PR SL normal140 3 7 163840 = cell149 := by
  calc
    leftChild 9 PR SL normal140 3 7 163840 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal140) 3 7 163840).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal140) 3 7 163840).symm
    _ = cell149 := by rfl
theorem right074 : rightChild 9 PR SL normal140 3 7 163840 = cell150 := by
  calc
    rightChild 9 PR SL normal140 3 7 163840 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal140) 3 7 163840).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal140) 3 7 163840).symm
    _ = cell150 := by rfl
theorem normalized075 : AdaptiveCoverage.normalize SL cell149 = normal141 := by
  calc
    AdaptiveCoverage.normalize SL cell149 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell149)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell149)).symm
    _ = normal141 := by rfl
theorem left075 : leftChild 9 PR SL normal141 2 6 163840 = cell151 := by
  calc
    leftChild 9 PR SL normal141 2 6 163840 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal141) 2 6 163840).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal141) 2 6 163840).symm
    _ = cell151 := by rfl
theorem right075 : rightChild 9 PR SL normal141 2 6 163840 = cell152 := by
  calc
    rightChild 9 PR SL normal141 2 6 163840 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal141) 2 6 163840).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal141) 2 6 163840).symm
    _ = cell152 := by rfl
theorem normalized076 : AdaptiveCoverage.normalize SL cell151 = normal142 := by
  calc
    AdaptiveCoverage.normalize SL cell151 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell151)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell151)).symm
    _ = normal142 := by rfl
theorem left076 : leftChild 9 PR SL normal142 0 9 319488 = cell153 := by
  calc
    leftChild 9 PR SL normal142 0 9 319488 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal142) 0 9 319488).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal142) 0 9 319488).symm
    _ = cell153 := by rfl
theorem right076 : rightChild 9 PR SL normal142 0 9 319488 = cell154 := by
  calc
    rightChild 9 PR SL normal142 0 9 319488 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal142) 0 9 319488).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal142) 0 9 319488).symm
    _ = cell154 := by rfl
theorem normalized077 : AdaptiveCoverage.normalize SL cell154 = normal144 := by
  calc
    AdaptiveCoverage.normalize SL cell154 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell154)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell154)).symm
    _ = normal144 := by rfl
theorem left077 : leftChild 9 PR SL normal144 1 8 245760 = cell155 := by
  calc
    leftChild 9 PR SL normal144 1 8 245760 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal144) 1 8 245760).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal144) 1 8 245760).symm
    _ = cell155 := by rfl
theorem right077 : rightChild 9 PR SL normal144 1 8 245760 = cell156 := by
  calc
    rightChild 9 PR SL normal144 1 8 245760 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal144) 1 8 245760).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal144) 1 8 245760).symm
    _ = cell156 := by rfl
theorem normalized078 : AdaptiveCoverage.normalize SL cell156 = normal146 := by
  calc
    AdaptiveCoverage.normalize SL cell156 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell156)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell156)).symm
    _ = normal146 := by rfl
theorem left078 : leftChild 9 PR SL normal146 4 6 81920 = cell157 := by
  calc
    leftChild 9 PR SL normal146 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal146) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal146) 4 6 81920).symm
    _ = cell157 := by rfl
theorem right078 : rightChild 9 PR SL normal146 4 6 81920 = cell158 := by
  calc
    rightChild 9 PR SL normal146 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal146) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal146) 4 6 81920).symm
    _ = cell158 := by rfl
theorem normalized079 : AdaptiveCoverage.normalize SL cell158 = normal148 := by
  calc
    AdaptiveCoverage.normalize SL cell158 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell158)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell158)).symm
    _ = normal148 := by rfl
theorem left079 : leftChild 9 PR SL normal148 0 6 229376 = cell159 := by
  calc
    leftChild 9 PR SL normal148 0 6 229376 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal148) 0 6 229376).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal148) 0 6 229376).symm
    _ = cell159 := by rfl
theorem right079 : rightChild 9 PR SL normal148 0 6 229376 = cell160 := by
  calc
    rightChild 9 PR SL normal148 0 6 229376 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal148) 0 6 229376).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal148) 0 6 229376).symm
    _ = cell160 := by rfl

set_option pp.fullNames true
#print axioms normalized072
#print axioms left072
#print axioms right072
#print axioms normalized073
#print axioms left073
#print axioms right073
#print axioms normalized074
#print axioms left074
#print axioms right074
#print axioms normalized075
#print axioms left075
#print axioms right075
#print axioms normalized076
#print axioms left076
#print axioms right076
#print axioms normalized077
#print axioms left077
#print axioms right077
#print axioms normalized078
#print axioms left078
#print axioms right078
#print axioms normalized079
#print axioms left079
#print axioms right079
end StructuralGoal20261016.W10Aux127
end
