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
theorem normalized080 : AdaptiveCoverage.normalize SL cell150 = normal152 := by
  calc
    AdaptiveCoverage.normalize SL cell150 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell150)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell150)).symm
    _ = normal152 := by rfl
theorem left080 : leftChild 9 PR SL normal152 2 6 163840 = cell161 := by
  calc
    leftChild 9 PR SL normal152 2 6 163840 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal152) 2 6 163840).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal152) 2 6 163840).symm
    _ = cell161 := by rfl
theorem right080 : rightChild 9 PR SL normal152 2 6 163840 = cell162 := by
  calc
    rightChild 9 PR SL normal152 2 6 163840 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal152) 2 6 163840).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal152) 2 6 163840).symm
    _ = cell162 := by rfl
theorem normalized081 : AdaptiveCoverage.normalize SL cell161 = normal153 := by
  calc
    AdaptiveCoverage.normalize SL cell161 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell161)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell161)).symm
    _ = normal153 := by rfl
theorem left081 : leftChild 9 PR SL normal153 0 9 319488 = cell163 := by
  calc
    leftChild 9 PR SL normal153 0 9 319488 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal153) 0 9 319488).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal153) 0 9 319488).symm
    _ = cell163 := by rfl
theorem right081 : rightChild 9 PR SL normal153 0 9 319488 = cell164 := by
  calc
    rightChild 9 PR SL normal153 0 9 319488 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal153) 0 9 319488).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal153) 0 9 319488).symm
    _ = cell164 := by rfl
theorem normalized082 : AdaptiveCoverage.normalize SL cell164 = normal155 := by
  calc
    AdaptiveCoverage.normalize SL cell164 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell164)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell164)).symm
    _ = normal155 := by rfl
theorem left082 : leftChild 9 PR SL normal155 4 6 81920 = cell165 := by
  calc
    leftChild 9 PR SL normal155 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal155) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal155) 4 6 81920).symm
    _ = cell165 := by rfl
theorem right082 : rightChild 9 PR SL normal155 4 6 81920 = cell166 := by
  calc
    rightChild 9 PR SL normal155 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal155) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal155) 4 6 81920).symm
    _ = cell166 := by rfl
theorem normalized083 : AdaptiveCoverage.normalize SL cell142 = normal160 := by
  calc
    AdaptiveCoverage.normalize SL cell142 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell142)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell142)).symm
    _ = normal160 := by rfl
theorem left083 : leftChild 9 PR SL normal160 4 7 114688 = cell167 := by
  calc
    leftChild 9 PR SL normal160 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal160) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal160) 4 7 114688).symm
    _ = cell167 := by rfl
theorem right083 : rightChild 9 PR SL normal160 4 7 114688 = cell168 := by
  calc
    rightChild 9 PR SL normal160 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal160) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal160) 4 7 114688).symm
    _ = cell168 := by rfl
theorem normalized084 : AdaptiveCoverage.normalize SL cell167 = normal161 := by
  calc
    AdaptiveCoverage.normalize SL cell167 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell167)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell167)).symm
    _ = normal161 := by rfl
theorem left084 : leftChild 9 PR SL normal161 2 4 98304 = cell169 := by
  calc
    leftChild 9 PR SL normal161 2 4 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal161) 2 4 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal161) 2 4 98304).symm
    _ = cell169 := by rfl
theorem right084 : rightChild 9 PR SL normal161 2 4 98304 = cell170 := by
  calc
    rightChild 9 PR SL normal161 2 4 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal161) 2 4 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal161) 2 4 98304).symm
    _ = cell170 := by rfl
theorem normalized085 : AdaptiveCoverage.normalize SL cell169 = normal162 := by
  calc
    AdaptiveCoverage.normalize SL cell169 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell169)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell169)).symm
    _ = normal162 := by rfl
theorem left085 : leftChild 9 PR SL normal162 0 8 278528 = cell171 := by
  calc
    leftChild 9 PR SL normal162 0 8 278528 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal162) 0 8 278528).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal162) 0 8 278528).symm
    _ = cell171 := by rfl
theorem right085 : rightChild 9 PR SL normal162 0 8 278528 = cell172 := by
  calc
    rightChild 9 PR SL normal162 0 8 278528 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal162) 0 8 278528).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal162) 0 8 278528).symm
    _ = cell172 := by rfl
theorem normalized086 : AdaptiveCoverage.normalize SL cell172 = normal164 := by
  calc
    AdaptiveCoverage.normalize SL cell172 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell172)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell172)).symm
    _ = normal164 := by rfl
theorem left086 : leftChild 9 PR SL normal164 1 9 278528 = cell173 := by
  calc
    leftChild 9 PR SL normal164 1 9 278528 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal164) 1 9 278528).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal164) 1 9 278528).symm
    _ = cell173 := by rfl
theorem right086 : rightChild 9 PR SL normal164 1 9 278528 = cell174 := by
  calc
    rightChild 9 PR SL normal164 1 9 278528 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal164) 1 9 278528).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal164) 1 9 278528).symm
    _ = cell174 := by rfl
theorem normalized087 : AdaptiveCoverage.normalize SL cell174 = normal166 := by
  calc
    AdaptiveCoverage.normalize SL cell174 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell174)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell174)).symm
    _ = normal166 := by rfl
theorem left087 : leftChild 9 PR SL normal166 2 6 163840 = cell175 := by
  calc
    leftChild 9 PR SL normal166 2 6 163840 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal166) 2 6 163840).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal166) 2 6 163840).symm
    _ = cell175 := by rfl
theorem right087 : rightChild 9 PR SL normal166 2 6 163840 = cell176 := by
  calc
    rightChild 9 PR SL normal166 2 6 163840 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal166) 2 6 163840).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal166) 2 6 163840).symm
    _ = cell176 := by rfl

set_option pp.fullNames true
#print axioms normalized080
#print axioms left080
#print axioms right080
#print axioms normalized081
#print axioms left081
#print axioms right081
#print axioms normalized082
#print axioms left082
#print axioms right082
#print axioms normalized083
#print axioms left083
#print axioms right083
#print axioms normalized084
#print axioms left084
#print axioms right084
#print axioms normalized085
#print axioms left085
#print axioms right085
#print axioms normalized086
#print axioms left086
#print axioms right086
#print axioms normalized087
#print axioms left087
#print axioms right087
end StructuralGoal20261016.W10Aux127
end
