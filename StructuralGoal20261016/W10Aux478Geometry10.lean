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
theorem normalized080 : AdaptiveCoverage.normalize SL cell096 = normal151 := by
  calc
    AdaptiveCoverage.normalize SL cell096 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell096)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell096)).symm
    _ = normal151 := by rfl
theorem left080 : leftChild 9 PR SL normal151 2 6 131072 = cell161 := by
  calc
    leftChild 9 PR SL normal151 2 6 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal151) 2 6 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal151) 2 6 131072).symm
    _ = cell161 := by rfl
theorem right080 : rightChild 9 PR SL normal151 2 6 131072 = cell162 := by
  calc
    rightChild 9 PR SL normal151 2 6 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal151) 2 6 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal151) 2 6 131072).symm
    _ = cell162 := by rfl
theorem normalized081 : AdaptiveCoverage.normalize SL cell162 = normal153 := by
  calc
    AdaptiveCoverage.normalize SL cell162 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell162)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell162)).symm
    _ = normal153 := by rfl
theorem left081 : leftChild 9 PR SL normal153 0 8 294912 = cell163 := by
  calc
    leftChild 9 PR SL normal153 0 8 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal153) 0 8 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal153) 0 8 294912).symm
    _ = cell163 := by rfl
theorem right081 : rightChild 9 PR SL normal153 0 8 294912 = cell164 := by
  calc
    rightChild 9 PR SL normal153 0 8 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal153) 0 8 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal153) 0 8 294912).symm
    _ = cell164 := by rfl
theorem normalized082 : AdaptiveCoverage.normalize SL cell163 = normal154 := by
  calc
    AdaptiveCoverage.normalize SL cell163 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell163)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell163)).symm
    _ = normal154 := by rfl
theorem left082 : leftChild 9 PR SL normal154 3 5 81920 = cell165 := by
  calc
    leftChild 9 PR SL normal154 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal154) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal154) 3 5 81920).symm
    _ = cell165 := by rfl
theorem right082 : rightChild 9 PR SL normal154 3 5 81920 = cell166 := by
  calc
    rightChild 9 PR SL normal154 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal154) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal154) 3 5 81920).symm
    _ = cell166 := by rfl
theorem normalized083 : AdaptiveCoverage.normalize SL cell165 = normal155 := by
  calc
    AdaptiveCoverage.normalize SL cell165 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell165)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell165)).symm
    _ = normal155 := by rfl
theorem left083 : leftChild 9 PR SL normal155 4 6 81920 = cell167 := by
  calc
    leftChild 9 PR SL normal155 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal155) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal155) 4 6 81920).symm
    _ = cell167 := by rfl
theorem right083 : rightChild 9 PR SL normal155 4 6 81920 = cell168 := by
  calc
    rightChild 9 PR SL normal155 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal155) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal155) 4 6 81920).symm
    _ = cell168 := by rfl
theorem normalized084 : AdaptiveCoverage.normalize SL cell167 = normal156 := by
  calc
    AdaptiveCoverage.normalize SL cell167 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell167)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell167)).symm
    _ = normal156 := by rfl
theorem left084 : leftChild 9 PR SL normal156 4 7 114688 = cell169 := by
  calc
    leftChild 9 PR SL normal156 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal156) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal156) 4 7 114688).symm
    _ = cell169 := by rfl
theorem right084 : rightChild 9 PR SL normal156 4 7 114688 = cell170 := by
  calc
    rightChild 9 PR SL normal156 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal156) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal156) 4 7 114688).symm
    _ = cell170 := by rfl
theorem normalized085 : AdaptiveCoverage.normalize SL cell169 = normal157 := by
  calc
    AdaptiveCoverage.normalize SL cell169 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell169)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell169)).symm
    _ = normal157 := by rfl
theorem left085 : leftChild 9 PR SL normal157 0 9 335872 = cell171 := by
  calc
    leftChild 9 PR SL normal157 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal157) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal157) 0 9 335872).symm
    _ = cell171 := by rfl
theorem right085 : rightChild 9 PR SL normal157 0 9 335872 = cell172 := by
  calc
    rightChild 9 PR SL normal157 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal157) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal157) 0 9 335872).symm
    _ = cell172 := by rfl
theorem normalized086 : AdaptiveCoverage.normalize SL cell171 = normal158 := by
  calc
    AdaptiveCoverage.normalize SL cell171 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell171)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell171)).symm
    _ = normal158 := by rfl
theorem left086 : leftChild 9 PR SL normal158 3 7 147456 = cell173 := by
  calc
    leftChild 9 PR SL normal158 3 7 147456 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal158) 3 7 147456).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal158) 3 7 147456).symm
    _ = cell173 := by rfl
theorem right086 : rightChild 9 PR SL normal158 3 7 147456 = cell174 := by
  calc
    rightChild 9 PR SL normal158 3 7 147456 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal158) 3 7 147456).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal158) 3 7 147456).symm
    _ = cell174 := by rfl
theorem normalized087 : AdaptiveCoverage.normalize SL cell164 = normal165 := by
  calc
    AdaptiveCoverage.normalize SL cell164 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell164)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell164)).symm
    _ = normal165 := by rfl
theorem left087 : leftChild 9 PR SL normal165 1 9 294912 = cell175 := by
  calc
    leftChild 9 PR SL normal165 1 9 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal165) 1 9 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal165) 1 9 294912).symm
    _ = cell175 := by rfl
theorem right087 : rightChild 9 PR SL normal165 1 9 294912 = cell176 := by
  calc
    rightChild 9 PR SL normal165 1 9 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal165) 1 9 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal165) 1 9 294912).symm
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
end StructuralGoal20261016.W10Aux478
end
