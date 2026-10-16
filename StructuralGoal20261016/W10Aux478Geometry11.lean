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
theorem normalized088 : AdaptiveCoverage.normalize SL cell176 = normal167 := by
  calc
    AdaptiveCoverage.normalize SL cell176 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell176)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell176)).symm
    _ = normal167 := by rfl
theorem left088 : leftChild 9 PR SL normal167 3 5 81920 = cell177 := by
  calc
    leftChild 9 PR SL normal167 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal167) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal167) 3 5 81920).symm
    _ = cell177 := by rfl
theorem right088 : rightChild 9 PR SL normal167 3 5 81920 = cell178 := by
  calc
    rightChild 9 PR SL normal167 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal167) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal167) 3 5 81920).symm
    _ = cell178 := by rfl
theorem normalized089 : AdaptiveCoverage.normalize SL cell094 = normal170 := by
  calc
    AdaptiveCoverage.normalize SL cell094 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell094)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell094)).symm
    _ = normal170 := by rfl
theorem left089 : leftChild 9 PR SL normal170 3 9 229376 = cell179 := by
  calc
    leftChild 9 PR SL normal170 3 9 229376 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal170) 3 9 229376).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal170) 3 9 229376).symm
    _ = cell179 := by rfl
theorem right089 : rightChild 9 PR SL normal170 3 9 229376 = cell180 := by
  calc
    rightChild 9 PR SL normal170 3 9 229376 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal170) 3 9 229376).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal170) 3 9 229376).symm
    _ = cell180 := by rfl
theorem normalized090 : AdaptiveCoverage.normalize SL cell179 = normal171 := by
  calc
    AdaptiveCoverage.normalize SL cell179 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell179)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell179)).symm
    _ = normal171 := by rfl
theorem left090 : leftChild 9 PR SL normal171 2 9 262144 = cell181 := by
  calc
    leftChild 9 PR SL normal171 2 9 262144 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal171) 2 9 262144).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal171) 2 9 262144).symm
    _ = cell181 := by rfl
theorem right090 : rightChild 9 PR SL normal171 2 9 262144 = cell182 := by
  calc
    rightChild 9 PR SL normal171 2 9 262144 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal171) 2 9 262144).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal171) 2 9 262144).symm
    _ = cell182 := by rfl
theorem normalized091 : AdaptiveCoverage.normalize SL cell181 = normal172 := by
  calc
    AdaptiveCoverage.normalize SL cell181 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell181)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell181)).symm
    _ = normal172 := by rfl
theorem left091 : leftChild 9 PR SL normal172 0 8 294912 = cell183 := by
  calc
    leftChild 9 PR SL normal172 0 8 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal172) 0 8 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal172) 0 8 294912).symm
    _ = cell183 := by rfl
theorem right091 : rightChild 9 PR SL normal172 0 8 294912 = cell184 := by
  calc
    rightChild 9 PR SL normal172 0 8 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal172) 0 8 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal172) 0 8 294912).symm
    _ = cell184 := by rfl
theorem normalized092 : AdaptiveCoverage.normalize SL cell183 = normal173 := by
  calc
    AdaptiveCoverage.normalize SL cell183 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell183)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell183)).symm
    _ = normal173 := by rfl
theorem left092 : leftChild 9 PR SL normal173 1 9 294912 = cell185 := by
  calc
    leftChild 9 PR SL normal173 1 9 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal173) 1 9 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal173) 1 9 294912).symm
    _ = cell185 := by rfl
theorem right092 : rightChild 9 PR SL normal173 1 9 294912 = cell186 := by
  calc
    rightChild 9 PR SL normal173 1 9 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal173) 1 9 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal173) 1 9 294912).symm
    _ = cell186 := by rfl
theorem normalized093 : AdaptiveCoverage.normalize SL cell185 = normal174 := by
  calc
    AdaptiveCoverage.normalize SL cell185 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell185)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell185)).symm
    _ = normal174 := by rfl
theorem left093 : leftChild 9 PR SL normal174 0 9 335872 = cell187 := by
  calc
    leftChild 9 PR SL normal174 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal174) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal174) 0 9 335872).symm
    _ = cell187 := by rfl
theorem right093 : rightChild 9 PR SL normal174 0 9 335872 = cell188 := by
  calc
    rightChild 9 PR SL normal174 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal174) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal174) 0 9 335872).symm
    _ = cell188 := by rfl
theorem normalized094 : AdaptiveCoverage.normalize SL cell187 = normal175 := by
  calc
    AdaptiveCoverage.normalize SL cell187 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell187)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell187)).symm
    _ = normal175 := by rfl
theorem left094 : leftChild 9 PR SL normal175 2 6 131072 = cell189 := by
  calc
    leftChild 9 PR SL normal175 2 6 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal175) 2 6 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal175) 2 6 131072).symm
    _ = cell189 := by rfl
theorem right094 : rightChild 9 PR SL normal175 2 6 131072 = cell190 := by
  calc
    rightChild 9 PR SL normal175 2 6 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal175) 2 6 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal175) 2 6 131072).symm
    _ = cell190 := by rfl
theorem normalized095 : AdaptiveCoverage.normalize SL cell190 = normal177 := by
  calc
    AdaptiveCoverage.normalize SL cell190 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell190)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell190)).symm
    _ = normal177 := by rfl
theorem left095 : leftChild 9 PR SL normal177 4 7 114688 = cell191 := by
  calc
    leftChild 9 PR SL normal177 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal177) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal177) 4 7 114688).symm
    _ = cell191 := by rfl
theorem right095 : rightChild 9 PR SL normal177 4 7 114688 = cell192 := by
  calc
    rightChild 9 PR SL normal177 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal177) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal177) 4 7 114688).symm
    _ = cell192 := by rfl

set_option pp.fullNames true
#print axioms normalized088
#print axioms left088
#print axioms right088
#print axioms normalized089
#print axioms left089
#print axioms right089
#print axioms normalized090
#print axioms left090
#print axioms right090
#print axioms normalized091
#print axioms left091
#print axioms right091
#print axioms normalized092
#print axioms left092
#print axioms right092
#print axioms normalized093
#print axioms left093
#print axioms right093
#print axioms normalized094
#print axioms left094
#print axioms right094
#print axioms normalized095
#print axioms left095
#print axioms right095
end StructuralGoal20261016.W10Aux478
end
