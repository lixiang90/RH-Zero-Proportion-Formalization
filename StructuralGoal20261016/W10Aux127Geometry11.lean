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
theorem normalized088 : AdaptiveCoverage.normalize SL cell175 = normal167 := by
  calc
    AdaptiveCoverage.normalize SL cell175 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell175)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell175)).symm
    _ = normal167 := by rfl
theorem left088 : leftChild 9 PR SL normal167 3 7 163840 = cell177 := by
  calc
    leftChild 9 PR SL normal167 3 7 163840 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal167) 3 7 163840).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal167) 3 7 163840).symm
    _ = cell177 := by rfl
theorem right088 : rightChild 9 PR SL normal167 3 7 163840 = cell178 := by
  calc
    rightChild 9 PR SL normal167 3 7 163840 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal167) 3 7 163840).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal167) 3 7 163840).symm
    _ = cell178 := by rfl
theorem normalized089 : AdaptiveCoverage.normalize SL cell177 = normal168 := by
  calc
    AdaptiveCoverage.normalize SL cell177 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell177)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell177)).symm
    _ = normal168 := by rfl
theorem left089 : leftChild 9 PR SL normal168 0 9 319488 = cell179 := by
  calc
    leftChild 9 PR SL normal168 0 9 319488 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal168) 0 9 319488).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal168) 0 9 319488).symm
    _ = cell179 := by rfl
theorem right089 : rightChild 9 PR SL normal168 0 9 319488 = cell180 := by
  calc
    rightChild 9 PR SL normal168 0 9 319488 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal168) 0 9 319488).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal168) 0 9 319488).symm
    _ = cell180 := by rfl
theorem normalized090 : AdaptiveCoverage.normalize SL cell180 = normal170 := by
  calc
    AdaptiveCoverage.normalize SL cell180 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell180)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell180)).symm
    _ = normal170 := by rfl
theorem left090 : leftChild 9 PR SL normal170 1 8 245760 = cell181 := by
  calc
    leftChild 9 PR SL normal170 1 8 245760 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal170) 1 8 245760).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal170) 1 8 245760).symm
    _ = cell181 := by rfl
theorem right090 : rightChild 9 PR SL normal170 1 8 245760 = cell182 := by
  calc
    rightChild 9 PR SL normal170 1 8 245760 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal170) 1 8 245760).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal170) 1 8 245760).symm
    _ = cell182 := by rfl
theorem normalized091 : AdaptiveCoverage.normalize SL cell182 = normal172 := by
  calc
    AdaptiveCoverage.normalize SL cell182 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell182)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell182)).symm
    _ = normal172 := by rfl
theorem left091 : leftChild 9 PR SL normal172 0 6 229376 = cell183 := by
  calc
    leftChild 9 PR SL normal172 0 6 229376 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal172) 0 6 229376).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal172) 0 6 229376).symm
    _ = cell183 := by rfl
theorem right091 : rightChild 9 PR SL normal172 0 6 229376 = cell184 := by
  calc
    rightChild 9 PR SL normal172 0 6 229376 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal172) 0 6 229376).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal172) 0 6 229376).symm
    _ = cell184 := by rfl
theorem normalized092 : AdaptiveCoverage.normalize SL cell183 = normal173 := by
  calc
    AdaptiveCoverage.normalize SL cell183 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell183)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell183)).symm
    _ = normal173 := by rfl
theorem left092 : leftChild 9 PR SL normal173 0 7 245760 = cell185 := by
  calc
    leftChild 9 PR SL normal173 0 7 245760 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal173) 0 7 245760).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal173) 0 7 245760).symm
    _ = cell185 := by rfl
theorem right092 : rightChild 9 PR SL normal173 0 7 245760 = cell186 := by
  calc
    rightChild 9 PR SL normal173 0 7 245760 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal173) 0 7 245760).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal173) 0 7 245760).symm
    _ = cell186 := by rfl
theorem normalized093 : AdaptiveCoverage.normalize SL cell186 = normal175 := by
  calc
    AdaptiveCoverage.normalize SL cell186 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell186)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell186)).symm
    _ = normal175 := by rfl
theorem left093 : leftChild 9 PR SL normal175 3 9 229376 = cell187 := by
  calc
    leftChild 9 PR SL normal175 3 9 229376 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal175) 3 9 229376).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal175) 3 9 229376).symm
    _ = cell187 := by rfl
theorem right093 : rightChild 9 PR SL normal175 3 9 229376 = cell188 := by
  calc
    rightChild 9 PR SL normal175 3 9 229376 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal175) 3 9 229376).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal175) 3 9 229376).symm
    _ = cell188 := by rfl
theorem normalized094 : AdaptiveCoverage.normalize SL cell187 = normal176 := by
  calc
    AdaptiveCoverage.normalize SL cell187 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell187)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell187)).symm
    _ = normal176 := by rfl
theorem left094 : leftChild 9 PR SL normal176 3 5 81920 = cell189 := by
  calc
    leftChild 9 PR SL normal176 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal176) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal176) 3 5 81920).symm
    _ = cell189 := by rfl
theorem right094 : rightChild 9 PR SL normal176 3 5 81920 = cell190 := by
  calc
    rightChild 9 PR SL normal176 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal176) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal176) 3 5 81920).symm
    _ = cell190 := by rfl
theorem normalized095 : AdaptiveCoverage.normalize SL cell188 = normal179 := by
  calc
    AdaptiveCoverage.normalize SL cell188 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell188)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell188)).symm
    _ = normal179 := by rfl
theorem left095 : leftChild 9 PR SL normal179 4 6 65536 = cell191 := by
  calc
    leftChild 9 PR SL normal179 4 6 65536 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal179) 4 6 65536).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal179) 4 6 65536).symm
    _ = cell191 := by rfl
theorem right095 : rightChild 9 PR SL normal179 4 6 65536 = cell192 := by
  calc
    rightChild 9 PR SL normal179 4 6 65536 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal179) 4 6 65536).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal179) 4 6 65536).symm
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
end StructuralGoal20261016.W10Aux127
end
