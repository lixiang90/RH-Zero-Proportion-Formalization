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
theorem normalized104 : AdaptiveCoverage.normalize SL cell208 = normal196 := by
  calc
    AdaptiveCoverage.normalize SL cell208 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell208)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell208)).symm
    _ = normal196 := by rfl
theorem left104 : leftChild 9 PR SL normal196 4 7 114688 = cell209 := by
  calc
    leftChild 9 PR SL normal196 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal196) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal196) 4 7 114688).symm
    _ = cell209 := by rfl
theorem right104 : rightChild 9 PR SL normal196 4 7 114688 = cell210 := by
  calc
    rightChild 9 PR SL normal196 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal196) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal196) 4 7 114688).symm
    _ = cell210 := by rfl
theorem normalized105 : AdaptiveCoverage.normalize SL cell204 = normal200 := by
  calc
    AdaptiveCoverage.normalize SL cell204 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell204)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell204)).symm
    _ = normal200 := by rfl
theorem left105 : leftChild 9 PR SL normal200 1 8 262144 = cell211 := by
  calc
    leftChild 9 PR SL normal200 1 8 262144 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal200) 1 8 262144).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal200) 1 8 262144).symm
    _ = cell211 := by rfl
theorem right105 : rightChild 9 PR SL normal200 1 8 262144 = cell212 := by
  calc
    rightChild 9 PR SL normal200 1 8 262144 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal200) 1 8 262144).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal200) 1 8 262144).symm
    _ = cell212 := by rfl
theorem normalized106 : AdaptiveCoverage.normalize SL cell211 = normal201 := by
  calc
    AdaptiveCoverage.normalize SL cell211 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell211)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell211)).symm
    _ = normal201 := by rfl
theorem left106 : leftChild 9 PR SL normal201 0 9 335872 = cell213 := by
  calc
    leftChild 9 PR SL normal201 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal201) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal201) 0 9 335872).symm
    _ = cell213 := by rfl
theorem right106 : rightChild 9 PR SL normal201 0 9 335872 = cell214 := by
  calc
    rightChild 9 PR SL normal201 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal201) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal201) 0 9 335872).symm
    _ = cell214 := by rfl
theorem normalized107 : AdaptiveCoverage.normalize SL cell213 = normal202 := by
  calc
    AdaptiveCoverage.normalize SL cell213 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell213)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell213)).symm
    _ = normal202 := by rfl
theorem left107 : leftChild 9 PR SL normal202 2 6 131072 = cell215 := by
  calc
    leftChild 9 PR SL normal202 2 6 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal202) 2 6 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal202) 2 6 131072).symm
    _ = cell215 := by rfl
theorem right107 : rightChild 9 PR SL normal202 2 6 131072 = cell216 := by
  calc
    rightChild 9 PR SL normal202 2 6 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal202) 2 6 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal202) 2 6 131072).symm
    _ = cell216 := by rfl
theorem normalized108 : AdaptiveCoverage.normalize SL cell216 = normal204 := by
  calc
    AdaptiveCoverage.normalize SL cell216 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell216)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell216)).symm
    _ = normal204 := by rfl
theorem left108 : leftChild 9 PR SL normal204 4 7 114688 = cell217 := by
  calc
    leftChild 9 PR SL normal204 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal204) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal204) 4 7 114688).symm
    _ = cell217 := by rfl
theorem right108 : rightChild 9 PR SL normal204 4 7 114688 = cell218 := by
  calc
    rightChild 9 PR SL normal204 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal204) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal204) 4 7 114688).symm
    _ = cell218 := by rfl
theorem normalized109 : AdaptiveCoverage.normalize SL cell212 = normal208 := by
  calc
    AdaptiveCoverage.normalize SL cell212 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell212)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell212)).symm
    _ = normal208 := by rfl
theorem left109 : leftChild 9 PR SL normal208 0 9 335872 = cell219 := by
  calc
    leftChild 9 PR SL normal208 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal208) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal208) 0 9 335872).symm
    _ = cell219 := by rfl
theorem right109 : rightChild 9 PR SL normal208 0 9 335872 = cell220 := by
  calc
    rightChild 9 PR SL normal208 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal208) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal208) 0 9 335872).symm
    _ = cell220 := by rfl
theorem normalized110 : AdaptiveCoverage.normalize SL cell219 = normal209 := by
  calc
    AdaptiveCoverage.normalize SL cell219 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell219)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell219)).symm
    _ = normal209 := by rfl
theorem left110 : leftChild 9 PR SL normal209 2 6 131072 = cell221 := by
  calc
    leftChild 9 PR SL normal209 2 6 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal209) 2 6 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal209) 2 6 131072).symm
    _ = cell221 := by rfl
theorem right110 : rightChild 9 PR SL normal209 2 6 131072 = cell222 := by
  calc
    rightChild 9 PR SL normal209 2 6 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal209) 2 6 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal209) 2 6 131072).symm
    _ = cell222 := by rfl
theorem normalized111 : AdaptiveCoverage.normalize SL cell222 = normal211 := by
  calc
    AdaptiveCoverage.normalize SL cell222 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell222)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell222)).symm
    _ = normal211 := by rfl
theorem left111 : leftChild 9 PR SL normal211 4 7 114688 = cell223 := by
  calc
    leftChild 9 PR SL normal211 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal211) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal211) 4 7 114688).symm
    _ = cell223 := by rfl
theorem right111 : rightChild 9 PR SL normal211 4 7 114688 = cell224 := by
  calc
    rightChild 9 PR SL normal211 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal211) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal211) 4 7 114688).symm
    _ = cell224 := by rfl

set_option pp.fullNames true
#print axioms normalized104
#print axioms left104
#print axioms right104
#print axioms normalized105
#print axioms left105
#print axioms right105
#print axioms normalized106
#print axioms left106
#print axioms right106
#print axioms normalized107
#print axioms left107
#print axioms right107
#print axioms normalized108
#print axioms left108
#print axioms right108
#print axioms normalized109
#print axioms left109
#print axioms right109
#print axioms normalized110
#print axioms left110
#print axioms right110
#print axioms normalized111
#print axioms left111
#print axioms right111
end StructuralGoal20261016.W10Aux478
end
