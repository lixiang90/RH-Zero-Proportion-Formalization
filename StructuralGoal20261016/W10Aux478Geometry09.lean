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
theorem normalized072 : AdaptiveCoverage.normalize SL cell144 = normal127 := by
  calc
    AdaptiveCoverage.normalize SL cell144 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell144)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell144)).symm
    _ = normal127 := by rfl
theorem left072 : leftChild 9 PR SL normal127 5 7 65536 = cell145 := by
  calc
    leftChild 9 PR SL normal127 5 7 65536 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal127) 5 7 65536).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal127) 5 7 65536).symm
    _ = cell145 := by rfl
theorem right072 : rightChild 9 PR SL normal127 5 7 65536 = cell146 := by
  calc
    rightChild 9 PR SL normal127 5 7 65536 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal127) 5 7 65536).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal127) 5 7 65536).symm
    _ = cell146 := by rfl
theorem normalized073 : AdaptiveCoverage.normalize SL cell126 = normal133 := by
  calc
    AdaptiveCoverage.normalize SL cell126 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell126)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell126)).symm
    _ = normal133 := by rfl
theorem left073 : leftChild 9 PR SL normal133 4 7 114688 = cell147 := by
  calc
    leftChild 9 PR SL normal133 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal133) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal133) 4 7 114688).symm
    _ = cell147 := by rfl
theorem right073 : rightChild 9 PR SL normal133 4 7 114688 = cell148 := by
  calc
    rightChild 9 PR SL normal133 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal133) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal133) 4 7 114688).symm
    _ = cell148 := by rfl
theorem normalized074 : AdaptiveCoverage.normalize SL cell147 = normal134 := by
  calc
    AdaptiveCoverage.normalize SL cell147 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell147)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell147)).symm
    _ = normal134 := by rfl
theorem left074 : leftChild 9 PR SL normal134 0 9 335872 = cell149 := by
  calc
    leftChild 9 PR SL normal134 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal134) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal134) 0 9 335872).symm
    _ = cell149 := by rfl
theorem right074 : rightChild 9 PR SL normal134 0 9 335872 = cell150 := by
  calc
    rightChild 9 PR SL normal134 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal134) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal134) 0 9 335872).symm
    _ = cell150 := by rfl
theorem normalized075 : AdaptiveCoverage.normalize SL cell149 = normal135 := by
  calc
    AdaptiveCoverage.normalize SL cell149 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell149)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell149)).symm
    _ = normal135 := by rfl
theorem left075 : leftChild 9 PR SL normal135 3 6 98304 = cell151 := by
  calc
    leftChild 9 PR SL normal135 3 6 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal135) 3 6 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal135) 3 6 98304).symm
    _ = cell151 := by rfl
theorem right075 : rightChild 9 PR SL normal135 3 6 98304 = cell152 := by
  calc
    rightChild 9 PR SL normal135 3 6 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal135) 3 6 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal135) 3 6 98304).symm
    _ = cell152 := by rfl
theorem normalized076 : AdaptiveCoverage.normalize SL cell152 = normal137 := by
  calc
    AdaptiveCoverage.normalize SL cell152 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell152)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell152)).symm
    _ = normal137 := by rfl
theorem left076 : leftChild 9 PR SL normal137 2 5 98304 = cell153 := by
  calc
    leftChild 9 PR SL normal137 2 5 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal137) 2 5 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal137) 2 5 98304).symm
    _ = cell153 := by rfl
theorem right076 : rightChild 9 PR SL normal137 2 5 98304 = cell154 := by
  calc
    rightChild 9 PR SL normal137 2 5 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal137) 2 5 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal137) 2 5 98304).symm
    _ = cell154 := by rfl
theorem normalized077 : AdaptiveCoverage.normalize SL cell154 = normal139 := by
  calc
    AdaptiveCoverage.normalize SL cell154 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell154)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell154)).symm
    _ = normal139 := by rfl
theorem left077 : leftChild 9 PR SL normal139 2 4 81920 = cell155 := by
  calc
    leftChild 9 PR SL normal139 2 4 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal139) 2 4 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal139) 2 4 81920).symm
    _ = cell155 := by rfl
theorem right077 : rightChild 9 PR SL normal139 2 4 81920 = cell156 := by
  calc
    rightChild 9 PR SL normal139 2 4 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal139) 2 4 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal139) 2 4 81920).symm
    _ = cell156 := by rfl
theorem normalized078 : AdaptiveCoverage.normalize SL cell155 = normal140 := by
  calc
    AdaptiveCoverage.normalize SL cell155 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell155)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell155)).symm
    _ = normal140 := by rfl
theorem left078 : leftChild 9 PR SL normal140 3 7 147456 = cell157 := by
  calc
    leftChild 9 PR SL normal140 3 7 147456 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal140) 3 7 147456).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal140) 3 7 147456).symm
    _ = cell157 := by rfl
theorem right078 : rightChild 9 PR SL normal140 3 7 147456 = cell158 := by
  calc
    rightChild 9 PR SL normal140 3 7 147456 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal140) 3 7 147456).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal140) 3 7 147456).symm
    _ = cell158 := by rfl
theorem normalized079 : AdaptiveCoverage.normalize SL cell157 = normal141 := by
  calc
    AdaptiveCoverage.normalize SL cell157 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell157)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell157)).symm
    _ = normal141 := by rfl
theorem left079 : leftChild 9 PR SL normal141 2 6 147456 = cell159 := by
  calc
    leftChild 9 PR SL normal141 2 6 147456 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal141) 2 6 147456).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal141) 2 6 147456).symm
    _ = cell159 := by rfl
theorem right079 : rightChild 9 PR SL normal141 2 6 147456 = cell160 := by
  calc
    rightChild 9 PR SL normal141 2 6 147456 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal141) 2 6 147456).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal141) 2 6 147456).symm
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
end StructuralGoal20261016.W10Aux478
end
