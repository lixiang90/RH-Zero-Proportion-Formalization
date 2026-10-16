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
theorem normalized040 : AdaptiveCoverage.normalize SL cell080 = normal074 := by
  calc
    AdaptiveCoverage.normalize SL cell080 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell080)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell080)).symm
    _ = normal074 := by rfl
theorem left040 : leftChild 9 PR SL normal074 5 7 98304 = cell081 := by
  calc
    leftChild 9 PR SL normal074 5 7 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal074) 5 7 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal074) 5 7 98304).symm
    _ = cell081 := by rfl
theorem right040 : rightChild 9 PR SL normal074 5 7 98304 = cell082 := by
  calc
    rightChild 9 PR SL normal074 5 7 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal074) 5 7 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal074) 5 7 98304).symm
    _ = cell082 := by rfl
theorem normalized041 : AdaptiveCoverage.normalize SL cell081 = normal075 := by
  calc
    AdaptiveCoverage.normalize SL cell081 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell081)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell081)).symm
    _ = normal075 := by rfl
theorem left041 : leftChild 9 PR SL normal075 0 8 278528 = cell083 := by
  calc
    leftChild 9 PR SL normal075 0 8 278528 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal075) 0 8 278528).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal075) 0 8 278528).symm
    _ = cell083 := by rfl
theorem right041 : rightChild 9 PR SL normal075 0 8 278528 = cell084 := by
  calc
    rightChild 9 PR SL normal075 0 8 278528 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal075) 0 8 278528).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal075) 0 8 278528).symm
    _ = cell084 := by rfl
theorem normalized042 : AdaptiveCoverage.normalize SL cell084 = normal077 := by
  calc
    AdaptiveCoverage.normalize SL cell084 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell084)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell084)).symm
    _ = normal077 := by rfl
theorem left042 : leftChild 9 PR SL normal077 1 9 278528 = cell085 := by
  calc
    leftChild 9 PR SL normal077 1 9 278528 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal077) 1 9 278528).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal077) 1 9 278528).symm
    _ = cell085 := by rfl
theorem right042 : rightChild 9 PR SL normal077 1 9 278528 = cell086 := by
  calc
    rightChild 9 PR SL normal077 1 9 278528 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal077) 1 9 278528).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal077) 1 9 278528).symm
    _ = cell086 := by rfl
theorem normalized043 : AdaptiveCoverage.normalize SL cell086 = normal079 := by
  calc
    AdaptiveCoverage.normalize SL cell086 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell086)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell086)).symm
    _ = normal079 := by rfl
theorem left043 : leftChild 9 PR SL normal079 3 7 163840 = cell087 := by
  calc
    leftChild 9 PR SL normal079 3 7 163840 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal079) 3 7 163840).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal079) 3 7 163840).symm
    _ = cell087 := by rfl
theorem right043 : rightChild 9 PR SL normal079 3 7 163840 = cell088 := by
  calc
    rightChild 9 PR SL normal079 3 7 163840 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal079) 3 7 163840).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal079) 3 7 163840).symm
    _ = cell088 := by rfl
theorem normalized044 : AdaptiveCoverage.normalize SL cell087 = normal080 := by
  calc
    AdaptiveCoverage.normalize SL cell087 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell087)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell087)).symm
    _ = normal080 := by rfl
theorem left044 : leftChild 9 PR SL normal080 0 6 196608 = cell089 := by
  calc
    leftChild 9 PR SL normal080 0 6 196608 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal080) 0 6 196608).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal080) 0 6 196608).symm
    _ = cell089 := by rfl
theorem right044 : rightChild 9 PR SL normal080 0 6 196608 = cell090 := by
  calc
    rightChild 9 PR SL normal080 0 6 196608 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal080) 0 6 196608).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal080) 0 6 196608).symm
    _ = cell090 := by rfl
theorem normalized045 : AdaptiveCoverage.normalize SL cell090 = normal082 := by
  calc
    AdaptiveCoverage.normalize SL cell090 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell090)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell090)).symm
    _ = normal082 := by rfl
theorem left045 : leftChild 9 PR SL normal082 0 9 319488 = cell091 := by
  calc
    leftChild 9 PR SL normal082 0 9 319488 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal082) 0 9 319488).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal082) 0 9 319488).symm
    _ = cell091 := by rfl
theorem right045 : rightChild 9 PR SL normal082 0 9 319488 = cell092 := by
  calc
    rightChild 9 PR SL normal082 0 9 319488 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal082) 0 9 319488).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal082) 0 9 319488).symm
    _ = cell092 := by rfl
theorem normalized046 : AdaptiveCoverage.normalize SL cell092 = normal084 := by
  calc
    AdaptiveCoverage.normalize SL cell092 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell092)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell092)).symm
    _ = normal084 := by rfl
theorem left046 : leftChild 9 PR SL normal084 1 8 245760 = cell093 := by
  calc
    leftChild 9 PR SL normal084 1 8 245760 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal084) 1 8 245760).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal084) 1 8 245760).symm
    _ = cell093 := by rfl
theorem right046 : rightChild 9 PR SL normal084 1 8 245760 = cell094 := by
  calc
    rightChild 9 PR SL normal084 1 8 245760 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal084) 1 8 245760).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal084) 1 8 245760).symm
    _ = cell094 := by rfl
theorem normalized047 : AdaptiveCoverage.normalize SL cell094 = normal086 := by
  calc
    AdaptiveCoverage.normalize SL cell094 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell094)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell094)).symm
    _ = normal086 := by rfl
theorem left047 : leftChild 9 PR SL normal086 2 6 131072 = cell095 := by
  calc
    leftChild 9 PR SL normal086 2 6 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal086) 2 6 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal086) 2 6 131072).symm
    _ = cell095 := by rfl
theorem right047 : rightChild 9 PR SL normal086 2 6 131072 = cell096 := by
  calc
    rightChild 9 PR SL normal086 2 6 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal086) 2 6 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal086) 2 6 131072).symm
    _ = cell096 := by rfl

set_option pp.fullNames true
#print axioms normalized040
#print axioms left040
#print axioms right040
#print axioms normalized041
#print axioms left041
#print axioms right041
#print axioms normalized042
#print axioms left042
#print axioms right042
#print axioms normalized043
#print axioms left043
#print axioms right043
#print axioms normalized044
#print axioms left044
#print axioms right044
#print axioms normalized045
#print axioms left045
#print axioms right045
#print axioms normalized046
#print axioms left046
#print axioms right046
#print axioms normalized047
#print axioms left047
#print axioms right047
end StructuralGoal20261016.W10Aux127
end
