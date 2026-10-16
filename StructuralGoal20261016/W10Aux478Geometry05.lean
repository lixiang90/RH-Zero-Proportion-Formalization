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
theorem normalized040 : AdaptiveCoverage.normalize SL cell080 = normal072 := by
  calc
    AdaptiveCoverage.normalize SL cell080 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell080)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell080)).symm
    _ = normal072 := by rfl
theorem left040 : leftChild 9 PR SL normal072 2 6 131072 = cell081 := by
  calc
    leftChild 9 PR SL normal072 2 6 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal072) 2 6 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal072) 2 6 131072).symm
    _ = cell081 := by rfl
theorem right040 : rightChild 9 PR SL normal072 2 6 131072 = cell082 := by
  calc
    rightChild 9 PR SL normal072 2 6 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal072) 2 6 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal072) 2 6 131072).symm
    _ = cell082 := by rfl
theorem normalized041 : AdaptiveCoverage.normalize SL cell082 = normal074 := by
  calc
    AdaptiveCoverage.normalize SL cell082 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell082)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell082)).symm
    _ = normal074 := by rfl
theorem left041 : leftChild 9 PR SL normal074 3 7 131072 = cell083 := by
  calc
    leftChild 9 PR SL normal074 3 7 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal074) 3 7 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal074) 3 7 131072).symm
    _ = cell083 := by rfl
theorem right041 : rightChild 9 PR SL normal074 3 7 131072 = cell084 := by
  calc
    rightChild 9 PR SL normal074 3 7 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal074) 3 7 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal074) 3 7 131072).symm
    _ = cell084 := by rfl
theorem normalized042 : AdaptiveCoverage.normalize SL cell084 = normal076 := by
  calc
    AdaptiveCoverage.normalize SL cell084 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell084)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell084)).symm
    _ = normal076 := by rfl
theorem left042 : leftChild 9 PR SL normal076 3 5 81920 = cell085 := by
  calc
    leftChild 9 PR SL normal076 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal076) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal076) 3 5 81920).symm
    _ = cell085 := by rfl
theorem right042 : rightChild 9 PR SL normal076 3 5 81920 = cell086 := by
  calc
    rightChild 9 PR SL normal076 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal076) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal076) 3 5 81920).symm
    _ = cell086 := by rfl
theorem normalized043 : AdaptiveCoverage.normalize SL cell085 = normal077 := by
  calc
    AdaptiveCoverage.normalize SL cell085 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell085)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell085)).symm
    _ = normal077 := by rfl
theorem left043 : leftChild 9 PR SL normal077 4 6 81920 = cell087 := by
  calc
    leftChild 9 PR SL normal077 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal077) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal077) 4 6 81920).symm
    _ = cell087 := by rfl
theorem right043 : rightChild 9 PR SL normal077 4 6 81920 = cell088 := by
  calc
    rightChild 9 PR SL normal077 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal077) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal077) 4 6 81920).symm
    _ = cell088 := by rfl
theorem normalized044 : AdaptiveCoverage.normalize SL cell076 = normal081 := by
  calc
    AdaptiveCoverage.normalize SL cell076 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell076)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell076)).symm
    _ = normal081 := by rfl
theorem left044 : leftChild 9 PR SL normal081 0 6 212992 = cell089 := by
  calc
    leftChild 9 PR SL normal081 0 6 212992 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal081) 0 6 212992).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal081) 0 6 212992).symm
    _ = cell089 := by rfl
theorem right044 : rightChild 9 PR SL normal081 0 6 212992 = cell090 := by
  calc
    rightChild 9 PR SL normal081 0 6 212992 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal081) 0 6 212992).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal081) 0 6 212992).symm
    _ = cell090 := by rfl
theorem normalized045 : AdaptiveCoverage.normalize SL cell089 = normal082 := by
  calc
    AdaptiveCoverage.normalize SL cell089 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell089)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell089)).symm
    _ = normal082 := by rfl
theorem left045 : leftChild 9 PR SL normal082 3 7 131072 = cell091 := by
  calc
    leftChild 9 PR SL normal082 3 7 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal082) 3 7 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal082) 3 7 131072).symm
    _ = cell091 := by rfl
theorem right045 : rightChild 9 PR SL normal082 3 7 131072 = cell092 := by
  calc
    rightChild 9 PR SL normal082 3 7 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal082) 3 7 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal082) 3 7 131072).symm
    _ = cell092 := by rfl
theorem normalized046 : AdaptiveCoverage.normalize SL cell092 = normal084 := by
  calc
    AdaptiveCoverage.normalize SL cell092 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell092)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell092)).symm
    _ = normal084 := by rfl
theorem left046 : leftChild 9 PR SL normal084 0 7 245760 = cell093 := by
  calc
    leftChild 9 PR SL normal084 0 7 245760 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal084) 0 7 245760).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal084) 0 7 245760).symm
    _ = cell093 := by rfl
theorem right046 : rightChild 9 PR SL normal084 0 7 245760 = cell094 := by
  calc
    rightChild 9 PR SL normal084 0 7 245760 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal084) 0 7 245760).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal084) 0 7 245760).symm
    _ = cell094 := by rfl
theorem normalized047 : AdaptiveCoverage.normalize SL cell093 = normal085 := by
  calc
    AdaptiveCoverage.normalize SL cell093 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell093)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell093)).symm
    _ = normal085 := by rfl
theorem left047 : leftChild 9 PR SL normal085 3 8 196608 = cell095 := by
  calc
    leftChild 9 PR SL normal085 3 8 196608 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal085) 3 8 196608).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal085) 3 8 196608).symm
    _ = cell095 := by rfl
theorem right047 : rightChild 9 PR SL normal085 3 8 196608 = cell096 := by
  calc
    rightChild 9 PR SL normal085 3 8 196608 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal085) 3 8 196608).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal085) 3 8 196608).symm
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
end StructuralGoal20261016.W10Aux478
end
