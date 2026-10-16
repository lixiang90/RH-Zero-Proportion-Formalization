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
theorem normalized032 : AdaptiveCoverage.normalize SL cell064 = normal056 := by
  calc
    AdaptiveCoverage.normalize SL cell064 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell064)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell064)).symm
    _ = normal056 := by rfl
theorem left032 : leftChild 9 PR SL normal056 2 6 131072 = cell065 := by
  calc
    leftChild 9 PR SL normal056 2 6 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal056) 2 6 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal056) 2 6 131072).symm
    _ = cell065 := by rfl
theorem right032 : rightChild 9 PR SL normal056 2 6 131072 = cell066 := by
  calc
    rightChild 9 PR SL normal056 2 6 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal056) 2 6 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal056) 2 6 131072).symm
    _ = cell066 := by rfl
theorem normalized033 : AdaptiveCoverage.normalize SL cell066 = normal058 := by
  calc
    AdaptiveCoverage.normalize SL cell066 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell066)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell066)).symm
    _ = normal058 := by rfl
theorem left033 : leftChild 9 PR SL normal058 3 7 131072 = cell067 := by
  calc
    leftChild 9 PR SL normal058 3 7 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal058) 3 7 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal058) 3 7 131072).symm
    _ = cell067 := by rfl
theorem right033 : rightChild 9 PR SL normal058 3 7 131072 = cell068 := by
  calc
    rightChild 9 PR SL normal058 3 7 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal058) 3 7 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal058) 3 7 131072).symm
    _ = cell068 := by rfl
theorem normalized034 : AdaptiveCoverage.normalize SL cell068 = normal060 := by
  calc
    AdaptiveCoverage.normalize SL cell068 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell068)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell068)).symm
    _ = normal060 := by rfl
theorem left034 : leftChild 9 PR SL normal060 3 5 65536 = cell069 := by
  calc
    leftChild 9 PR SL normal060 3 5 65536 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal060) 3 5 65536).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal060) 3 5 65536).symm
    _ = cell069 := by rfl
theorem right034 : rightChild 9 PR SL normal060 3 5 65536 = cell070 := by
  calc
    rightChild 9 PR SL normal060 3 5 65536 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal060) 3 5 65536).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal060) 3 5 65536).symm
    _ = cell070 := by rfl
theorem normalized035 : AdaptiveCoverage.normalize SL cell070 = normal062 := by
  calc
    AdaptiveCoverage.normalize SL cell070 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell070)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell070)).symm
    _ = normal062 := by rfl
theorem left035 : leftChild 9 PR SL normal062 4 6 65536 = cell071 := by
  calc
    leftChild 9 PR SL normal062 4 6 65536 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal062) 4 6 65536).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal062) 4 6 65536).symm
    _ = cell071 := by rfl
theorem right035 : rightChild 9 PR SL normal062 4 6 65536 = cell072 := by
  calc
    rightChild 9 PR SL normal062 4 6 65536 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal062) 4 6 65536).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal062) 4 6 65536).symm
    _ = cell072 := by rfl
theorem normalized036 : AdaptiveCoverage.normalize SL cell072 = normal064 := by
  calc
    AdaptiveCoverage.normalize SL cell072 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell072)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell072)).symm
    _ = normal064 := by rfl
theorem left036 : leftChild 9 PR SL normal064 1 8 245760 = cell073 := by
  calc
    leftChild 9 PR SL normal064 1 8 245760 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal064) 1 8 245760).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal064) 1 8 245760).symm
    _ = cell073 := by rfl
theorem right036 : rightChild 9 PR SL normal064 1 8 245760 = cell074 := by
  calc
    rightChild 9 PR SL normal064 1 8 245760 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal064) 1 8 245760).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal064) 1 8 245760).symm
    _ = cell074 := by rfl
theorem normalized037 : AdaptiveCoverage.normalize SL cell074 = normal066 := by
  calc
    AdaptiveCoverage.normalize SL cell074 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell074)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell074)).symm
    _ = normal066 := by rfl
theorem left037 : leftChild 9 PR SL normal066 2 9 245760 = cell075 := by
  calc
    leftChild 9 PR SL normal066 2 9 245760 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal066) 2 9 245760).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal066) 2 9 245760).symm
    _ = cell075 := by rfl
theorem right037 : rightChild 9 PR SL normal066 2 9 245760 = cell076 := by
  calc
    rightChild 9 PR SL normal066 2 9 245760 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal066) 2 9 245760).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal066) 2 9 245760).symm
    _ = cell076 := by rfl
theorem normalized038 : AdaptiveCoverage.normalize SL cell016 = normal071 := by
  calc
    AdaptiveCoverage.normalize SL cell016 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell016)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell016)).symm
    _ = normal071 := by rfl
theorem left038 : leftChild 9 PR SL normal071 0 6 212992 = cell077 := by
  calc
    leftChild 9 PR SL normal071 0 6 212992 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal071) 0 6 212992).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal071) 0 6 212992).symm
    _ = cell077 := by rfl
theorem right038 : rightChild 9 PR SL normal071 0 6 212992 = cell078 := by
  calc
    rightChild 9 PR SL normal071 0 6 212992 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal071) 0 6 212992).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal071) 0 6 212992).symm
    _ = cell078 := by rfl
theorem normalized039 : AdaptiveCoverage.normalize SL cell077 = normal072 := by
  calc
    AdaptiveCoverage.normalize SL cell077 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell077)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell077)).symm
    _ = normal072 := by rfl
theorem left039 : leftChild 9 PR SL normal072 4 7 114688 = cell079 := by
  calc
    leftChild 9 PR SL normal072 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal072) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal072) 4 7 114688).symm
    _ = cell079 := by rfl
theorem right039 : rightChild 9 PR SL normal072 4 7 114688 = cell080 := by
  calc
    rightChild 9 PR SL normal072 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal072) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal072) 4 7 114688).symm
    _ = cell080 := by rfl

set_option pp.fullNames true
#print axioms normalized032
#print axioms left032
#print axioms right032
#print axioms normalized033
#print axioms left033
#print axioms right033
#print axioms normalized034
#print axioms left034
#print axioms right034
#print axioms normalized035
#print axioms left035
#print axioms right035
#print axioms normalized036
#print axioms left036
#print axioms right036
#print axioms normalized037
#print axioms left037
#print axioms right037
#print axioms normalized038
#print axioms left038
#print axioms right038
#print axioms normalized039
#print axioms left039
#print axioms right039
end StructuralGoal20261016.W10Aux127
end
