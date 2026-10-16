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
theorem normalized032 : AdaptiveCoverage.normalize SL cell063 = normal053 := by
  calc
    AdaptiveCoverage.normalize SL cell063 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell063)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell063)).symm
    _ = normal053 := by rfl
theorem left032 : leftChild 9 PR SL normal053 3 7 147456 = cell065 := by
  calc
    leftChild 9 PR SL normal053 3 7 147456 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal053) 3 7 147456).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal053) 3 7 147456).symm
    _ = cell065 := by rfl
theorem right032 : rightChild 9 PR SL normal053 3 7 147456 = cell066 := by
  calc
    rightChild 9 PR SL normal053 3 7 147456 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal053) 3 7 147456).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal053) 3 7 147456).symm
    _ = cell066 := by rfl
theorem normalized033 : AdaptiveCoverage.normalize SL cell010 = normal062 := by
  calc
    AdaptiveCoverage.normalize SL cell010 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell010)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell010)).symm
    _ = normal062 := by rfl
theorem left033 : leftChild 9 PR SL normal062 1 9 278528 = cell067 := by
  calc
    leftChild 9 PR SL normal062 1 9 278528 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal062) 1 9 278528).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal062) 1 9 278528).symm
    _ = cell067 := by rfl
theorem right033 : rightChild 9 PR SL normal062 1 9 278528 = cell068 := by
  calc
    rightChild 9 PR SL normal062 1 9 278528 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal062) 1 9 278528).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal062) 1 9 278528).symm
    _ = cell068 := by rfl
theorem normalized034 : AdaptiveCoverage.normalize SL cell068 = normal064 := by
  calc
    AdaptiveCoverage.normalize SL cell068 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell068)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell068)).symm
    _ = normal064 := by rfl
theorem left034 : leftChild 9 PR SL normal064 0 9 344064 = cell069 := by
  calc
    leftChild 9 PR SL normal064 0 9 344064 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal064) 0 9 344064).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal064) 0 9 344064).symm
    _ = cell069 := by rfl
theorem right034 : rightChild 9 PR SL normal064 0 9 344064 = cell070 := by
  calc
    rightChild 9 PR SL normal064 0 9 344064 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal064) 0 9 344064).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal064) 0 9 344064).symm
    _ = cell070 := by rfl
theorem normalized035 : AdaptiveCoverage.normalize SL cell069 = normal065 := by
  calc
    AdaptiveCoverage.normalize SL cell069 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell069)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell069)).symm
    _ = normal065 := by rfl
theorem left035 : leftChild 9 PR SL normal065 2 6 163840 = cell071 := by
  calc
    leftChild 9 PR SL normal065 2 6 163840 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal065) 2 6 163840).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal065) 2 6 163840).symm
    _ = cell071 := by rfl
theorem right035 : rightChild 9 PR SL normal065 2 6 163840 = cell072 := by
  calc
    rightChild 9 PR SL normal065 2 6 163840 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal065) 2 6 163840).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal065) 2 6 163840).symm
    _ = cell072 := by rfl
theorem normalized036 : AdaptiveCoverage.normalize SL cell071 = normal066 := by
  calc
    AdaptiveCoverage.normalize SL cell071 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell071)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell071)).symm
    _ = normal066 := by rfl
theorem left036 : leftChild 9 PR SL normal066 3 7 163840 = cell073 := by
  calc
    leftChild 9 PR SL normal066 3 7 163840 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal066) 3 7 163840).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal066) 3 7 163840).symm
    _ = cell073 := by rfl
theorem right036 : rightChild 9 PR SL normal066 3 7 163840 = cell074 := by
  calc
    rightChild 9 PR SL normal066 3 7 163840 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal066) 3 7 163840).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal066) 3 7 163840).symm
    _ = cell074 := by rfl
theorem normalized037 : AdaptiveCoverage.normalize SL cell073 = normal067 := by
  calc
    AdaptiveCoverage.normalize SL cell073 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell073)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell073)).symm
    _ = normal067 := by rfl
theorem left037 : leftChild 9 PR SL normal067 1 8 245760 = cell075 := by
  calc
    leftChild 9 PR SL normal067 1 8 245760 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal067) 1 8 245760).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal067) 1 8 245760).symm
    _ = cell075 := by rfl
theorem right037 : rightChild 9 PR SL normal067 1 8 245760 = cell076 := by
  calc
    rightChild 9 PR SL normal067 1 8 245760 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal067) 1 8 245760).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal067) 1 8 245760).symm
    _ = cell076 := by rfl
theorem normalized038 : AdaptiveCoverage.normalize SL cell075 = normal068 := by
  calc
    AdaptiveCoverage.normalize SL cell075 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell075)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell075)).symm
    _ = normal068 := by rfl
theorem left038 : leftChild 9 PR SL normal068 0 6 212992 = cell077 := by
  calc
    leftChild 9 PR SL normal068 0 6 212992 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal068) 0 6 212992).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal068) 0 6 212992).symm
    _ = cell077 := by rfl
theorem right038 : rightChild 9 PR SL normal068 0 6 212992 = cell078 := by
  calc
    rightChild 9 PR SL normal068 0 6 212992 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal068) 0 6 212992).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal068) 0 6 212992).symm
    _ = cell078 := by rfl
theorem normalized039 : AdaptiveCoverage.normalize SL cell078 = normal070 := by
  calc
    AdaptiveCoverage.normalize SL cell078 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell078)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell078)).symm
    _ = normal070 := by rfl
theorem left039 : leftChild 9 PR SL normal070 3 9 212992 = cell079 := by
  calc
    leftChild 9 PR SL normal070 3 9 212992 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal070) 3 9 212992).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal070) 3 9 212992).symm
    _ = cell079 := by rfl
theorem right039 : rightChild 9 PR SL normal070 3 9 212992 = cell080 := by
  calc
    rightChild 9 PR SL normal070 3 9 212992 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal070) 3 9 212992).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal070) 3 9 212992).symm
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
end StructuralGoal20261016.W10Aux478
end
