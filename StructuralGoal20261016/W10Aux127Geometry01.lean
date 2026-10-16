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
theorem normalized008 : AdaptiveCoverage.normalize SL cell015 = normal010 := by
  calc
    AdaptiveCoverage.normalize SL cell015 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell015)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell015)).symm
    _ = normal010 := by rfl
theorem left008 : leftChild 9 PR SL normal010 1 8 229376 = cell017 := by
  calc
    leftChild 9 PR SL normal010 1 8 229376 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal010) 1 8 229376).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal010) 1 8 229376).symm
    _ = cell017 := by rfl
theorem right008 : rightChild 9 PR SL normal010 1 8 229376 = cell018 := by
  calc
    rightChild 9 PR SL normal010 1 8 229376 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal010) 1 8 229376).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal010) 1 8 229376).symm
    _ = cell018 := by rfl
theorem normalized009 : AdaptiveCoverage.normalize SL cell018 = normal012 := by
  calc
    AdaptiveCoverage.normalize SL cell018 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell018)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell018)).symm
    _ = normal012 := by rfl
theorem left009 : leftChild 9 PR SL normal012 0 6 212992 = cell019 := by
  calc
    leftChild 9 PR SL normal012 0 6 212992 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal012) 0 6 212992).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal012) 0 6 212992).symm
    _ = cell019 := by rfl
theorem right009 : rightChild 9 PR SL normal012 0 6 212992 = cell020 := by
  calc
    rightChild 9 PR SL normal012 0 6 212992 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal012) 0 6 212992).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal012) 0 6 212992).symm
    _ = cell020 := by rfl
theorem normalized010 : AdaptiveCoverage.normalize SL cell019 = normal013 := by
  calc
    AdaptiveCoverage.normalize SL cell019 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell019)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell019)).symm
    _ = normal013 := by rfl
theorem left010 : leftChild 9 PR SL normal013 0 7 229376 = cell021 := by
  calc
    leftChild 9 PR SL normal013 0 7 229376 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal013) 0 7 229376).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal013) 0 7 229376).symm
    _ = cell021 := by rfl
theorem right010 : rightChild 9 PR SL normal013 0 7 229376 = cell022 := by
  calc
    rightChild 9 PR SL normal013 0 7 229376 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal013) 0 7 229376).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal013) 0 7 229376).symm
    _ = cell022 := by rfl
theorem normalized011 : AdaptiveCoverage.normalize SL cell022 = normal015 := by
  calc
    AdaptiveCoverage.normalize SL cell022 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell022)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell022)).symm
    _ = normal015 := by rfl
theorem left011 : leftChild 9 PR SL normal015 3 9 212992 = cell023 := by
  calc
    leftChild 9 PR SL normal015 3 9 212992 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal015) 3 9 212992).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal015) 3 9 212992).symm
    _ = cell023 := by rfl
theorem right011 : rightChild 9 PR SL normal015 3 9 212992 = cell024 := by
  calc
    rightChild 9 PR SL normal015 3 9 212992 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal015) 3 9 212992).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal015) 3 9 212992).symm
    _ = cell024 := by rfl
theorem normalized012 : AdaptiveCoverage.normalize SL cell024 = normal017 := by
  calc
    AdaptiveCoverage.normalize SL cell024 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell024)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell024)).symm
    _ = normal017 := by rfl
theorem left012 : leftChild 9 PR SL normal017 3 8 180224 = cell025 := by
  calc
    leftChild 9 PR SL normal017 3 8 180224 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal017) 3 8 180224).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal017) 3 8 180224).symm
    _ = cell025 := by rfl
theorem right012 : rightChild 9 PR SL normal017 3 8 180224 = cell026 := by
  calc
    rightChild 9 PR SL normal017 3 8 180224 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal017) 3 8 180224).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal017) 3 8 180224).symm
    _ = cell026 := by rfl
theorem normalized013 : AdaptiveCoverage.normalize SL cell025 = normal018 := by
  calc
    AdaptiveCoverage.normalize SL cell025 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell025)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell025)).symm
    _ = normal018 := by rfl
theorem left013 : leftChild 9 PR SL normal018 0 8 278528 = cell027 := by
  calc
    leftChild 9 PR SL normal018 0 8 278528 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal018) 0 8 278528).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal018) 0 8 278528).symm
    _ = cell027 := by rfl
theorem right013 : rightChild 9 PR SL normal018 0 8 278528 = cell028 := by
  calc
    rightChild 9 PR SL normal018 0 8 278528 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal018) 0 8 278528).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal018) 0 8 278528).symm
    _ = cell028 := by rfl
theorem normalized014 : AdaptiveCoverage.normalize SL cell026 = normal021 := by
  calc
    AdaptiveCoverage.normalize SL cell026 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell026)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell026)).symm
    _ = normal021 := by rfl
theorem left014 : leftChild 9 PR SL normal021 0 8 278528 = cell029 := by
  calc
    leftChild 9 PR SL normal021 0 8 278528 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal021) 0 8 278528).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal021) 0 8 278528).symm
    _ = cell029 := by rfl
theorem right014 : rightChild 9 PR SL normal021 0 8 278528 = cell030 := by
  calc
    rightChild 9 PR SL normal021 0 8 278528 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal021) 0 8 278528).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal021) 0 8 278528).symm
    _ = cell030 := by rfl
theorem normalized015 : AdaptiveCoverage.normalize SL cell030 = normal023 := by
  calc
    AdaptiveCoverage.normalize SL cell030 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell030)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell030)).symm
    _ = normal023 := by rfl
theorem left015 : leftChild 9 PR SL normal023 0 6 196608 = cell031 := by
  calc
    leftChild 9 PR SL normal023 0 6 196608 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal023) 0 6 196608).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal023) 0 6 196608).symm
    _ = cell031 := by rfl
theorem right015 : rightChild 9 PR SL normal023 0 6 196608 = cell032 := by
  calc
    rightChild 9 PR SL normal023 0 6 196608 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal023) 0 6 196608).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal023) 0 6 196608).symm
    _ = cell032 := by rfl

set_option pp.fullNames true
#print axioms normalized008
#print axioms left008
#print axioms right008
#print axioms normalized009
#print axioms left009
#print axioms right009
#print axioms normalized010
#print axioms left010
#print axioms right010
#print axioms normalized011
#print axioms left011
#print axioms right011
#print axioms normalized012
#print axioms left012
#print axioms right012
#print axioms normalized013
#print axioms left013
#print axioms right013
#print axioms normalized014
#print axioms left014
#print axioms right014
#print axioms normalized015
#print axioms left015
#print axioms right015
end StructuralGoal20261016.W10Aux127
end
