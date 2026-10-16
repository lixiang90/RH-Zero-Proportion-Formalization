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
theorem normalized016 : AdaptiveCoverage.normalize SL cell031 = normal022 := by
  calc
    AdaptiveCoverage.normalize SL cell031 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell031)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell031)).symm
    _ = normal022 := by rfl
theorem left016 : leftChild 9 PR SL normal022 3 6 114688 = cell033 := by
  calc
    leftChild 9 PR SL normal022 3 6 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal022) 3 6 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal022) 3 6 114688).symm
    _ = cell033 := by rfl
theorem right016 : rightChild 9 PR SL normal022 3 6 114688 = cell034 := by
  calc
    rightChild 9 PR SL normal022 3 6 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal022) 3 6 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal022) 3 6 114688).symm
    _ = cell034 := by rfl
theorem normalized017 : AdaptiveCoverage.normalize SL cell033 = normal023 := by
  calc
    AdaptiveCoverage.normalize SL cell033 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell033)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell033)).symm
    _ = normal023 := by rfl
theorem left017 : leftChild 9 PR SL normal023 0 8 262144 = cell035 := by
  calc
    leftChild 9 PR SL normal023 0 8 262144 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal023) 0 8 262144).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal023) 0 8 262144).symm
    _ = cell035 := by rfl
theorem right017 : rightChild 9 PR SL normal023 0 8 262144 = cell036 := by
  calc
    rightChild 9 PR SL normal023 0 8 262144 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal023) 0 8 262144).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal023) 0 8 262144).symm
    _ = cell036 := by rfl
theorem normalized018 : AdaptiveCoverage.normalize SL cell036 = normal025 := by
  calc
    AdaptiveCoverage.normalize SL cell036 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell036)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell036)).symm
    _ = normal025 := by rfl
theorem left018 : leftChild 9 PR SL normal025 0 9 335872 = cell037 := by
  calc
    leftChild 9 PR SL normal025 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal025) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal025) 0 9 335872).symm
    _ = cell037 := by rfl
theorem right018 : rightChild 9 PR SL normal025 0 9 335872 = cell038 := by
  calc
    rightChild 9 PR SL normal025 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal025) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal025) 0 9 335872).symm
    _ = cell038 := by rfl
theorem normalized019 : AdaptiveCoverage.normalize SL cell016 = normal033 := by
  calc
    AdaptiveCoverage.normalize SL cell016 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell016)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell016)).symm
    _ = normal033 := by rfl
theorem left019 : leftChild 9 PR SL normal033 0 8 245760 = cell039 := by
  calc
    leftChild 9 PR SL normal033 0 8 245760 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal033) 0 8 245760).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal033) 0 8 245760).symm
    _ = cell039 := by rfl
theorem right019 : rightChild 9 PR SL normal033 0 8 245760 = cell040 := by
  calc
    rightChild 9 PR SL normal033 0 8 245760 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal033) 0 8 245760).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal033) 0 8 245760).symm
    _ = cell040 := by rfl
theorem normalized020 : AdaptiveCoverage.normalize SL cell040 = normal035 := by
  calc
    AdaptiveCoverage.normalize SL cell040 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell040)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell040)).symm
    _ = normal035 := by rfl
theorem left020 : leftChild 9 PR SL normal035 2 6 131072 = cell041 := by
  calc
    leftChild 9 PR SL normal035 2 6 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal035) 2 6 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal035) 2 6 131072).symm
    _ = cell041 := by rfl
theorem right020 : rightChild 9 PR SL normal035 2 6 131072 = cell042 := by
  calc
    rightChild 9 PR SL normal035 2 6 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal035) 2 6 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal035) 2 6 131072).symm
    _ = cell042 := by rfl
theorem normalized021 : AdaptiveCoverage.normalize SL cell042 = normal037 := by
  calc
    AdaptiveCoverage.normalize SL cell042 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell042)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell042)).symm
    _ = normal037 := by rfl
theorem left021 : leftChild 9 PR SL normal037 3 7 131072 = cell043 := by
  calc
    leftChild 9 PR SL normal037 3 7 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal037) 3 7 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal037) 3 7 131072).symm
    _ = cell043 := by rfl
theorem right021 : rightChild 9 PR SL normal037 3 7 131072 = cell044 := by
  calc
    rightChild 9 PR SL normal037 3 7 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal037) 3 7 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal037) 3 7 131072).symm
    _ = cell044 := by rfl
theorem normalized022 : AdaptiveCoverage.normalize SL cell044 = normal039 := by
  calc
    AdaptiveCoverage.normalize SL cell044 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell044)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell044)).symm
    _ = normal039 := by rfl
theorem left022 : leftChild 9 PR SL normal039 3 5 81920 = cell045 := by
  calc
    leftChild 9 PR SL normal039 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal039) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal039) 3 5 81920).symm
    _ = cell045 := by rfl
theorem right022 : rightChild 9 PR SL normal039 3 5 81920 = cell046 := by
  calc
    rightChild 9 PR SL normal039 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal039) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal039) 3 5 81920).symm
    _ = cell046 := by rfl
theorem normalized023 : AdaptiveCoverage.normalize SL cell045 = normal040 := by
  calc
    AdaptiveCoverage.normalize SL cell045 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell045)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell045)).symm
    _ = normal040 := by rfl
theorem left023 : leftChild 9 PR SL normal040 4 6 81920 = cell047 := by
  calc
    leftChild 9 PR SL normal040 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal040) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal040) 4 6 81920).symm
    _ = cell047 := by rfl
theorem right023 : rightChild 9 PR SL normal040 4 6 81920 = cell048 := by
  calc
    rightChild 9 PR SL normal040 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal040) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal040) 4 6 81920).symm
    _ = cell048 := by rfl

set_option pp.fullNames true
#print axioms normalized016
#print axioms left016
#print axioms right016
#print axioms normalized017
#print axioms left017
#print axioms right017
#print axioms normalized018
#print axioms left018
#print axioms right018
#print axioms normalized019
#print axioms left019
#print axioms right019
#print axioms normalized020
#print axioms left020
#print axioms right020
#print axioms normalized021
#print axioms left021
#print axioms right021
#print axioms normalized022
#print axioms left022
#print axioms right022
#print axioms normalized023
#print axioms left023
#print axioms right023
end StructuralGoal20261016.W10Aux478
end
