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
theorem normalized016 : AdaptiveCoverage.normalize SL cell032 = normal025 := by
  calc
    AdaptiveCoverage.normalize SL cell032 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell032)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell032)).symm
    _ = normal025 := by rfl
theorem left016 : leftChild 9 PR SL normal025 0 9 319488 = cell033 := by
  calc
    leftChild 9 PR SL normal025 0 9 319488 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal025) 0 9 319488).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal025) 0 9 319488).symm
    _ = cell033 := by rfl
theorem right016 : rightChild 9 PR SL normal025 0 9 319488 = cell034 := by
  calc
    rightChild 9 PR SL normal025 0 9 319488 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal025) 0 9 319488).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal025) 0 9 319488).symm
    _ = cell034 := by rfl
theorem normalized017 : AdaptiveCoverage.normalize SL cell034 = normal027 := by
  calc
    AdaptiveCoverage.normalize SL cell034 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell034)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell034)).symm
    _ = normal027 := by rfl
theorem left017 : leftChild 9 PR SL normal027 2 7 180224 = cell035 := by
  calc
    leftChild 9 PR SL normal027 2 7 180224 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal027) 2 7 180224).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal027) 2 7 180224).symm
    _ = cell035 := by rfl
theorem right017 : rightChild 9 PR SL normal027 2 7 180224 = cell036 := by
  calc
    rightChild 9 PR SL normal027 2 7 180224 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal027) 2 7 180224).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal027) 2 7 180224).symm
    _ = cell036 := by rfl
theorem normalized018 : AdaptiveCoverage.normalize SL cell035 = normal028 := by
  calc
    AdaptiveCoverage.normalize SL cell035 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell035)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell035)).symm
    _ = normal028 := by rfl
theorem left018 : leftChild 9 PR SL normal028 1 9 278528 = cell037 := by
  calc
    leftChild 9 PR SL normal028 1 9 278528 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal028) 1 9 278528).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal028) 1 9 278528).symm
    _ = cell037 := by rfl
theorem right018 : rightChild 9 PR SL normal028 1 9 278528 = cell038 := by
  calc
    rightChild 9 PR SL normal028 1 9 278528 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal028) 1 9 278528).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal028) 1 9 278528).symm
    _ = cell038 := by rfl
theorem normalized019 : AdaptiveCoverage.normalize SL cell038 = normal030 := by
  calc
    AdaptiveCoverage.normalize SL cell038 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell038)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell038)).symm
    _ = normal030 := by rfl
theorem left019 : leftChild 9 PR SL normal030 2 6 131072 = cell039 := by
  calc
    leftChild 9 PR SL normal030 2 6 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal030) 2 6 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal030) 2 6 131072).symm
    _ = cell039 := by rfl
theorem right019 : rightChild 9 PR SL normal030 2 6 131072 = cell040 := by
  calc
    rightChild 9 PR SL normal030 2 6 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal030) 2 6 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal030) 2 6 131072).symm
    _ = cell040 := by rfl
theorem normalized020 : AdaptiveCoverage.normalize SL cell040 = normal032 := by
  calc
    AdaptiveCoverage.normalize SL cell040 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell040)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell040)).symm
    _ = normal032 := by rfl
theorem left020 : leftChild 9 PR SL normal032 3 5 65536 = cell041 := by
  calc
    leftChild 9 PR SL normal032 3 5 65536 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal032) 3 5 65536).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal032) 3 5 65536).symm
    _ = cell041 := by rfl
theorem right020 : rightChild 9 PR SL normal032 3 5 65536 = cell042 := by
  calc
    rightChild 9 PR SL normal032 3 5 65536 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal032) 3 5 65536).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal032) 3 5 65536).symm
    _ = cell042 := by rfl
theorem normalized021 : AdaptiveCoverage.normalize SL cell042 = normal034 := by
  calc
    AdaptiveCoverage.normalize SL cell042 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell042)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell042)).symm
    _ = normal034 := by rfl
theorem left021 : leftChild 9 PR SL normal034 4 6 65536 = cell043 := by
  calc
    leftChild 9 PR SL normal034 4 6 65536 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal034) 4 6 65536).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal034) 4 6 65536).symm
    _ = cell043 := by rfl
theorem right021 : rightChild 9 PR SL normal034 4 6 65536 = cell044 := by
  calc
    rightChild 9 PR SL normal034 4 6 65536 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal034) 4 6 65536).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal034) 4 6 65536).symm
    _ = cell044 := by rfl
theorem normalized022 : AdaptiveCoverage.normalize SL cell044 = normal036 := by
  calc
    AdaptiveCoverage.normalize SL cell044 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell044)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell044)).symm
    _ = normal036 := by rfl
theorem left022 : leftChild 9 PR SL normal036 1 8 245760 = cell045 := by
  calc
    leftChild 9 PR SL normal036 1 8 245760 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal036) 1 8 245760).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal036) 1 8 245760).symm
    _ = cell045 := by rfl
theorem right022 : rightChild 9 PR SL normal036 1 8 245760 = cell046 := by
  calc
    rightChild 9 PR SL normal036 1 8 245760 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal036) 1 8 245760).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal036) 1 8 245760).symm
    _ = cell046 := by rfl
theorem normalized023 : AdaptiveCoverage.normalize SL cell046 = normal038 := by
  calc
    AdaptiveCoverage.normalize SL cell046 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell046)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell046)).symm
    _ = normal038 := by rfl
theorem left023 : leftChild 9 PR SL normal038 5 8 114688 = cell047 := by
  calc
    leftChild 9 PR SL normal038 5 8 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal038) 5 8 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal038) 5 8 114688).symm
    _ = cell047 := by rfl
theorem right023 : rightChild 9 PR SL normal038 5 8 114688 = cell048 := by
  calc
    rightChild 9 PR SL normal038 5 8 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal038) 5 8 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal038) 5 8 114688).symm
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
end StructuralGoal20261016.W10Aux127
end
