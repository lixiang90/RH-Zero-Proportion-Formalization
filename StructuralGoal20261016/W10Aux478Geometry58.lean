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
theorem normalized464 : AdaptiveCoverage.normalize SL cell927 = normal915 := by
  calc
    AdaptiveCoverage.normalize SL cell927 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell927)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell927)).symm
    _ = normal915 := by rfl
theorem left464 : leftChild 9 PR SL normal915 2 6 140288 = cell929 := by
  calc
    leftChild 9 PR SL normal915 2 6 140288 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal915) 2 6 140288).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal915) 2 6 140288).symm
    _ = cell929 := by rfl
theorem right464 : rightChild 9 PR SL normal915 2 6 140288 = cell930 := by
  calc
    rightChild 9 PR SL normal915 2 6 140288 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal915) 2 6 140288).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal915) 2 6 140288).symm
    _ = cell930 := by rfl
theorem normalized465 : AdaptiveCoverage.normalize SL cell929 = normal916 := by
  calc
    AdaptiveCoverage.normalize SL cell929 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell929)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell929)).symm
    _ = normal916 := by rfl
theorem left465 : leftChild 9 PR SL normal916 0 8 310896 = cell931 := by
  calc
    leftChild 9 PR SL normal916 0 8 310896 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal916) 0 8 310896).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal916) 0 8 310896).symm
    _ = cell931 := by rfl
theorem right465 : rightChild 9 PR SL normal916 0 8 310896 = cell932 := by
  calc
    rightChild 9 PR SL normal916 0 8 310896 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal916) 0 8 310896).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal916) 0 8 310896).symm
    _ = cell932 := by rfl
theorem normalized466 : AdaptiveCoverage.normalize SL cell930 = normal919 := by
  calc
    AdaptiveCoverage.normalize SL cell930 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell930)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell930)).symm
    _ = normal919 := by rfl
theorem left466 : leftChild 9 PR SL normal919 3 7 140768 = cell933 := by
  calc
    leftChild 9 PR SL normal919 3 7 140768 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal919) 3 7 140768).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal919) 3 7 140768).symm
    _ = cell933 := by rfl
theorem right466 : rightChild 9 PR SL normal919 3 7 140768 = cell934 := by
  calc
    rightChild 9 PR SL normal919 3 7 140768 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal919) 3 7 140768).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal919) 3 7 140768).symm
    _ = cell934 := by rfl
theorem normalized467 : AdaptiveCoverage.normalize SL cell922 = normal925 := by
  calc
    AdaptiveCoverage.normalize SL cell922 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell922)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell922)).symm
    _ = normal925 := by rfl
theorem left467 : leftChild 9 PR SL normal925 3 7 136352 = cell935 := by
  calc
    leftChild 9 PR SL normal925 3 7 136352 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal925) 3 7 136352).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal925) 3 7 136352).symm
    _ = cell935 := by rfl
theorem right467 : rightChild 9 PR SL normal925 3 7 136352 = cell936 := by
  calc
    rightChild 9 PR SL normal925 3 7 136352 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal925) 3 7 136352).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal925) 3 7 136352).symm
    _ = cell936 := by rfl
theorem normalized468 : AdaptiveCoverage.normalize SL cell920 = normal928 := by
  calc
    AdaptiveCoverage.normalize SL cell920 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell920)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell920)).symm
    _ = normal928 := by rfl
theorem left468 : leftChild 9 PR SL normal928 2 6 136448 = cell937 := by
  calc
    leftChild 9 PR SL normal928 2 6 136448 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal928) 2 6 136448).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal928) 2 6 136448).symm
    _ = cell937 := by rfl
theorem right468 : rightChild 9 PR SL normal928 2 6 136448 = cell938 := by
  calc
    rightChild 9 PR SL normal928 2 6 136448 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal928) 2 6 136448).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal928) 2 6 136448).symm
    _ = cell938 := by rfl
theorem normalized469 : AdaptiveCoverage.normalize SL cell918 = normal931 := by
  calc
    AdaptiveCoverage.normalize SL cell918 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell918)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell918)).symm
    _ = normal931 := by rfl
theorem left469 : leftChild 9 PR SL normal931 3 7 136480 = cell939 := by
  calc
    leftChild 9 PR SL normal931 3 7 136480 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal931) 3 7 136480).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal931) 3 7 136480).symm
    _ = cell939 := by rfl
theorem right469 : rightChild 9 PR SL normal931 3 7 136480 = cell940 := by
  calc
    rightChild 9 PR SL normal931 3 7 136480 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal931) 3 7 136480).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal931) 3 7 136480).symm
    _ = cell940 := by rfl
theorem normalized470 : AdaptiveCoverage.normalize SL cell916 = normal934 := by
  calc
    AdaptiveCoverage.normalize SL cell916 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell916)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell916)).symm
    _ = normal934 := by rfl
theorem left470 : leftChild 9 PR SL normal934 3 7 138176 = cell941 := by
  calc
    leftChild 9 PR SL normal934 3 7 138176 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal934) 3 7 138176).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal934) 3 7 138176).symm
    _ = cell941 := by rfl
theorem right470 : rightChild 9 PR SL normal934 3 7 138176 = cell942 := by
  calc
    rightChild 9 PR SL normal934 3 7 138176 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal934) 3 7 138176).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal934) 3 7 138176).symm
    _ = cell942 := by rfl
theorem normalized471 : AdaptiveCoverage.normalize SL cell941 = normal935 := by
  calc
    AdaptiveCoverage.normalize SL cell941 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell941)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell941)).symm
    _ = normal935 := by rfl
theorem left471 : leftChild 9 PR SL normal935 2 6 135760 = cell943 := by
  calc
    leftChild 9 PR SL normal935 2 6 135760 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal935) 2 6 135760).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal935) 2 6 135760).symm
    _ = cell943 := by rfl
theorem right471 : rightChild 9 PR SL normal935 2 6 135760 = cell944 := by
  calc
    rightChild 9 PR SL normal935 2 6 135760 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal935) 2 6 135760).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal935) 2 6 135760).symm
    _ = cell944 := by rfl

set_option pp.fullNames true
#print axioms normalized464
#print axioms left464
#print axioms right464
#print axioms normalized465
#print axioms left465
#print axioms right465
#print axioms normalized466
#print axioms left466
#print axioms right466
#print axioms normalized467
#print axioms left467
#print axioms right467
#print axioms normalized468
#print axioms left468
#print axioms right468
#print axioms normalized469
#print axioms left469
#print axioms right469
#print axioms normalized470
#print axioms left470
#print axioms right470
#print axioms normalized471
#print axioms left471
#print axioms right471
end StructuralGoal20261016.W10Aux478
end
