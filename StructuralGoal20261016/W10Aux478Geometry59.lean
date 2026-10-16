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
theorem normalized472 : AdaptiveCoverage.normalize SL cell942 = normal938 := by
  calc
    AdaptiveCoverage.normalize SL cell942 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell942)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell942)).symm
    _ = normal938 := by rfl
theorem left472 : leftChild 9 PR SL normal938 2 6 138064 = cell945 := by
  calc
    leftChild 9 PR SL normal938 2 6 138064 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal938) 2 6 138064).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal938) 2 6 138064).symm
    _ = cell945 := by rfl
theorem right472 : rightChild 9 PR SL normal938 2 6 138064 = cell946 := by
  calc
    rightChild 9 PR SL normal938 2 6 138064 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal938) 2 6 138064).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal938) 2 6 138064).symm
    _ = cell946 := by rfl
theorem normalized473 : AdaptiveCoverage.normalize SL cell914 = normal941 := by
  calc
    AdaptiveCoverage.normalize SL cell914 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell914)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell914)).symm
    _ = normal941 := by rfl
theorem left473 : leftChild 9 PR SL normal941 3 7 137248 = cell947 := by
  calc
    leftChild 9 PR SL normal941 3 7 137248 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal941) 3 7 137248).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal941) 3 7 137248).symm
    _ = cell947 := by rfl
theorem right473 : rightChild 9 PR SL normal941 3 7 137248 = cell948 := by
  calc
    rightChild 9 PR SL normal941 3 7 137248 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal941) 3 7 137248).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal941) 3 7 137248).symm
    _ = cell948 := by rfl
theorem normalized474 : AdaptiveCoverage.normalize SL cell947 = normal942 := by
  calc
    AdaptiveCoverage.normalize SL cell947 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell947)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell947)).symm
    _ = normal942 := by rfl
theorem left474 : leftChild 9 PR SL normal942 2 6 135280 = cell949 := by
  calc
    leftChild 9 PR SL normal942 2 6 135280 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal942) 2 6 135280).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal942) 2 6 135280).symm
    _ = cell949 := by rfl
theorem right474 : rightChild 9 PR SL normal942 2 6 135280 = cell950 := by
  calc
    rightChild 9 PR SL normal942 2 6 135280 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal942) 2 6 135280).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal942) 2 6 135280).symm
    _ = cell950 := by rfl
theorem normalized475 : AdaptiveCoverage.normalize SL cell948 = normal945 := by
  calc
    AdaptiveCoverage.normalize SL cell948 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell948)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell948)).symm
    _ = normal945 := by rfl
theorem left475 : leftChild 9 PR SL normal945 2 6 137344 = cell951 := by
  calc
    leftChild 9 PR SL normal945 2 6 137344 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal945) 2 6 137344).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal945) 2 6 137344).symm
    _ = cell951 := by rfl
theorem right475 : rightChild 9 PR SL normal945 2 6 137344 = cell952 := by
  calc
    rightChild 9 PR SL normal945 2 6 137344 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal945) 2 6 137344).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal945) 2 6 137344).symm
    _ = cell952 := by rfl
theorem normalized476 : AdaptiveCoverage.normalize SL cell752 = normal948 := by
  calc
    AdaptiveCoverage.normalize SL cell752 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell752)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell752)).symm
    _ = normal948 := by rfl
theorem left476 : leftChild 9 PR SL normal948 2 6 137184 = cell953 := by
  calc
    leftChild 9 PR SL normal948 2 6 137184 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal948) 2 6 137184).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal948) 2 6 137184).symm
    _ = cell953 := by rfl
theorem right476 : rightChild 9 PR SL normal948 2 6 137184 = cell954 := by
  calc
    rightChild 9 PR SL normal948 2 6 137184 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal948) 2 6 137184).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal948) 2 6 137184).symm
    _ = cell954 := by rfl
theorem normalized477 : AdaptiveCoverage.normalize SL cell953 = normal949 := by
  calc
    AdaptiveCoverage.normalize SL cell953 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell953)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell953)).symm
    _ = normal949 := by rfl
theorem left477 : leftChild 9 PR SL normal949 1 8 237103 = cell955 := by
  calc
    leftChild 9 PR SL normal949 1 8 237103 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal949) 1 8 237103).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal949) 1 8 237103).symm
    _ = cell955 := by rfl
theorem right477 : rightChild 9 PR SL normal949 1 8 237103 = cell956 := by
  calc
    rightChild 9 PR SL normal949 1 8 237103 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal949) 1 8 237103).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal949) 1 8 237103).symm
    _ = cell956 := by rfl
theorem normalized478 : AdaptiveCoverage.normalize SL cell956 = normal951 := by
  calc
    AdaptiveCoverage.normalize SL cell956 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell956)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell956)).symm
    _ = normal951 := by rfl
theorem left478 : leftChild 9 PR SL normal951 1 8 248777 = cell957 := by
  calc
    leftChild 9 PR SL normal951 1 8 248777 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal951) 1 8 248777).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal951) 1 8 248777).symm
    _ = cell957 := by rfl
theorem right478 : rightChild 9 PR SL normal951 1 8 248777 = cell958 := by
  calc
    rightChild 9 PR SL normal951 1 8 248777 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal951) 1 8 248777).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal951) 1 8 248777).symm
    _ = cell958 := by rfl
theorem normalized479 : AdaptiveCoverage.normalize SL cell954 = normal954 := by
  calc
    AdaptiveCoverage.normalize SL cell954 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell954)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell954)).symm
    _ = normal954 := by rfl
theorem left479 : leftChild 9 PR SL normal954 3 7 137280 = cell959 := by
  calc
    leftChild 9 PR SL normal954 3 7 137280 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal954) 3 7 137280).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal954) 3 7 137280).symm
    _ = cell959 := by rfl
theorem right479 : rightChild 9 PR SL normal954 3 7 137280 = cell960 := by
  calc
    rightChild 9 PR SL normal954 3 7 137280 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal954) 3 7 137280).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal954) 3 7 137280).symm
    _ = cell960 := by rfl

set_option pp.fullNames true
#print axioms normalized472
#print axioms left472
#print axioms right472
#print axioms normalized473
#print axioms left473
#print axioms right473
#print axioms normalized474
#print axioms left474
#print axioms right474
#print axioms normalized475
#print axioms left475
#print axioms right475
#print axioms normalized476
#print axioms left476
#print axioms right476
#print axioms normalized477
#print axioms left477
#print axioms right477
#print axioms normalized478
#print axioms left478
#print axioms right478
#print axioms normalized479
#print axioms left479
#print axioms right479
end StructuralGoal20261016.W10Aux478
end
