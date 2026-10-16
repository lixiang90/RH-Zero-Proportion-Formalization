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
theorem normalized432 : AdaptiveCoverage.normalize SL cell863 = normal852 := by
  calc
    AdaptiveCoverage.normalize SL cell863 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell863)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell863)).symm
    _ = normal852 := by rfl
theorem left432 : leftChild 9 PR SL normal852 4 5 47629 = cell865 := by
  calc
    leftChild 9 PR SL normal852 4 5 47629 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal852) 4 5 47629).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal852) 4 5 47629).symm
    _ = cell865 := by rfl
theorem right432 : rightChild 9 PR SL normal852 4 5 47629 = cell866 := by
  calc
    rightChild 9 PR SL normal852 4 5 47629 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal852) 4 5 47629).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal852) 4 5 47629).symm
    _ = cell866 := by rfl
theorem normalized433 : AdaptiveCoverage.normalize SL cell865 = normal853 := by
  calc
    AdaptiveCoverage.normalize SL cell865 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell865)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell865)).symm
    _ = normal853 := by rfl
theorem left433 : leftChild 9 PR SL normal853 3 7 140288 = cell867 := by
  calc
    leftChild 9 PR SL normal853 3 7 140288 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal853) 3 7 140288).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal853) 3 7 140288).symm
    _ = cell867 := by rfl
theorem right433 : rightChild 9 PR SL normal853 3 7 140288 = cell868 := by
  calc
    rightChild 9 PR SL normal853 3 7 140288 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal853) 3 7 140288).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal853) 3 7 140288).symm
    _ = cell868 := by rfl
theorem normalized434 : AdaptiveCoverage.normalize SL cell867 = normal854 := by
  calc
    AdaptiveCoverage.normalize SL cell867 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell867)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell867)).symm
    _ = normal854 := by rfl
theorem left434 : leftChild 9 PR SL normal854 1 9 310271 = cell869 := by
  calc
    leftChild 9 PR SL normal854 1 9 310271 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal854) 1 9 310271).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal854) 1 9 310271).symm
    _ = cell869 := by rfl
theorem right434 : rightChild 9 PR SL normal854 1 9 310271 = cell870 := by
  calc
    rightChild 9 PR SL normal854 1 9 310271 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal854) 1 9 310271).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal854) 1 9 310271).symm
    _ = cell870 := by rfl
theorem normalized435 : AdaptiveCoverage.normalize SL cell868 = normal857 := by
  calc
    AdaptiveCoverage.normalize SL cell868 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell868)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell868)).symm
    _ = normal857 := by rfl
theorem left435 : leftChild 9 PR SL normal857 2 6 174016 = cell871 := by
  calc
    leftChild 9 PR SL normal857 2 6 174016 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal857) 2 6 174016).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal857) 2 6 174016).symm
    _ = cell871 := by rfl
theorem right435 : rightChild 9 PR SL normal857 2 6 174016 = cell872 := by
  calc
    rightChild 9 PR SL normal857 2 6 174016 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal857) 2 6 174016).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal857) 2 6 174016).symm
    _ = cell872 := by rfl
theorem normalized436 : AdaptiveCoverage.normalize SL cell858 = normal864 := by
  calc
    AdaptiveCoverage.normalize SL cell858 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell858)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell858)).symm
    _ = normal864 := by rfl
theorem left436 : leftChild 9 PR SL normal864 3 7 137664 = cell873 := by
  calc
    leftChild 9 PR SL normal864 3 7 137664 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal864) 3 7 137664).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal864) 3 7 137664).symm
    _ = cell873 := by rfl
theorem right436 : rightChild 9 PR SL normal864 3 7 137664 = cell874 := by
  calc
    rightChild 9 PR SL normal864 3 7 137664 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal864) 3 7 137664).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal864) 3 7 137664).symm
    _ = cell874 := by rfl
theorem normalized437 : AdaptiveCoverage.normalize SL cell856 = normal867 := by
  calc
    AdaptiveCoverage.normalize SL cell856 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell856)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell856)).symm
    _ = normal867 := by rfl
theorem left437 : leftChild 9 PR SL normal867 3 7 136992 = cell875 := by
  calc
    leftChild 9 PR SL normal867 3 7 136992 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal867) 3 7 136992).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal867) 3 7 136992).symm
    _ = cell875 := by rfl
theorem right437 : rightChild 9 PR SL normal867 3 7 136992 = cell876 := by
  calc
    rightChild 9 PR SL normal867 3 7 136992 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal867) 3 7 136992).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal867) 3 7 136992).symm
    _ = cell876 := by rfl
theorem normalized438 : AdaptiveCoverage.normalize SL cell876 = normal869 := by
  calc
    AdaptiveCoverage.normalize SL cell876 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell876)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell876)).symm
    _ = normal869 := by rfl
theorem left438 : leftChild 9 PR SL normal869 3 8 171152 = cell877 := by
  calc
    leftChild 9 PR SL normal869 3 8 171152 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal869) 3 8 171152).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal869) 3 8 171152).symm
    _ = cell877 := by rfl
theorem right438 : rightChild 9 PR SL normal869 3 8 171152 = cell878 := by
  calc
    rightChild 9 PR SL normal869 3 8 171152 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal869) 3 8 171152).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal869) 3 8 171152).symm
    _ = cell878 := by rfl
theorem normalized439 : AdaptiveCoverage.normalize SL cell756 = normal872 := by
  calc
    AdaptiveCoverage.normalize SL cell756 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell756)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell756)).symm
    _ = normal872 := by rfl
theorem left439 : leftChild 9 PR SL normal872 8 9 49095 = cell879 := by
  calc
    leftChild 9 PR SL normal872 8 9 49095 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal872) 8 9 49095).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal872) 8 9 49095).symm
    _ = cell879 := by rfl
theorem right439 : rightChild 9 PR SL normal872 8 9 49095 = cell880 := by
  calc
    rightChild 9 PR SL normal872 8 9 49095 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal872) 8 9 49095).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal872) 8 9 49095).symm
    _ = cell880 := by rfl

set_option pp.fullNames true
#print axioms normalized432
#print axioms left432
#print axioms right432
#print axioms normalized433
#print axioms left433
#print axioms right433
#print axioms normalized434
#print axioms left434
#print axioms right434
#print axioms normalized435
#print axioms left435
#print axioms right435
#print axioms normalized436
#print axioms left436
#print axioms right436
#print axioms normalized437
#print axioms left437
#print axioms right437
#print axioms normalized438
#print axioms left438
#print axioms right438
#print axioms normalized439
#print axioms left439
#print axioms right439
end StructuralGoal20261016.W10Aux478
end
