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
theorem normalized408 : AdaptiveCoverage.normalize SL cell815 = normal804 := by
  calc
    AdaptiveCoverage.normalize SL cell815 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell815)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell815)).symm
    _ = normal804 := by rfl
theorem left408 : leftChild 9 PR SL normal804 4 5 47629 = cell817 := by
  calc
    leftChild 9 PR SL normal804 4 5 47629 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal804) 4 5 47629).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal804) 4 5 47629).symm
    _ = cell817 := by rfl
theorem right408 : rightChild 9 PR SL normal804 4 5 47629 = cell818 := by
  calc
    rightChild 9 PR SL normal804 4 5 47629 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal804) 4 5 47629).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal804) 4 5 47629).symm
    _ = cell818 := by rfl
theorem normalized409 : AdaptiveCoverage.normalize SL cell817 = normal805 := by
  calc
    AdaptiveCoverage.normalize SL cell817 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell817)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell817)).symm
    _ = normal805 := by rfl
theorem left409 : leftChild 9 PR SL normal805 2 6 173296 = cell819 := by
  calc
    leftChild 9 PR SL normal805 2 6 173296 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal805) 2 6 173296).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal805) 2 6 173296).symm
    _ = cell819 := by rfl
theorem right409 : rightChild 9 PR SL normal805 2 6 173296 = cell820 := by
  calc
    rightChild 9 PR SL normal805 2 6 173296 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal805) 2 6 173296).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal805) 2 6 173296).symm
    _ = cell820 := by rfl
theorem normalized410 : AdaptiveCoverage.normalize SL cell819 = normal806 := by
  calc
    AdaptiveCoverage.normalize SL cell819 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell819)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell819)).symm
    _ = normal806 := by rfl
theorem left410 : leftChild 9 PR SL normal806 1 9 309819 = cell821 := by
  calc
    leftChild 9 PR SL normal806 1 9 309819 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal806) 1 9 309819).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal806) 1 9 309819).symm
    _ = cell821 := by rfl
theorem right410 : rightChild 9 PR SL normal806 1 9 309819 = cell822 := by
  calc
    rightChild 9 PR SL normal806 1 9 309819 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal806) 1 9 309819).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal806) 1 9 309819).symm
    _ = cell822 := by rfl
theorem normalized411 : AdaptiveCoverage.normalize SL cell822 = normal808 := by
  calc
    AdaptiveCoverage.normalize SL cell822 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell822)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell822)).symm
    _ = normal808 := by rfl
theorem left411 : leftChild 9 PR SL normal808 0 8 310815 = cell823 := by
  calc
    leftChild 9 PR SL normal808 0 8 310815 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal808) 0 8 310815).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal808) 0 8 310815).symm
    _ = cell823 := by rfl
theorem right411 : rightChild 9 PR SL normal808 0 8 310815 = cell824 := by
  calc
    rightChild 9 PR SL normal808 0 8 310815 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal808) 0 8 310815).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal808) 0 8 310815).symm
    _ = cell824 := by rfl
theorem normalized412 : AdaptiveCoverage.normalize SL cell820 = normal811 := by
  calc
    AdaptiveCoverage.normalize SL cell820 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell820)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell820)).symm
    _ = normal811 := by rfl
theorem left412 : leftChild 9 PR SL normal811 3 7 174270 = cell825 := by
  calc
    leftChild 9 PR SL normal811 3 7 174270 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal811) 3 7 174270).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal811) 3 7 174270).symm
    _ = cell825 := by rfl
theorem right412 : rightChild 9 PR SL normal811 3 7 174270 = cell826 := by
  calc
    rightChild 9 PR SL normal811 3 7 174270 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal811) 3 7 174270).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal811) 3 7 174270).symm
    _ = cell826 := by rfl
theorem normalized413 : AdaptiveCoverage.normalize SL cell826 = normal813 := by
  calc
    AdaptiveCoverage.normalize SL cell826 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell826)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell826)).symm
    _ = normal813 := by rfl
theorem left413 : leftChild 9 PR SL normal813 3 6 140095 = cell827 := by
  calc
    leftChild 9 PR SL normal813 3 6 140095 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal813) 3 6 140095).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal813) 3 6 140095).symm
    _ = cell827 := by rfl
theorem right413 : rightChild 9 PR SL normal813 3 6 140095 = cell828 := by
  calc
    rightChild 9 PR SL normal813 3 6 140095 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal813) 3 6 140095).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal813) 3 6 140095).symm
    _ = cell828 := by rfl
theorem normalized414 : AdaptiveCoverage.normalize SL cell812 = normal819 := by
  calc
    AdaptiveCoverage.normalize SL cell812 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell812)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell812)).symm
    _ = normal819 := by rfl
theorem left414 : leftChild 9 PR SL normal819 4 8 136640 = cell829 := by
  calc
    leftChild 9 PR SL normal819 4 8 136640 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal819) 4 8 136640).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal819) 4 8 136640).symm
    _ = cell829 := by rfl
theorem right414 : rightChild 9 PR SL normal819 4 8 136640 = cell830 := by
  calc
    rightChild 9 PR SL normal819 4 8 136640 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal819) 4 8 136640).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal819) 4 8 136640).symm
    _ = cell830 := by rfl
theorem normalized415 : AdaptiveCoverage.normalize SL cell830 = normal821 := by
  calc
    AdaptiveCoverage.normalize SL cell830 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell830)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell830)).symm
    _ = normal821 := by rfl
theorem left415 : leftChild 9 PR SL normal821 4 7 102800 = cell831 := by
  calc
    leftChild 9 PR SL normal821 4 7 102800 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal821) 4 7 102800).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal821) 4 7 102800).symm
    _ = cell831 := by rfl
theorem right415 : rightChild 9 PR SL normal821 4 7 102800 = cell832 := by
  calc
    rightChild 9 PR SL normal821 4 7 102800 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal821) 4 7 102800).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal821) 4 7 102800).symm
    _ = cell832 := by rfl

set_option pp.fullNames true
#print axioms normalized408
#print axioms left408
#print axioms right408
#print axioms normalized409
#print axioms left409
#print axioms right409
#print axioms normalized410
#print axioms left410
#print axioms right410
#print axioms normalized411
#print axioms left411
#print axioms right411
#print axioms normalized412
#print axioms left412
#print axioms right412
#print axioms normalized413
#print axioms left413
#print axioms right413
#print axioms normalized414
#print axioms left414
#print axioms right414
#print axioms normalized415
#print axioms left415
#print axioms right415
end StructuralGoal20261016.W10Aux478
end
