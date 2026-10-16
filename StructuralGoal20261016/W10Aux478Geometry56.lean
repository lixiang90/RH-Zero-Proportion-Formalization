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
theorem normalized448 : AdaptiveCoverage.normalize SL cell894 = normal883 := by
  calc
    AdaptiveCoverage.normalize SL cell894 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell894)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell894)).symm
    _ = normal883 := by rfl
theorem left448 : leftChild 9 PR SL normal883 3 7 140768 = cell897 := by
  calc
    leftChild 9 PR SL normal883 3 7 140768 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal883) 3 7 140768).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal883) 3 7 140768).symm
    _ = cell897 := by rfl
theorem right448 : rightChild 9 PR SL normal883 3 7 140768 = cell898 := by
  calc
    rightChild 9 PR SL normal883 3 7 140768 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal883) 3 7 140768).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal883) 3 7 140768).symm
    _ = cell898 := by rfl
theorem normalized449 : AdaptiveCoverage.normalize SL cell886 = normal889 := by
  calc
    AdaptiveCoverage.normalize SL cell886 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell886)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell886)).symm
    _ = normal889 := by rfl
theorem left449 : leftChild 9 PR SL normal889 3 7 136448 = cell899 := by
  calc
    leftChild 9 PR SL normal889 3 7 136448 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal889) 3 7 136448).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal889) 3 7 136448).symm
    _ = cell899 := by rfl
theorem right449 : rightChild 9 PR SL normal889 3 7 136448 = cell900 := by
  calc
    rightChild 9 PR SL normal889 3 7 136448 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal889) 3 7 136448).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal889) 3 7 136448).symm
    _ = cell900 := by rfl
theorem normalized450 : AdaptiveCoverage.normalize SL cell884 = normal892 := by
  calc
    AdaptiveCoverage.normalize SL cell884 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell884)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell884)).symm
    _ = normal892 := by rfl
theorem left450 : leftChild 9 PR SL normal892 2 6 136352 = cell901 := by
  calc
    leftChild 9 PR SL normal892 2 6 136352 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal892) 2 6 136352).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal892) 2 6 136352).symm
    _ = cell901 := by rfl
theorem right450 : rightChild 9 PR SL normal892 2 6 136352 = cell902 := by
  calc
    rightChild 9 PR SL normal892 2 6 136352 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal892) 2 6 136352).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal892) 2 6 136352).symm
    _ = cell902 := by rfl
theorem normalized451 : AdaptiveCoverage.normalize SL cell882 = normal895 := by
  calc
    AdaptiveCoverage.normalize SL cell882 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell882)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell882)).symm
    _ = normal895 := by rfl
theorem left451 : leftChild 9 PR SL normal895 2 6 138176 = cell903 := by
  calc
    leftChild 9 PR SL normal895 2 6 138176 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal895) 2 6 138176).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal895) 2 6 138176).symm
    _ = cell903 := by rfl
theorem right451 : rightChild 9 PR SL normal895 2 6 138176 = cell904 := by
  calc
    rightChild 9 PR SL normal895 2 6 138176 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal895) 2 6 138176).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal895) 2 6 138176).symm
    _ = cell904 := by rfl
theorem normalized452 : AdaptiveCoverage.normalize SL cell903 = normal896 := by
  calc
    AdaptiveCoverage.normalize SL cell903 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell903)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell903)).symm
    _ = normal896 := by rfl
theorem left452 : leftChild 9 PR SL normal896 3 7 135760 = cell905 := by
  calc
    leftChild 9 PR SL normal896 3 7 135760 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal896) 3 7 135760).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal896) 3 7 135760).symm
    _ = cell905 := by rfl
theorem right452 : rightChild 9 PR SL normal896 3 7 135760 = cell906 := by
  calc
    rightChild 9 PR SL normal896 3 7 135760 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal896) 3 7 135760).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal896) 3 7 135760).symm
    _ = cell906 := by rfl
theorem normalized453 : AdaptiveCoverage.normalize SL cell904 = normal899 := by
  calc
    AdaptiveCoverage.normalize SL cell904 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell904)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell904)).symm
    _ = normal899 := by rfl
theorem left453 : leftChild 9 PR SL normal899 3 7 138064 = cell907 := by
  calc
    leftChild 9 PR SL normal899 3 7 138064 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal899) 3 7 138064).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal899) 3 7 138064).symm
    _ = cell907 := by rfl
theorem right453 : rightChild 9 PR SL normal899 3 7 138064 = cell908 := by
  calc
    rightChild 9 PR SL normal899 3 7 138064 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal899) 3 7 138064).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal899) 3 7 138064).symm
    _ = cell908 := by rfl
theorem normalized454 : AdaptiveCoverage.normalize SL cell880 = normal902 := by
  calc
    AdaptiveCoverage.normalize SL cell880 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell880)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell880)).symm
    _ = normal902 := by rfl
theorem left454 : leftChild 9 PR SL normal902 2 6 137120 = cell909 := by
  calc
    leftChild 9 PR SL normal902 2 6 137120 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal902) 2 6 137120).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal902) 2 6 137120).symm
    _ = cell909 := by rfl
theorem right454 : rightChild 9 PR SL normal902 2 6 137120 = cell910 := by
  calc
    rightChild 9 PR SL normal902 2 6 137120 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal902) 2 6 137120).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal902) 2 6 137120).symm
    _ = cell910 := by rfl
theorem normalized455 : AdaptiveCoverage.normalize SL cell910 = normal904 := by
  calc
    AdaptiveCoverage.normalize SL cell910 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell910)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell910)).symm
    _ = normal904 := by rfl
theorem left455 : leftChild 9 PR SL normal904 3 7 137152 = cell911 := by
  calc
    leftChild 9 PR SL normal904 3 7 137152 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal904) 3 7 137152).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal904) 3 7 137152).symm
    _ = cell911 := by rfl
theorem right455 : rightChild 9 PR SL normal904 3 7 137152 = cell912 := by
  calc
    rightChild 9 PR SL normal904 3 7 137152 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal904) 3 7 137152).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal904) 3 7 137152).symm
    _ = cell912 := by rfl

set_option pp.fullNames true
#print axioms normalized448
#print axioms left448
#print axioms right448
#print axioms normalized449
#print axioms left449
#print axioms right449
#print axioms normalized450
#print axioms left450
#print axioms right450
#print axioms normalized451
#print axioms left451
#print axioms right451
#print axioms normalized452
#print axioms left452
#print axioms right452
#print axioms normalized453
#print axioms left453
#print axioms right453
#print axioms normalized454
#print axioms left454
#print axioms right454
#print axioms normalized455
#print axioms left455
#print axioms right455
end StructuralGoal20261016.W10Aux478
end
