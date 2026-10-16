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
theorem normalized320 : AdaptiveCoverage.normalize SL cell639 = normal630 := by
  calc
    AdaptiveCoverage.normalize SL cell639 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell639)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell639)).symm
    _ = normal630 := by rfl
theorem left320 : leftChild 9 PR SL normal630 4 5 60251 = cell641 := by
  calc
    leftChild 9 PR SL normal630 4 5 60251 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal630) 4 5 60251).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal630) 4 5 60251).symm
    _ = cell641 := by rfl
theorem right320 : rightChild 9 PR SL normal630 4 5 60251 = cell642 := by
  calc
    rightChild 9 PR SL normal630 4 5 60251 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal630) 4 5 60251).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal630) 4 5 60251).symm
    _ = cell642 := by rfl
theorem normalized321 : AdaptiveCoverage.normalize SL cell568 = normal634 := by
  calc
    AdaptiveCoverage.normalize SL cell568 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell568)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell568)).symm
    _ = normal634 := by rfl
theorem left321 : leftChild 9 PR SL normal634 3 4 55158 = cell643 := by
  calc
    leftChild 9 PR SL normal634 3 4 55158 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal634) 3 4 55158).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal634) 3 4 55158).symm
    _ = cell643 := by rfl
theorem right321 : rightChild 9 PR SL normal634 3 4 55158 = cell644 := by
  calc
    rightChild 9 PR SL normal634 3 4 55158 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal634) 3 4 55158).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal634) 3 4 55158).symm
    _ = cell644 := by rfl
theorem normalized322 : AdaptiveCoverage.normalize SL cell643 = normal635 := by
  calc
    AdaptiveCoverage.normalize SL cell643 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell643)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell643)).symm
    _ = normal635 := by rfl
theorem left322 : leftChild 9 PR SL normal635 5 6 55243 = cell645 := by
  calc
    leftChild 9 PR SL normal635 5 6 55243 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal635) 5 6 55243).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal635) 5 6 55243).symm
    _ = cell645 := by rfl
theorem right322 : rightChild 9 PR SL normal635 5 6 55243 = cell646 := by
  calc
    rightChild 9 PR SL normal635 5 6 55243 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal635) 5 6 55243).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal635) 5 6 55243).symm
    _ = cell646 := by rfl
theorem normalized323 : AdaptiveCoverage.normalize SL cell645 = normal636 := by
  calc
    AdaptiveCoverage.normalize SL cell645 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell645)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell645)).symm
    _ = normal636 := by rfl
theorem left323 : leftChild 9 PR SL normal636 4 5 55099 = cell647 := by
  calc
    leftChild 9 PR SL normal636 4 5 55099 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal636) 4 5 55099).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal636) 4 5 55099).symm
    _ = cell647 := by rfl
theorem right323 : rightChild 9 PR SL normal636 4 5 55099 = cell648 := by
  calc
    rightChild 9 PR SL normal636 4 5 55099 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal636) 4 5 55099).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal636) 4 5 55099).symm
    _ = cell648 := by rfl
theorem normalized324 : AdaptiveCoverage.normalize SL cell647 = normal637 := by
  calc
    AdaptiveCoverage.normalize SL cell647 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell647)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell647)).symm
    _ = normal637 := by rfl
theorem left324 : leftChild 9 PR SL normal637 6 7 48336 = cell649 := by
  calc
    leftChild 9 PR SL normal637 6 7 48336 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal637) 6 7 48336).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal637) 6 7 48336).symm
    _ = cell649 := by rfl
theorem right324 : rightChild 9 PR SL normal637 6 7 48336 = cell650 := by
  calc
    rightChild 9 PR SL normal637 6 7 48336 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal637) 6 7 48336).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal637) 6 7 48336).symm
    _ = cell650 := by rfl
theorem normalized325 : AdaptiveCoverage.normalize SL cell649 = normal638 := by
  calc
    AdaptiveCoverage.normalize SL cell649 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell649)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell649)).symm
    _ = normal638 := by rfl
theorem left325 : leftChild 9 PR SL normal638 7 8 56208 = cell651 := by
  calc
    leftChild 9 PR SL normal638 7 8 56208 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal638) 7 8 56208).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal638) 7 8 56208).symm
    _ = cell651 := by rfl
theorem right325 : rightChild 9 PR SL normal638 7 8 56208 = cell652 := by
  calc
    rightChild 9 PR SL normal638 7 8 56208 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal638) 7 8 56208).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal638) 7 8 56208).symm
    _ = cell652 := by rfl
theorem normalized326 : AdaptiveCoverage.normalize SL cell566 = normal645 := by
  calc
    AdaptiveCoverage.normalize SL cell566 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell566)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell566)).symm
    _ = normal645 := by rfl
theorem left326 : leftChild 9 PR SL normal645 3 4 55158 = cell653 := by
  calc
    leftChild 9 PR SL normal645 3 4 55158 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal645) 3 4 55158).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal645) 3 4 55158).symm
    _ = cell653 := by rfl
theorem right326 : rightChild 9 PR SL normal645 3 4 55158 = cell654 := by
  calc
    rightChild 9 PR SL normal645 3 4 55158 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal645) 3 4 55158).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal645) 3 4 55158).symm
    _ = cell654 := by rfl
theorem normalized327 : AdaptiveCoverage.normalize SL cell653 = normal646 := by
  calc
    AdaptiveCoverage.normalize SL cell653 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell653)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell653)).symm
    _ = normal646 := by rfl
theorem left327 : leftChild 9 PR SL normal646 5 6 55158 = cell655 := by
  calc
    leftChild 9 PR SL normal646 5 6 55158 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal646) 5 6 55158).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal646) 5 6 55158).symm
    _ = cell655 := by rfl
theorem right327 : rightChild 9 PR SL normal646 5 6 55158 = cell656 := by
  calc
    rightChild 9 PR SL normal646 5 6 55158 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal646) 5 6 55158).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal646) 5 6 55158).symm
    _ = cell656 := by rfl

set_option pp.fullNames true
#print axioms normalized320
#print axioms left320
#print axioms right320
#print axioms normalized321
#print axioms left321
#print axioms right321
#print axioms normalized322
#print axioms left322
#print axioms right322
#print axioms normalized323
#print axioms left323
#print axioms right323
#print axioms normalized324
#print axioms left324
#print axioms right324
#print axioms normalized325
#print axioms left325
#print axioms right325
#print axioms normalized326
#print axioms left326
#print axioms right326
#print axioms normalized327
#print axioms left327
#print axioms right327
end StructuralGoal20261016.W10Aux478
end
