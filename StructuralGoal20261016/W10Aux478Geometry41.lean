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
theorem normalized328 : AdaptiveCoverage.normalize SL cell655 = normal647 := by
  calc
    AdaptiveCoverage.normalize SL cell655 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell655)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell655)).symm
    _ = normal647 := by rfl
theorem left328 : leftChild 9 PR SL normal647 4 5 55099 = cell657 := by
  calc
    leftChild 9 PR SL normal647 4 5 55099 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal647) 4 5 55099).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal647) 4 5 55099).symm
    _ = cell657 := by rfl
theorem right328 : rightChild 9 PR SL normal647 4 5 55099 = cell658 := by
  calc
    rightChild 9 PR SL normal647 4 5 55099 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal647) 4 5 55099).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal647) 4 5 55099).symm
    _ = cell658 := by rfl
theorem normalized329 : AdaptiveCoverage.normalize SL cell657 = normal648 := by
  calc
    AdaptiveCoverage.normalize SL cell657 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell657)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell657)).symm
    _ = normal648 := by rfl
theorem left329 : leftChild 9 PR SL normal648 2 3 48336 = cell659 := by
  calc
    leftChild 9 PR SL normal648 2 3 48336 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal648) 2 3 48336).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal648) 2 3 48336).symm
    _ = cell659 := by rfl
theorem right329 : rightChild 9 PR SL normal648 2 3 48336 = cell660 := by
  calc
    rightChild 9 PR SL normal648 2 3 48336 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal648) 2 3 48336).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal648) 2 3 48336).symm
    _ = cell660 := by rfl
theorem normalized330 : AdaptiveCoverage.normalize SL cell659 = normal649 := by
  calc
    AdaptiveCoverage.normalize SL cell659 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell659)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell659)).symm
    _ = normal649 := by rfl
theorem left330 : leftChild 9 PR SL normal649 1 2 56208 = cell661 := by
  calc
    leftChild 9 PR SL normal649 1 2 56208 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal649) 1 2 56208).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal649) 1 2 56208).symm
    _ = cell661 := by rfl
theorem right330 : rightChild 9 PR SL normal649 1 2 56208 = cell662 := by
  calc
    rightChild 9 PR SL normal649 1 2 56208 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal649) 1 2 56208).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal649) 1 2 56208).symm
    _ = cell662 := by rfl
theorem normalized331 : AdaptiveCoverage.normalize SL cell074 = normal656 := by
  calc
    AdaptiveCoverage.normalize SL cell074 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell074)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell074)).symm
    _ = normal656 := by rfl
theorem left331 : leftChild 9 PR SL normal656 6 7 59296 = cell663 := by
  calc
    leftChild 9 PR SL normal656 6 7 59296 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal656) 6 7 59296).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal656) 6 7 59296).symm
    _ = cell663 := by rfl
theorem right331 : rightChild 9 PR SL normal656 6 7 59296 = cell664 := by
  calc
    rightChild 9 PR SL normal656 6 7 59296 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal656) 6 7 59296).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal656) 6 7 59296).symm
    _ = cell664 := by rfl
theorem normalized332 : AdaptiveCoverage.normalize SL cell663 = normal657 := by
  calc
    AdaptiveCoverage.normalize SL cell663 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell663)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell663)).symm
    _ = normal657 := by rfl
theorem left332 : leftChild 9 PR SL normal657 5 6 59238 = cell665 := by
  calc
    leftChild 9 PR SL normal657 5 6 59238 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal657) 5 6 59238).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal657) 5 6 59238).symm
    _ = cell665 := by rfl
theorem right332 : rightChild 9 PR SL normal657 5 6 59238 = cell666 := by
  calc
    rightChild 9 PR SL normal657 5 6 59238 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal657) 5 6 59238).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal657) 5 6 59238).symm
    _ = cell666 := by rfl
theorem normalized333 : AdaptiveCoverage.normalize SL cell665 = normal658 := by
  calc
    AdaptiveCoverage.normalize SL cell665 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell665)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell665)).symm
    _ = normal658 := by rfl
theorem left333 : leftChild 9 PR SL normal658 3 4 59222 = cell667 := by
  calc
    leftChild 9 PR SL normal658 3 4 59222 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal658) 3 4 59222).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal658) 3 4 59222).symm
    _ = cell667 := by rfl
theorem right333 : rightChild 9 PR SL normal658 3 4 59222 = cell668 := by
  calc
    rightChild 9 PR SL normal658 3 4 59222 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal658) 3 4 59222).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal658) 3 4 59222).symm
    _ = cell668 := by rfl
theorem normalized334 : AdaptiveCoverage.normalize SL cell667 = normal659 := by
  calc
    AdaptiveCoverage.normalize SL cell667 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell667)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell667)).symm
    _ = normal659 := by rfl
theorem left334 : leftChild 9 PR SL normal659 4 5 59211 = cell669 := by
  calc
    leftChild 9 PR SL normal659 4 5 59211 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal659) 4 5 59211).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal659) 4 5 59211).symm
    _ = cell669 := by rfl
theorem right334 : rightChild 9 PR SL normal659 4 5 59211 = cell670 := by
  calc
    rightChild 9 PR SL normal659 4 5 59211 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal659) 4 5 59211).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal659) 4 5 59211).symm
    _ = cell670 := by rfl
theorem normalized335 : AdaptiveCoverage.normalize SL cell664 = normal664 := by
  calc
    AdaptiveCoverage.normalize SL cell664 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell664)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell664)).symm
    _ = normal664 := by rfl
theorem left335 : leftChild 9 PR SL normal664 2 6 137856 = cell671 := by
  calc
    leftChild 9 PR SL normal664 2 6 137856 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal664) 2 6 137856).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal664) 2 6 137856).symm
    _ = cell671 := by rfl
theorem right335 : rightChild 9 PR SL normal664 2 6 137856 = cell672 := by
  calc
    rightChild 9 PR SL normal664 2 6 137856 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal664) 2 6 137856).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal664) 2 6 137856).symm
    _ = cell672 := by rfl

set_option pp.fullNames true
#print axioms normalized328
#print axioms left328
#print axioms right328
#print axioms normalized329
#print axioms left329
#print axioms right329
#print axioms normalized330
#print axioms left330
#print axioms right330
#print axioms normalized331
#print axioms left331
#print axioms right331
#print axioms normalized332
#print axioms left332
#print axioms right332
#print axioms normalized333
#print axioms left333
#print axioms right333
#print axioms normalized334
#print axioms left334
#print axioms right334
#print axioms normalized335
#print axioms left335
#print axioms right335
end StructuralGoal20261016.W10Aux478
end
