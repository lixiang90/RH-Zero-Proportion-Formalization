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
theorem normalized376 : AdaptiveCoverage.normalize SL cell751 = normal747 := by
  calc
    AdaptiveCoverage.normalize SL cell751 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell751)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell751)).symm
    _ = normal747 := by rfl
theorem left376 : leftChild 9 PR SL normal747 7 8 49619 = cell753 := by
  calc
    leftChild 9 PR SL normal747 7 8 49619 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal747) 7 8 49619).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal747) 7 8 49619).symm
    _ = cell753 := by rfl
theorem right376 : rightChild 9 PR SL normal747 7 8 49619 = cell754 := by
  calc
    rightChild 9 PR SL normal747 7 8 49619 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal747) 7 8 49619).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal747) 7 8 49619).symm
    _ = cell754 := by rfl
theorem normalized377 : AdaptiveCoverage.normalize SL cell753 = normal748 := by
  calc
    AdaptiveCoverage.normalize SL cell753 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell753)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell753)).symm
    _ = normal748 := by rfl
theorem left377 : leftChild 9 PR SL normal748 1 2 49587 = cell755 := by
  calc
    leftChild 9 PR SL normal748 1 2 49587 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal748) 1 2 49587).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal748) 1 2 49587).symm
    _ = cell755 := by rfl
theorem right377 : rightChild 9 PR SL normal748 1 2 49587 = cell756 := by
  calc
    rightChild 9 PR SL normal748 1 2 49587 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal748) 1 2 49587).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal748) 1 2 49587).symm
    _ = cell756 := by rfl
theorem normalized378 : AdaptiveCoverage.normalize SL cell755 = normal749 := by
  calc
    AdaptiveCoverage.normalize SL cell755 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell755)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell755)).symm
    _ = normal749 := by rfl
theorem left378 : leftChild 9 PR SL normal749 2 3 49315 = cell757 := by
  calc
    leftChild 9 PR SL normal749 2 3 49315 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal749) 2 3 49315).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal749) 2 3 49315).symm
    _ = cell757 := by rfl
theorem right378 : rightChild 9 PR SL normal749 2 3 49315 = cell758 := by
  calc
    rightChild 9 PR SL normal749 2 3 49315 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal749) 2 3 49315).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal749) 2 3 49315).symm
    _ = cell758 := by rfl
theorem normalized379 : AdaptiveCoverage.normalize SL cell757 = normal750 := by
  calc
    AdaptiveCoverage.normalize SL cell757 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell757)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell757)).symm
    _ = normal750 := by rfl
theorem left379 : leftChild 9 PR SL normal750 6 7 49283 = cell759 := by
  calc
    leftChild 9 PR SL normal750 6 7 49283 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal750) 6 7 49283).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal750) 6 7 49283).symm
    _ = cell759 := by rfl
theorem right379 : rightChild 9 PR SL normal750 6 7 49283 = cell760 := by
  calc
    rightChild 9 PR SL normal750 6 7 49283 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal750) 6 7 49283).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal750) 6 7 49283).symm
    _ = cell760 := by rfl
theorem normalized380 : AdaptiveCoverage.normalize SL cell759 = normal751 := by
  calc
    AdaptiveCoverage.normalize SL cell759 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell759)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell759)).symm
    _ = normal751 := by rfl
theorem left380 : leftChild 9 PR SL normal751 3 4 48652 = cell761 := by
  calc
    leftChild 9 PR SL normal751 3 4 48652 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal751) 3 4 48652).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal751) 3 4 48652).symm
    _ = cell761 := by rfl
theorem right380 : rightChild 9 PR SL normal751 3 4 48652 = cell762 := by
  calc
    rightChild 9 PR SL normal751 3 4 48652 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal751) 3 4 48652).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal751) 3 4 48652).symm
    _ = cell762 := by rfl
theorem normalized381 : AdaptiveCoverage.normalize SL cell761 = normal752 := by
  calc
    AdaptiveCoverage.normalize SL cell761 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell761)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell761)).symm
    _ = normal752 := by rfl
theorem left381 : leftChild 9 PR SL normal752 5 6 48620 = cell763 := by
  calc
    leftChild 9 PR SL normal752 5 6 48620 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal752) 5 6 48620).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal752) 5 6 48620).symm
    _ = cell763 := by rfl
theorem right381 : rightChild 9 PR SL normal752 5 6 48620 = cell764 := by
  calc
    rightChild 9 PR SL normal752 5 6 48620 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal752) 5 6 48620).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal752) 5 6 48620).symm
    _ = cell764 := by rfl
theorem normalized382 : AdaptiveCoverage.normalize SL cell763 = normal753 := by
  calc
    AdaptiveCoverage.normalize SL cell763 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell763)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell763)).symm
    _ = normal753 := by rfl
theorem left382 : leftChild 9 PR SL normal753 4 5 48555 = cell765 := by
  calc
    leftChild 9 PR SL normal753 4 5 48555 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal753) 4 5 48555).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal753) 4 5 48555).symm
    _ = cell765 := by rfl
theorem right382 : rightChild 9 PR SL normal753 4 5 48555 = cell766 := by
  calc
    rightChild 9 PR SL normal753 4 5 48555 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal753) 4 5 48555).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal753) 4 5 48555).symm
    _ = cell766 := by rfl
theorem normalized383 : AdaptiveCoverage.normalize SL cell765 = normal754 := by
  calc
    AdaptiveCoverage.normalize SL cell765 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell765)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell765)).symm
    _ = normal754 := by rfl
theorem left383 : leftChild 9 PR SL normal754 2 6 140512 = cell767 := by
  calc
    leftChild 9 PR SL normal754 2 6 140512 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal754) 2 6 140512).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal754) 2 6 140512).symm
    _ = cell767 := by rfl
theorem right383 : rightChild 9 PR SL normal754 2 6 140512 = cell768 := by
  calc
    rightChild 9 PR SL normal754 2 6 140512 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal754) 2 6 140512).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal754) 2 6 140512).symm
    _ = cell768 := by rfl

set_option pp.fullNames true
#print axioms normalized376
#print axioms left376
#print axioms right376
#print axioms normalized377
#print axioms left377
#print axioms right377
#print axioms normalized378
#print axioms left378
#print axioms right378
#print axioms normalized379
#print axioms left379
#print axioms right379
#print axioms normalized380
#print axioms left380
#print axioms right380
#print axioms normalized381
#print axioms left381
#print axioms right381
#print axioms normalized382
#print axioms left382
#print axioms right382
#print axioms normalized383
#print axioms left383
#print axioms right383
end StructuralGoal20261016.W10Aux478
end
