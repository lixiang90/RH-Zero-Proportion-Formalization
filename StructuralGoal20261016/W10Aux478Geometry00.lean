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
theorem root_eq : cell000 = RootBounds.initialCell := by rfl
theorem same_frozen_cell : selectedCell = ⟨[27852, 27852, 27852, 27852, 27852, 27852, 27852, 27852, 27852], [137632, 137632, 137632, 137632, 137632, 137632, 137632, 137632, 137632], [55704, 83556, 111408, 139260, 167112, 194964, 222816, 327680, 55704, 83556, 111408, 139260, 167112, 194964, 222816, 55704, 83556, 111408, 139260, 167112, 194964, 55704, 83556, 111408, 139260, 167112, 55704, 83556, 111408, 139260, 55704, 83556, 111408, 55704, 83556, 55704], [165484, 193336, 221188, 249040, 276892, 304744, 332596, 360448, 165484, 193336, 221188, 249040, 276892, 304744, 332596, 165484, 193336, 221188, 249040, 276892, 304744, 165484, 193336, 221188, 249040, 276892, 165484, 193336, 221188, 249040, 165484, 193336, 221188, 165484, 193336, 165484]⟩ := by rfl
theorem normalized000 : AdaptiveCoverage.normalize SL cell000 = normal000 := by
  calc
    AdaptiveCoverage.normalize SL cell000 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell000)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell000)).symm
    _ = normal000 := by rfl
theorem left000 : leftChild 9 PR SL normal000 0 9 458752 = cell001 := by
  calc
    leftChild 9 PR SL normal000 0 9 458752 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal000) 0 9 458752).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal000) 0 9 458752).symm
    _ = cell001 := by rfl
theorem right000 : rightChild 9 PR SL normal000 0 9 458752 = cell002 := by
  calc
    rightChild 9 PR SL normal000 0 9 458752 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal000) 0 9 458752).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal000) 0 9 458752).symm
    _ = cell002 := by rfl
theorem normalized001 : AdaptiveCoverage.normalize SL cell001 = normal001 := by
  calc
    AdaptiveCoverage.normalize SL cell001 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell001)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell001)).symm
    _ = normal001 := by rfl
theorem left001 : leftChild 9 PR SL normal001 0 9 360448 = cell003 := by
  calc
    leftChild 9 PR SL normal001 0 9 360448 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal001) 0 9 360448).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal001) 0 9 360448).symm
    _ = cell003 := by rfl
theorem right001 : rightChild 9 PR SL normal001 0 9 360448 = cell004 := by
  calc
    rightChild 9 PR SL normal001 0 9 360448 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal001) 0 9 360448).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal001) 0 9 360448).symm
    _ = cell004 := by rfl
theorem normalized002 : AdaptiveCoverage.normalize SL cell003 = normal002 := by
  calc
    AdaptiveCoverage.normalize SL cell003 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell003)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell003)).symm
    _ = normal002 := by rfl
theorem left002 : leftChild 9 PR SL normal002 0 9 311296 = cell005 := by
  calc
    leftChild 9 PR SL normal002 0 9 311296 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal002) 0 9 311296).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal002) 0 9 311296).symm
    _ = cell005 := by rfl
theorem right002 : rightChild 9 PR SL normal002 0 9 311296 = cell006 := by
  calc
    rightChild 9 PR SL normal002 0 9 311296 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal002) 0 9 311296).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal002) 0 9 311296).symm
    _ = cell006 := by rfl
theorem normalized003 : AdaptiveCoverage.normalize SL cell006 = normal003 := by
  calc
    AdaptiveCoverage.normalize SL cell006 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell006)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell006)).symm
    _ = normal003 := by rfl
theorem left003 : leftChild 9 PR SL normal003 0 9 327680 = cell007 := by
  calc
    leftChild 9 PR SL normal003 0 9 327680 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal003) 0 9 327680).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal003) 0 9 327680).symm
    _ = cell007 := by rfl
theorem right003 : rightChild 9 PR SL normal003 0 9 327680 = cell008 := by
  calc
    rightChild 9 PR SL normal003 0 9 327680 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal003) 0 9 327680).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal003) 0 9 327680).symm
    _ = cell008 := by rfl
theorem normalized004 : AdaptiveCoverage.normalize SL cell008 = normal004 := by
  calc
    AdaptiveCoverage.normalize SL cell008 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell008)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell008)).symm
    _ = normal004 := by rfl
theorem left004 : leftChild 9 PR SL normal004 0 8 278528 = cell009 := by
  calc
    leftChild 9 PR SL normal004 0 8 278528 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal004) 0 8 278528).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal004) 0 8 278528).symm
    _ = cell009 := by rfl
theorem right004 : rightChild 9 PR SL normal004 0 8 278528 = cell010 := by
  calc
    rightChild 9 PR SL normal004 0 8 278528 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal004) 0 8 278528).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal004) 0 8 278528).symm
    _ = cell010 := by rfl
theorem normalized005 : AdaptiveCoverage.normalize SL cell009 = normal005 := by
  calc
    AdaptiveCoverage.normalize SL cell009 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell009)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell009)).symm
    _ = normal005 := by rfl
theorem left005 : leftChild 9 PR SL normal005 1 9 294912 = cell011 := by
  calc
    leftChild 9 PR SL normal005 1 9 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal005) 1 9 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal005) 1 9 294912).symm
    _ = cell011 := by rfl
theorem right005 : rightChild 9 PR SL normal005 1 9 294912 = cell012 := by
  calc
    rightChild 9 PR SL normal005 1 9 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal005) 1 9 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal005) 1 9 294912).symm
    _ = cell012 := by rfl
theorem normalized006 : AdaptiveCoverage.normalize SL cell011 = normal006 := by
  calc
    AdaptiveCoverage.normalize SL cell011 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell011)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell011)).symm
    _ = normal006 := by rfl
theorem left006 : leftChild 9 PR SL normal006 0 9 344064 = cell013 := by
  calc
    leftChild 9 PR SL normal006 0 9 344064 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal006) 0 9 344064).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal006) 0 9 344064).symm
    _ = cell013 := by rfl
theorem right006 : rightChild 9 PR SL normal006 0 9 344064 = cell014 := by
  calc
    rightChild 9 PR SL normal006 0 9 344064 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal006) 0 9 344064).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal006) 0 9 344064).symm
    _ = cell014 := by rfl
theorem normalized007 : AdaptiveCoverage.normalize SL cell012 = normal009 := by
  calc
    AdaptiveCoverage.normalize SL cell012 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell012)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell012)).symm
    _ = normal009 := by rfl
theorem left007 : leftChild 9 PR SL normal009 0 9 344064 = cell015 := by
  calc
    leftChild 9 PR SL normal009 0 9 344064 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal009) 0 9 344064).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal009) 0 9 344064).symm
    _ = cell015 := by rfl
theorem right007 : rightChild 9 PR SL normal009 0 9 344064 = cell016 := by
  calc
    rightChild 9 PR SL normal009 0 9 344064 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal009) 0 9 344064).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal009) 0 9 344064).symm
    _ = cell016 := by rfl

set_option pp.fullNames true
#print axioms root_eq
#print axioms same_frozen_cell
#print axioms normalized000
#print axioms left000
#print axioms right000
#print axioms normalized001
#print axioms left001
#print axioms right001
#print axioms normalized002
#print axioms left002
#print axioms right002
#print axioms normalized003
#print axioms left003
#print axioms right003
#print axioms normalized004
#print axioms left004
#print axioms right004
#print axioms normalized005
#print axioms left005
#print axioms right005
#print axioms normalized006
#print axioms left006
#print axioms right006
#print axioms normalized007
#print axioms left007
#print axioms right007
end StructuralGoal20261016.W10Aux478
end
