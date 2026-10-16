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
theorem normalized160 : AdaptiveCoverage.normalize SL cell320 = normal307 := by
  calc
    AdaptiveCoverage.normalize SL cell320 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell320)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell320)).symm
    _ = normal307 := by rfl
theorem left160 : leftChild 9 PR SL normal307 5 7 81920 = cell321 := by
  calc
    leftChild 9 PR SL normal307 5 7 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal307) 5 7 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal307) 5 7 81920).symm
    _ = cell321 := by rfl
theorem right160 : rightChild 9 PR SL normal307 5 7 81920 = cell322 := by
  calc
    rightChild 9 PR SL normal307 5 7 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal307) 5 7 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal307) 5 7 81920).symm
    _ = cell322 := by rfl
theorem normalized161 : AdaptiveCoverage.normalize SL cell308 = normal314 := by
  calc
    AdaptiveCoverage.normalize SL cell308 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell308)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell308)).symm
    _ = normal314 := by rfl
theorem left161 : leftChild 9 PR SL normal314 3 5 81920 = cell323 := by
  calc
    leftChild 9 PR SL normal314 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal314) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal314) 3 5 81920).symm
    _ = cell323 := by rfl
theorem right161 : rightChild 9 PR SL normal314 3 5 81920 = cell324 := by
  calc
    rightChild 9 PR SL normal314 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal314) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal314) 3 5 81920).symm
    _ = cell324 := by rfl
theorem normalized162 : AdaptiveCoverage.normalize SL cell323 = normal315 := by
  calc
    AdaptiveCoverage.normalize SL cell323 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell323)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell323)).symm
    _ = normal315 := by rfl
theorem left162 : leftChild 9 PR SL normal315 4 6 81920 = cell325 := by
  calc
    leftChild 9 PR SL normal315 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal315) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal315) 4 6 81920).symm
    _ = cell325 := by rfl
theorem right162 : rightChild 9 PR SL normal315 4 6 81920 = cell326 := by
  calc
    rightChild 9 PR SL normal315 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal315) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal315) 4 6 81920).symm
    _ = cell326 := by rfl
theorem normalized163 : AdaptiveCoverage.normalize SL cell325 = normal316 := by
  calc
    AdaptiveCoverage.normalize SL cell325 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell325)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell325)).symm
    _ = normal316 := by rfl
theorem left163 : leftChild 9 PR SL normal316 0 9 335872 = cell327 := by
  calc
    leftChild 9 PR SL normal316 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal316) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal316) 0 9 335872).symm
    _ = cell327 := by rfl
theorem right163 : rightChild 9 PR SL normal316 0 9 335872 = cell328 := by
  calc
    rightChild 9 PR SL normal316 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal316) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal316) 0 9 335872).symm
    _ = cell328 := by rfl
theorem normalized164 : AdaptiveCoverage.normalize SL cell327 = normal317 := by
  calc
    AdaptiveCoverage.normalize SL cell327 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell327)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell327)).symm
    _ = normal317 := by rfl
theorem left164 : leftChild 9 PR SL normal317 4 7 114688 = cell329 := by
  calc
    leftChild 9 PR SL normal317 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal317) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal317) 4 7 114688).symm
    _ = cell329 := by rfl
theorem right164 : rightChild 9 PR SL normal317 4 7 114688 = cell330 := by
  calc
    rightChild 9 PR SL normal317 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal317) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal317) 4 7 114688).symm
    _ = cell330 := by rfl
theorem normalized165 : AdaptiveCoverage.normalize SL cell330 = normal319 := by
  calc
    AdaptiveCoverage.normalize SL cell330 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell330)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell330)).symm
    _ = normal319 := by rfl
theorem left165 : leftChild 9 PR SL normal319 3 6 98304 = cell331 := by
  calc
    leftChild 9 PR SL normal319 3 6 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal319) 3 6 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal319) 3 6 98304).symm
    _ = cell331 := by rfl
theorem right165 : rightChild 9 PR SL normal319 3 6 98304 = cell332 := by
  calc
    rightChild 9 PR SL normal319 3 6 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal319) 3 6 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal319) 3 6 98304).symm
    _ = cell332 := by rfl
theorem normalized166 : AdaptiveCoverage.normalize SL cell332 = normal321 := by
  calc
    AdaptiveCoverage.normalize SL cell332 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell332)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell332)).symm
    _ = normal321 := by rfl
theorem left166 : leftChild 9 PR SL normal321 2 5 98304 = cell333 := by
  calc
    leftChild 9 PR SL normal321 2 5 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal321) 2 5 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal321) 2 5 98304).symm
    _ = cell333 := by rfl
theorem right166 : rightChild 9 PR SL normal321 2 5 98304 = cell334 := by
  calc
    rightChild 9 PR SL normal321 2 5 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal321) 2 5 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal321) 2 5 98304).symm
    _ = cell334 := by rfl
theorem normalized167 : AdaptiveCoverage.normalize SL cell334 = normal323 := by
  calc
    AdaptiveCoverage.normalize SL cell334 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell334)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell334)).symm
    _ = normal323 := by rfl
theorem left167 : leftChild 9 PR SL normal323 5 7 81920 = cell335 := by
  calc
    leftChild 9 PR SL normal323 5 7 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal323) 5 7 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal323) 5 7 81920).symm
    _ = cell335 := by rfl
theorem right167 : rightChild 9 PR SL normal323 5 7 81920 = cell336 := by
  calc
    rightChild 9 PR SL normal323 5 7 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal323) 5 7 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal323) 5 7 81920).symm
    _ = cell336 := by rfl

set_option pp.fullNames true
#print axioms normalized160
#print axioms left160
#print axioms right160
#print axioms normalized161
#print axioms left161
#print axioms right161
#print axioms normalized162
#print axioms left162
#print axioms right162
#print axioms normalized163
#print axioms left163
#print axioms right163
#print axioms normalized164
#print axioms left164
#print axioms right164
#print axioms normalized165
#print axioms left165
#print axioms right165
#print axioms normalized166
#print axioms left166
#print axioms right166
#print axioms normalized167
#print axioms left167
#print axioms right167
end StructuralGoal20261016.W10Aux478
end
