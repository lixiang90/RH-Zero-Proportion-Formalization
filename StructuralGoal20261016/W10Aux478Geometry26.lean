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
theorem normalized208 : AdaptiveCoverage.normalize SL cell415 = normal406 := by
  calc
    AdaptiveCoverage.normalize SL cell415 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell415)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell415)).symm
    _ = normal406 := by rfl
theorem left208 : leftChild 9 PR SL normal406 1 9 294912 = cell417 := by
  calc
    leftChild 9 PR SL normal406 1 9 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal406) 1 9 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal406) 1 9 294912).symm
    _ = cell417 := by rfl
theorem right208 : rightChild 9 PR SL normal406 1 9 294912 = cell418 := by
  calc
    rightChild 9 PR SL normal406 1 9 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal406) 1 9 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal406) 1 9 294912).symm
    _ = cell418 := by rfl
theorem normalized209 : AdaptiveCoverage.normalize SL cell417 = normal407 := by
  calc
    AdaptiveCoverage.normalize SL cell417 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell417)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell417)).symm
    _ = normal407 := by rfl
theorem left209 : leftChild 9 PR SL normal407 3 5 81920 = cell419 := by
  calc
    leftChild 9 PR SL normal407 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal407) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal407) 3 5 81920).symm
    _ = cell419 := by rfl
theorem right209 : rightChild 9 PR SL normal407 3 5 81920 = cell420 := by
  calc
    rightChild 9 PR SL normal407 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal407) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal407) 3 5 81920).symm
    _ = cell420 := by rfl
theorem normalized210 : AdaptiveCoverage.normalize SL cell419 = normal408 := by
  calc
    AdaptiveCoverage.normalize SL cell419 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell419)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell419)).symm
    _ = normal408 := by rfl
theorem left210 : leftChild 9 PR SL normal408 4 6 81920 = cell421 := by
  calc
    leftChild 9 PR SL normal408 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal408) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal408) 4 6 81920).symm
    _ = cell421 := by rfl
theorem right210 : rightChild 9 PR SL normal408 4 6 81920 = cell422 := by
  calc
    rightChild 9 PR SL normal408 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal408) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal408) 4 6 81920).symm
    _ = cell422 := by rfl
theorem normalized211 : AdaptiveCoverage.normalize SL cell421 = normal409 := by
  calc
    AdaptiveCoverage.normalize SL cell421 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell421)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell421)).symm
    _ = normal409 := by rfl
theorem left211 : leftChild 9 PR SL normal409 0 9 335872 = cell423 := by
  calc
    leftChild 9 PR SL normal409 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal409) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal409) 0 9 335872).symm
    _ = cell423 := by rfl
theorem right211 : rightChild 9 PR SL normal409 0 9 335872 = cell424 := by
  calc
    rightChild 9 PR SL normal409 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal409) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal409) 0 9 335872).symm
    _ = cell424 := by rfl
theorem normalized212 : AdaptiveCoverage.normalize SL cell423 = normal410 := by
  calc
    AdaptiveCoverage.normalize SL cell423 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell423)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell423)).symm
    _ = normal410 := by rfl
theorem left212 : leftChild 9 PR SL normal410 2 5 114688 = cell425 := by
  calc
    leftChild 9 PR SL normal410 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal410) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal410) 2 5 114688).symm
    _ = cell425 := by rfl
theorem right212 : rightChild 9 PR SL normal410 2 5 114688 = cell426 := by
  calc
    rightChild 9 PR SL normal410 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal410) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal410) 2 5 114688).symm
    _ = cell426 := by rfl
theorem normalized213 : AdaptiveCoverage.normalize SL cell426 = normal412 := by
  calc
    AdaptiveCoverage.normalize SL cell426 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell426)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell426)).symm
    _ = normal412 := by rfl
theorem left213 : leftChild 9 PR SL normal412 2 4 81920 = cell427 := by
  calc
    leftChild 9 PR SL normal412 2 4 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal412) 2 4 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal412) 2 4 81920).symm
    _ = cell427 := by rfl
theorem right213 : rightChild 9 PR SL normal412 2 4 81920 = cell428 := by
  calc
    rightChild 9 PR SL normal412 2 4 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal412) 2 4 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal412) 2 4 81920).symm
    _ = cell428 := by rfl
theorem normalized214 : AdaptiveCoverage.normalize SL cell418 = normal418 := by
  calc
    AdaptiveCoverage.normalize SL cell418 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell418)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell418)).symm
    _ = normal418 := by rfl
theorem left214 : leftChild 9 PR SL normal418 0 9 335872 = cell429 := by
  calc
    leftChild 9 PR SL normal418 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal418) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal418) 0 9 335872).symm
    _ = cell429 := by rfl
theorem right214 : rightChild 9 PR SL normal418 0 9 335872 = cell430 := by
  calc
    rightChild 9 PR SL normal418 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal418) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal418) 0 9 335872).symm
    _ = cell430 := by rfl
theorem normalized215 : AdaptiveCoverage.normalize SL cell429 = normal419 := by
  calc
    AdaptiveCoverage.normalize SL cell429 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell429)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell429)).symm
    _ = normal419 := by rfl
theorem left215 : leftChild 9 PR SL normal419 2 5 114688 = cell431 := by
  calc
    leftChild 9 PR SL normal419 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal419) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal419) 2 5 114688).symm
    _ = cell431 := by rfl
theorem right215 : rightChild 9 PR SL normal419 2 5 114688 = cell432 := by
  calc
    rightChild 9 PR SL normal419 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal419) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal419) 2 5 114688).symm
    _ = cell432 := by rfl

set_option pp.fullNames true
#print axioms normalized208
#print axioms left208
#print axioms right208
#print axioms normalized209
#print axioms left209
#print axioms right209
#print axioms normalized210
#print axioms left210
#print axioms right210
#print axioms normalized211
#print axioms left211
#print axioms right211
#print axioms normalized212
#print axioms left212
#print axioms right212
#print axioms normalized213
#print axioms left213
#print axioms right213
#print axioms normalized214
#print axioms left214
#print axioms right214
#print axioms normalized215
#print axioms left215
#print axioms right215
end StructuralGoal20261016.W10Aux478
end
