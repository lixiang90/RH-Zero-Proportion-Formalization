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
theorem normalized136 : AdaptiveCoverage.normalize SL cell271 = normal259 := by
  calc
    AdaptiveCoverage.normalize SL cell271 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell271)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell271)).symm
    _ = normal259 := by rfl
theorem left136 : leftChild 9 PR SL normal259 4 7 114688 = cell273 := by
  calc
    leftChild 9 PR SL normal259 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal259) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal259) 4 7 114688).symm
    _ = cell273 := by rfl
theorem right136 : rightChild 9 PR SL normal259 4 7 114688 = cell274 := by
  calc
    rightChild 9 PR SL normal259 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal259) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal259) 4 7 114688).symm
    _ = cell274 := by rfl
theorem normalized137 : AdaptiveCoverage.normalize SL cell274 = normal261 := by
  calc
    AdaptiveCoverage.normalize SL cell274 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell274)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell274)).symm
    _ = normal261 := by rfl
theorem left137 : leftChild 9 PR SL normal261 3 6 98304 = cell275 := by
  calc
    leftChild 9 PR SL normal261 3 6 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal261) 3 6 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal261) 3 6 98304).symm
    _ = cell275 := by rfl
theorem right137 : rightChild 9 PR SL normal261 3 6 98304 = cell276 := by
  calc
    rightChild 9 PR SL normal261 3 6 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal261) 3 6 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal261) 3 6 98304).symm
    _ = cell276 := by rfl
theorem normalized138 : AdaptiveCoverage.normalize SL cell276 = normal263 := by
  calc
    AdaptiveCoverage.normalize SL cell276 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell276)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell276)).symm
    _ = normal263 := by rfl
theorem left138 : leftChild 9 PR SL normal263 2 5 98304 = cell277 := by
  calc
    leftChild 9 PR SL normal263 2 5 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal263) 2 5 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal263) 2 5 98304).symm
    _ = cell277 := by rfl
theorem right138 : rightChild 9 PR SL normal263 2 5 98304 = cell278 := by
  calc
    rightChild 9 PR SL normal263 2 5 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal263) 2 5 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal263) 2 5 98304).symm
    _ = cell278 := by rfl
theorem normalized139 : AdaptiveCoverage.normalize SL cell278 = normal265 := by
  calc
    AdaptiveCoverage.normalize SL cell278 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell278)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell278)).symm
    _ = normal265 := by rfl
theorem left139 : leftChild 9 PR SL normal265 5 7 81920 = cell279 := by
  calc
    leftChild 9 PR SL normal265 5 7 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal265) 5 7 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal265) 5 7 81920).symm
    _ = cell279 := by rfl
theorem right139 : rightChild 9 PR SL normal265 5 7 81920 = cell280 := by
  calc
    rightChild 9 PR SL normal265 5 7 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal265) 5 7 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal265) 5 7 81920).symm
    _ = cell280 := by rfl
theorem normalized140 : AdaptiveCoverage.normalize SL cell280 = normal267 := by
  calc
    AdaptiveCoverage.normalize SL cell280 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell280)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell280)).symm
    _ = normal267 := by rfl
theorem left140 : leftChild 9 PR SL normal267 2 4 81920 = cell281 := by
  calc
    leftChild 9 PR SL normal267 2 4 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal267) 2 4 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal267) 2 4 81920).symm
    _ = cell281 := by rfl
theorem right140 : rightChild 9 PR SL normal267 2 4 81920 = cell282 := by
  calc
    rightChild 9 PR SL normal267 2 4 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal267) 2 4 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal267) 2 4 81920).symm
    _ = cell282 := by rfl
theorem normalized141 : AdaptiveCoverage.normalize SL cell281 = normal268 := by
  calc
    AdaptiveCoverage.normalize SL cell281 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell281)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell281)).symm
    _ = normal268 := by rfl
theorem left141 : leftChild 9 PR SL normal268 1 9 294912 = cell283 := by
  calc
    leftChild 9 PR SL normal268 1 9 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal268) 1 9 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal268) 1 9 294912).symm
    _ = cell283 := by rfl
theorem right141 : rightChild 9 PR SL normal268 1 9 294912 = cell284 := by
  calc
    rightChild 9 PR SL normal268 1 9 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal268) 1 9 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal268) 1 9 294912).symm
    _ = cell284 := by rfl
theorem normalized142 : AdaptiveCoverage.normalize SL cell284 = normal270 := by
  calc
    AdaptiveCoverage.normalize SL cell284 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell284)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell284)).symm
    _ = normal270 := by rfl
theorem left142 : leftChild 9 PR SL normal270 2 6 147456 = cell285 := by
  calc
    leftChild 9 PR SL normal270 2 6 147456 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal270) 2 6 147456).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal270) 2 6 147456).symm
    _ = cell285 := by rfl
theorem right142 : rightChild 9 PR SL normal270 2 6 147456 = cell286 := by
  calc
    rightChild 9 PR SL normal270 2 6 147456 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal270) 2 6 147456).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal270) 2 6 147456).symm
    _ = cell286 := by rfl
theorem normalized143 : AdaptiveCoverage.normalize SL cell270 = normal275 := by
  calc
    AdaptiveCoverage.normalize SL cell270 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell270)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell270)).symm
    _ = normal275 := by rfl
theorem left143 : leftChild 9 PR SL normal275 0 9 335872 = cell287 := by
  calc
    leftChild 9 PR SL normal275 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal275) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal275) 0 9 335872).symm
    _ = cell287 := by rfl
theorem right143 : rightChild 9 PR SL normal275 0 9 335872 = cell288 := by
  calc
    rightChild 9 PR SL normal275 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal275) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal275) 0 9 335872).symm
    _ = cell288 := by rfl

set_option pp.fullNames true
#print axioms normalized136
#print axioms left136
#print axioms right136
#print axioms normalized137
#print axioms left137
#print axioms right137
#print axioms normalized138
#print axioms left138
#print axioms right138
#print axioms normalized139
#print axioms left139
#print axioms right139
#print axioms normalized140
#print axioms left140
#print axioms right140
#print axioms normalized141
#print axioms left141
#print axioms right141
#print axioms normalized142
#print axioms left142
#print axioms right142
#print axioms normalized143
#print axioms left143
#print axioms right143
end StructuralGoal20261016.W10Aux478
end
