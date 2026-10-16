/- Eight-leaf pilot only; complete W10 coverage is not asserted. -/
import StructuralGoal20261016.W10LeafPilotData
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
namespace StructuralGoal20261016.W10LeafPilotBatch
open StructuralGoal20261016.W10LeafPilot
theorem normalizedLeaf00 : AdaptiveCoverage.normalize SL cell035 = normal018 := by
  calc
    AdaptiveCoverage.normalize SL cell035 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell035)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell035)).symm
    _ = normal018 := by rfl

theorem numeric00 : ForcedCoverage2.dispatch (fun _ => payload00) normal018 46 = true := by
  decide +kernel

theorem coveredLeaf00 : CovBy 9 PR (Pg cN 9 BS TS) cell035 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf00]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload00) normal018 46 numeric00

set_option pp.fullNames true
#print axioms normalizedLeaf00
#print axioms numeric00
#print axioms coveredLeaf00

theorem normalizedLeaf01 : AdaptiveCoverage.normalize SL cell037 = normal020 := by
  calc
    AdaptiveCoverage.normalize SL cell037 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell037)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell037)).symm
    _ = normal020 := by rfl

theorem numeric01 : ForcedCoverage2.dispatch (fun _ => payload01) normal020 46 = true := by
  decide +kernel

theorem coveredLeaf01 : CovBy 9 PR (Pg cN 9 BS TS) cell037 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf01]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload01) normal020 46 numeric01

set_option pp.fullNames true
#print axioms normalizedLeaf01
#print axioms numeric01
#print axioms coveredLeaf01

theorem normalizedLeaf02 : AdaptiveCoverage.normalize SL cell039 = normal022 := by
  calc
    AdaptiveCoverage.normalize SL cell039 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell039)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell039)).symm
    _ = normal022 := by rfl

theorem numeric02 : ForcedCoverage2.dispatch (fun _ => payload02) normal022 46 = true := by
  decide +kernel

theorem coveredLeaf02 : CovBy 9 PR (Pg cN 9 BS TS) cell039 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf02]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload02) normal022 46 numeric02

set_option pp.fullNames true
#print axioms normalizedLeaf02
#print axioms numeric02
#print axioms coveredLeaf02

theorem normalizedLeaf03 : AdaptiveCoverage.normalize SL cell041 = normal024 := by
  calc
    AdaptiveCoverage.normalize SL cell041 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell041)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell041)).symm
    _ = normal024 := by rfl

theorem numeric03 : ForcedCoverage2.dispatch (fun _ => payload03) normal024 46 = true := by
  decide +kernel

theorem coveredLeaf03 : CovBy 9 PR (Pg cN 9 BS TS) cell041 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf03]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload03) normal024 46 numeric03

set_option pp.fullNames true
#print axioms normalizedLeaf03
#print axioms numeric03
#print axioms coveredLeaf03

theorem normalizedLeaf04 : AdaptiveCoverage.normalize SL cell043 = normal026 := by
  calc
    AdaptiveCoverage.normalize SL cell043 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell043)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell043)).symm
    _ = normal026 := by rfl

theorem numeric04 : ForcedCoverage2.dispatch (fun _ => payload04) normal026 46 = true := by
  decide +kernel

theorem coveredLeaf04 : CovBy 9 PR (Pg cN 9 BS TS) cell043 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf04]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload04) normal026 46 numeric04

set_option pp.fullNames true
#print axioms normalizedLeaf04
#print axioms numeric04
#print axioms coveredLeaf04

theorem normalizedLeaf05 : AdaptiveCoverage.normalize SL cell045 = normal028 := by
  calc
    AdaptiveCoverage.normalize SL cell045 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell045)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell045)).symm
    _ = normal028 := by rfl

theorem numeric05 : ForcedCoverage2.dispatch (fun _ => payload05) normal028 46 = true := by
  decide +kernel

theorem coveredLeaf05 : CovBy 9 PR (Pg cN 9 BS TS) cell045 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf05]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload05) normal028 46 numeric05

set_option pp.fullNames true
#print axioms normalizedLeaf05
#print axioms numeric05
#print axioms coveredLeaf05

theorem normalizedLeaf06 : AdaptiveCoverage.normalize SL cell046 = normal029 := by
  calc
    AdaptiveCoverage.normalize SL cell046 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell046)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell046)).symm
    _ = normal029 := by rfl

theorem numeric06 : ForcedCoverage2.dispatch (fun _ => payload06) normal029 46 = true := by
  decide +kernel

theorem coveredLeaf06 : CovBy 9 PR (Pg cN 9 BS TS) cell046 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf06]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload06) normal029 46 numeric06

set_option pp.fullNames true
#print axioms normalizedLeaf06
#print axioms numeric06
#print axioms coveredLeaf06

theorem normalizedLeaf07 : AdaptiveCoverage.normalize SL cell034 = normal030 := by
  calc
    AdaptiveCoverage.normalize SL cell034 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell034)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell034)).symm
    _ = normal030 := by rfl

theorem numeric07 : ForcedCoverage2.dispatch (fun _ => payload07) normal030 46 = true := by
  decide +kernel

theorem coveredLeaf07 : CovBy 9 PR (Pg cN 9 BS TS) cell034 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf07]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload07) normal030 46 numeric07

set_option pp.fullNames true
#print axioms normalizedLeaf07
#print axioms numeric07
#print axioms coveredLeaf07

end StructuralGoal20261016.W10LeafPilotBatch
end
