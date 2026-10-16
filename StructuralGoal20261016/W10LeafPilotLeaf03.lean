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
namespace StructuralGoal20261016.W10LeafPilot
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
end StructuralGoal20261016.W10LeafPilot
end
