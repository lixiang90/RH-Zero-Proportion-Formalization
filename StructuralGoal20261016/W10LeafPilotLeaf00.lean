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
end StructuralGoal20261016.W10LeafPilot
end
