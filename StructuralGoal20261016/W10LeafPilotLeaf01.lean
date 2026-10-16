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
end StructuralGoal20261016.W10LeafPilot
end
