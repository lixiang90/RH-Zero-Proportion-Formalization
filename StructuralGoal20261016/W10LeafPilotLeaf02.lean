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
end StructuralGoal20261016.W10LeafPilot
end
