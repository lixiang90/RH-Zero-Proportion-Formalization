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
end StructuralGoal20261016.W10LeafPilot
end
