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
end StructuralGoal20261016.W10LeafPilot
end
