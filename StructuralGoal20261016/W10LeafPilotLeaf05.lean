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
end StructuralGoal20261016.W10LeafPilot
end
