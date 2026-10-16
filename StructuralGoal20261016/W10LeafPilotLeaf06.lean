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
end StructuralGoal20261016.W10LeafPilot
end
