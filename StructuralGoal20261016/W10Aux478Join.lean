/- Frozen 478-leaf W10 subtree; complete global coverage is not asserted. -/
import StructuralGoal20261016.W10Aux478Cover
import StructuralGoal20261016.W10Aux127Cover
import StructuralGoal20261016.LeanCoverPart000
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
theorem r000_exact : cell005 = StructuralGoal20261016.LeanCoverPart000.initialCell := by rfl

theorem r0010_exact : cell007 = StructuralGoal20261016.W10Aux127.selectedCell := by rfl

theorem r00_covered : CovBy 9 PR (Pg cN 9 BS TS) cell003 := by
  have h000 : CovBy 9 PR (Pg cN 9 BS TS) cell005 := by
    rw [r000_exact]
    exact StructuralGoal20261016.LeanCoverPart000.covered
  have h0010 : CovBy 9 PR (Pg cN 9 BS TS) cell007 := by
    rw [r0010_exact]
    exact StructuralGoal20261016.W10Aux127.selected_covered
  have h001 : CovBy 9 PR (Pg cN 9 BS TS) cell006 :=
    branch 0 9 327680 (by decide) (by decide) normalized003 left003 right003 h0010 selected_covered
  exact branch 0 9 311296 (by decide) (by decide) normalized002 left002 right002 h000 h001

theorem root_covered_of_outer_siblings
    (hr1 : CovBy 9 PR (Pg cN 9 BS TS) cell002)
    (hr01 : CovBy 9 PR (Pg cN 9 BS TS) cell004) :
    CovBy 9 PR (Pg cN 9 BS TS) RootBounds.initialCell := by
  have h0 : CovBy 9 PR (Pg cN 9 BS TS) cell001 :=
    branch 0 9 360448 (by decide) (by decide) normalized001 left001 right001 r00_covered hr01
  have hroot : CovBy 9 PR (Pg cN 9 BS TS) cell000 :=
    branch 0 9 458752 (by decide) (by decide) normalized000 left000 right000 h0 hr1
  simpa only [root_eq] using hroot

set_option pp.fullNames true
#print axioms r000_exact
#print axioms r0010_exact
#print axioms r00_covered
#print axioms root_covered_of_outer_siblings
end StructuralGoal20261016.W10Aux478
end
