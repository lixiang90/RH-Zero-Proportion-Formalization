/- Frozen 478-leaf W10 subtree; complete global coverage is not asserted. -/
import StructuralGoal20261016.W10Aux478Data
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
theorem normalizedLeaf320 : AdaptiveCoverage.normalize SL cell662 = normal651 := by
  calc
    AdaptiveCoverage.normalize SL cell662 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell662)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell662)).symm
    _ = normal651 := by rfl

theorem numeric320 : ForcedCoverage2.dispatch (fun _ => payload320) normal651 46 = true := by
  decide +kernel

theorem coveredLeaf320 : CovBy 9 PR (Pg cN 9 BS TS) cell662 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf320]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload320) normal651 46 numeric320
theorem normalizedLeaf321 : AdaptiveCoverage.normalize SL cell660 = normal652 := by
  calc
    AdaptiveCoverage.normalize SL cell660 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell660)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell660)).symm
    _ = normal652 := by rfl

theorem numeric321 : ForcedCoverage2.dispatch (fun _ => payload321) normal652 46 = true := by
  decide +kernel

theorem coveredLeaf321 : CovBy 9 PR (Pg cN 9 BS TS) cell660 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf321]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload321) normal652 46 numeric321
theorem normalizedLeaf322 : AdaptiveCoverage.normalize SL cell658 = normal653 := by
  calc
    AdaptiveCoverage.normalize SL cell658 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell658)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell658)).symm
    _ = normal653 := by rfl

theorem numeric322 : ForcedCoverage2.dispatch (fun _ => payload322) normal653 46 = true := by
  decide +kernel

theorem coveredLeaf322 : CovBy 9 PR (Pg cN 9 BS TS) cell658 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf322]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload322) normal653 46 numeric322
theorem normalizedLeaf323 : AdaptiveCoverage.normalize SL cell656 = normal654 := by
  calc
    AdaptiveCoverage.normalize SL cell656 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell656)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell656)).symm
    _ = normal654 := by rfl

theorem numeric323 : ForcedCoverage2.dispatch (fun _ => payload323) normal654 46 = true := by
  decide +kernel

theorem coveredLeaf323 : CovBy 9 PR (Pg cN 9 BS TS) cell656 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf323]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload323) normal654 46 numeric323
theorem normalizedLeaf324 : AdaptiveCoverage.normalize SL cell654 = normal655 := by
  calc
    AdaptiveCoverage.normalize SL cell654 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell654)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell654)).symm
    _ = normal655 := by rfl

theorem numeric324 : ForcedCoverage2.dispatch (fun _ => payload324) normal655 46 = true := by
  decide +kernel

theorem coveredLeaf324 : CovBy 9 PR (Pg cN 9 BS TS) cell654 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf324]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload324) normal655 46 numeric324
theorem normalizedLeaf325 : AdaptiveCoverage.normalize SL cell669 = normal660 := by
  calc
    AdaptiveCoverage.normalize SL cell669 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell669)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell669)).symm
    _ = normal660 := by rfl

theorem numeric325 : ForcedCoverage2.dispatch (fun _ => payload325) normal660 46 = true := by
  decide +kernel

theorem coveredLeaf325 : CovBy 9 PR (Pg cN 9 BS TS) cell669 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf325]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload325) normal660 46 numeric325
theorem normalizedLeaf326 : AdaptiveCoverage.normalize SL cell670 = normal661 := by
  calc
    AdaptiveCoverage.normalize SL cell670 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell670)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell670)).symm
    _ = normal661 := by rfl

theorem numeric326 : ForcedCoverage2.dispatch (fun _ => payload326) normal661 46 = true := by
  decide +kernel

theorem coveredLeaf326 : CovBy 9 PR (Pg cN 9 BS TS) cell670 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf326]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload326) normal661 46 numeric326
theorem normalizedLeaf327 : AdaptiveCoverage.normalize SL cell668 = normal662 := by
  calc
    AdaptiveCoverage.normalize SL cell668 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell668)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell668)).symm
    _ = normal662 := by rfl

theorem numeric327 : ForcedCoverage2.dispatch (fun _ => payload327) normal662 46 = true := by
  decide +kernel

theorem coveredLeaf327 : CovBy 9 PR (Pg cN 9 BS TS) cell668 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf327]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload327) normal662 46 numeric327
theorem normalizedLeaf328 : AdaptiveCoverage.normalize SL cell666 = normal663 := by
  calc
    AdaptiveCoverage.normalize SL cell666 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell666)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell666)).symm
    _ = normal663 := by rfl

theorem numeric328 : ForcedCoverage2.dispatch (fun _ => payload328) normal663 46 = true := by
  decide +kernel

theorem coveredLeaf328 : CovBy 9 PR (Pg cN 9 BS TS) cell666 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf328]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload328) normal663 46 numeric328
theorem normalizedLeaf329 : AdaptiveCoverage.normalize SL cell673 = normal666 := by
  calc
    AdaptiveCoverage.normalize SL cell673 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell673)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell673)).symm
    _ = normal666 := by rfl

theorem numeric329 : ForcedCoverage2.dispatch (fun _ => payload329) normal666 46 = true := by
  decide +kernel

theorem coveredLeaf329 : CovBy 9 PR (Pg cN 9 BS TS) cell673 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf329]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload329) normal666 46 numeric329
theorem normalizedLeaf330 : AdaptiveCoverage.normalize SL cell674 = normal667 := by
  calc
    AdaptiveCoverage.normalize SL cell674 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell674)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell674)).symm
    _ = normal667 := by rfl

theorem numeric330 : ForcedCoverage2.dispatch (fun _ => payload330) normal667 46 = true := by
  decide +kernel

theorem coveredLeaf330 : CovBy 9 PR (Pg cN 9 BS TS) cell674 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf330]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload330) normal667 46 numeric330
theorem normalizedLeaf331 : AdaptiveCoverage.normalize SL cell675 = normal669 := by
  calc
    AdaptiveCoverage.normalize SL cell675 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell675)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell675)).symm
    _ = normal669 := by rfl

theorem numeric331 : ForcedCoverage2.dispatch (fun _ => payload331) normal669 46 = true := by
  decide +kernel

theorem coveredLeaf331 : CovBy 9 PR (Pg cN 9 BS TS) cell675 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf331]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload331) normal669 46 numeric331
theorem normalizedLeaf332 : AdaptiveCoverage.normalize SL cell676 = normal670 := by
  calc
    AdaptiveCoverage.normalize SL cell676 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell676)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell676)).symm
    _ = normal670 := by rfl

theorem numeric332 : ForcedCoverage2.dispatch (fun _ => payload332) normal670 46 = true := by
  decide +kernel

theorem coveredLeaf332 : CovBy 9 PR (Pg cN 9 BS TS) cell676 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf332]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload332) normal670 46 numeric332
theorem normalizedLeaf333 : AdaptiveCoverage.normalize SL cell683 = normal675 := by
  calc
    AdaptiveCoverage.normalize SL cell683 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell683)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell683)).symm
    _ = normal675 := by rfl

theorem numeric333 : ForcedCoverage2.dispatch (fun _ => payload333) normal675 46 = true := by
  decide +kernel

theorem coveredLeaf333 : CovBy 9 PR (Pg cN 9 BS TS) cell683 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf333]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload333) normal675 46 numeric333
theorem normalizedLeaf334 : AdaptiveCoverage.normalize SL cell685 = normal677 := by
  calc
    AdaptiveCoverage.normalize SL cell685 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell685)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell685)).symm
    _ = normal677 := by rfl

theorem numeric334 : ForcedCoverage2.dispatch (fun _ => payload334) normal677 46 = true := by
  decide +kernel

theorem coveredLeaf334 : CovBy 9 PR (Pg cN 9 BS TS) cell685 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf334]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload334) normal677 46 numeric334
theorem normalizedLeaf335 : AdaptiveCoverage.normalize SL cell689 = normal680 := by
  calc
    AdaptiveCoverage.normalize SL cell689 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell689)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell689)).symm
    _ = normal680 := by rfl

theorem numeric335 : ForcedCoverage2.dispatch (fun _ => payload335) normal680 46 = true := by
  decide +kernel

theorem coveredLeaf335 : CovBy 9 PR (Pg cN 9 BS TS) cell689 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf335]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload335) normal680 46 numeric335
theorem normalizedLeaf336 : AdaptiveCoverage.normalize SL cell693 = normal683 := by
  calc
    AdaptiveCoverage.normalize SL cell693 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell693)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell693)).symm
    _ = normal683 := by rfl

theorem numeric336 : ForcedCoverage2.dispatch (fun _ => payload336) normal683 46 = true := by
  decide +kernel

theorem coveredLeaf336 : CovBy 9 PR (Pg cN 9 BS TS) cell693 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf336]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload336) normal683 46 numeric336
theorem normalizedLeaf337 : AdaptiveCoverage.normalize SL cell694 = normal684 := by
  calc
    AdaptiveCoverage.normalize SL cell694 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell694)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell694)).symm
    _ = normal684 := by rfl

theorem numeric337 : ForcedCoverage2.dispatch (fun _ => payload337) normal684 46 = true := by
  decide +kernel

theorem coveredLeaf337 : CovBy 9 PR (Pg cN 9 BS TS) cell694 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf337]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload337) normal684 46 numeric337
theorem normalizedLeaf338 : AdaptiveCoverage.normalize SL cell692 = normal685 := by
  calc
    AdaptiveCoverage.normalize SL cell692 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell692)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell692)).symm
    _ = normal685 := by rfl

theorem numeric338 : ForcedCoverage2.dispatch (fun _ => payload338) normal685 46 = true := by
  decide +kernel

theorem coveredLeaf338 : CovBy 9 PR (Pg cN 9 BS TS) cell692 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf338]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload338) normal685 46 numeric338
theorem normalizedLeaf339 : AdaptiveCoverage.normalize SL cell695 = normal687 := by
  calc
    AdaptiveCoverage.normalize SL cell695 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell695)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell695)).symm
    _ = normal687 := by rfl

theorem numeric339 : ForcedCoverage2.dispatch (fun _ => payload339) normal687 46 = true := by
  decide +kernel

theorem coveredLeaf339 : CovBy 9 PR (Pg cN 9 BS TS) cell695 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf339]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload339) normal687 46 numeric339
theorem normalizedLeaf340 : AdaptiveCoverage.normalize SL cell697 = normal689 := by
  calc
    AdaptiveCoverage.normalize SL cell697 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell697)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell697)).symm
    _ = normal689 := by rfl

theorem numeric340 : ForcedCoverage2.dispatch (fun _ => payload340) normal689 46 = true := by
  decide +kernel

theorem coveredLeaf340 : CovBy 9 PR (Pg cN 9 BS TS) cell697 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf340]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload340) normal689 46 numeric340
theorem normalizedLeaf341 : AdaptiveCoverage.normalize SL cell699 = normal691 := by
  calc
    AdaptiveCoverage.normalize SL cell699 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell699)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell699)).symm
    _ = normal691 := by rfl

theorem numeric341 : ForcedCoverage2.dispatch (fun _ => payload341) normal691 46 = true := by
  decide +kernel

theorem coveredLeaf341 : CovBy 9 PR (Pg cN 9 BS TS) cell699 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf341]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload341) normal691 46 numeric341
theorem normalizedLeaf342 : AdaptiveCoverage.normalize SL cell700 = normal692 := by
  calc
    AdaptiveCoverage.normalize SL cell700 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell700)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell700)).symm
    _ = normal692 := by rfl

theorem numeric342 : ForcedCoverage2.dispatch (fun _ => payload342) normal692 46 = true := by
  decide +kernel

theorem coveredLeaf342 : CovBy 9 PR (Pg cN 9 BS TS) cell700 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf342]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload342) normal692 46 numeric342
theorem normalizedLeaf343 : AdaptiveCoverage.normalize SL cell703 = normal695 := by
  calc
    AdaptiveCoverage.normalize SL cell703 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell703)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell703)).symm
    _ = normal695 := by rfl

theorem numeric343 : ForcedCoverage2.dispatch (fun _ => payload343) normal695 46 = true := by
  decide +kernel

theorem coveredLeaf343 : CovBy 9 PR (Pg cN 9 BS TS) cell703 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf343]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload343) normal695 46 numeric343
theorem normalizedLeaf344 : AdaptiveCoverage.normalize SL cell707 = normal698 := by
  calc
    AdaptiveCoverage.normalize SL cell707 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell707)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell707)).symm
    _ = normal698 := by rfl

theorem numeric344 : ForcedCoverage2.dispatch (fun _ => payload344) normal698 46 = true := by
  decide +kernel

theorem coveredLeaf344 : CovBy 9 PR (Pg cN 9 BS TS) cell707 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf344]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload344) normal698 46 numeric344
theorem normalizedLeaf345 : AdaptiveCoverage.normalize SL cell709 = normal700 := by
  calc
    AdaptiveCoverage.normalize SL cell709 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell709)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell709)).symm
    _ = normal700 := by rfl

theorem numeric345 : ForcedCoverage2.dispatch (fun _ => payload345) normal700 46 = true := by
  decide +kernel

theorem coveredLeaf345 : CovBy 9 PR (Pg cN 9 BS TS) cell709 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf345]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload345) normal700 46 numeric345
theorem normalizedLeaf346 : AdaptiveCoverage.normalize SL cell710 = normal701 := by
  calc
    AdaptiveCoverage.normalize SL cell710 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell710)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell710)).symm
    _ = normal701 := by rfl

theorem numeric346 : ForcedCoverage2.dispatch (fun _ => payload346) normal701 46 = true := by
  decide +kernel

theorem coveredLeaf346 : CovBy 9 PR (Pg cN 9 BS TS) cell710 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf346]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload346) normal701 46 numeric346
theorem normalizedLeaf347 : AdaptiveCoverage.normalize SL cell706 = normal702 := by
  calc
    AdaptiveCoverage.normalize SL cell706 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell706)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell706)).symm
    _ = normal702 := by rfl

theorem numeric347 : ForcedCoverage2.dispatch (fun _ => payload347) normal702 46 = true := by
  decide +kernel

theorem coveredLeaf347 : CovBy 9 PR (Pg cN 9 BS TS) cell706 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf347]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload347) normal702 46 numeric347
theorem normalizedLeaf348 : AdaptiveCoverage.normalize SL cell711 = normal704 := by
  calc
    AdaptiveCoverage.normalize SL cell711 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell711)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell711)).symm
    _ = normal704 := by rfl

theorem numeric348 : ForcedCoverage2.dispatch (fun _ => payload348) normal704 46 = true := by
  decide +kernel

theorem coveredLeaf348 : CovBy 9 PR (Pg cN 9 BS TS) cell711 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf348]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload348) normal704 46 numeric348
theorem normalizedLeaf349 : AdaptiveCoverage.normalize SL cell715 = normal707 := by
  calc
    AdaptiveCoverage.normalize SL cell715 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell715)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell715)).symm
    _ = normal707 := by rfl

theorem numeric349 : ForcedCoverage2.dispatch (fun _ => payload349) normal707 46 = true := by
  decide +kernel

theorem coveredLeaf349 : CovBy 9 PR (Pg cN 9 BS TS) cell715 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf349]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload349) normal707 46 numeric349
theorem normalizedLeaf350 : AdaptiveCoverage.normalize SL cell717 = normal709 := by
  calc
    AdaptiveCoverage.normalize SL cell717 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell717)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell717)).symm
    _ = normal709 := by rfl

theorem numeric350 : ForcedCoverage2.dispatch (fun _ => payload350) normal709 46 = true := by
  decide +kernel

theorem coveredLeaf350 : CovBy 9 PR (Pg cN 9 BS TS) cell717 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf350]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload350) normal709 46 numeric350
theorem normalizedLeaf351 : AdaptiveCoverage.normalize SL cell719 = normal711 := by
  calc
    AdaptiveCoverage.normalize SL cell719 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell719)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell719)).symm
    _ = normal711 := by rfl

theorem numeric351 : ForcedCoverage2.dispatch (fun _ => payload351) normal711 46 = true := by
  decide +kernel

theorem coveredLeaf351 : CovBy 9 PR (Pg cN 9 BS TS) cell719 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf351]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload351) normal711 46 numeric351

set_option pp.fullNames true
#print axioms normalizedLeaf320
#print axioms numeric320
#print axioms coveredLeaf320
#print axioms normalizedLeaf321
#print axioms numeric321
#print axioms coveredLeaf321
#print axioms normalizedLeaf322
#print axioms numeric322
#print axioms coveredLeaf322
#print axioms normalizedLeaf323
#print axioms numeric323
#print axioms coveredLeaf323
#print axioms normalizedLeaf324
#print axioms numeric324
#print axioms coveredLeaf324
#print axioms normalizedLeaf325
#print axioms numeric325
#print axioms coveredLeaf325
#print axioms normalizedLeaf326
#print axioms numeric326
#print axioms coveredLeaf326
#print axioms normalizedLeaf327
#print axioms numeric327
#print axioms coveredLeaf327
#print axioms normalizedLeaf328
#print axioms numeric328
#print axioms coveredLeaf328
#print axioms normalizedLeaf329
#print axioms numeric329
#print axioms coveredLeaf329
#print axioms normalizedLeaf330
#print axioms numeric330
#print axioms coveredLeaf330
#print axioms normalizedLeaf331
#print axioms numeric331
#print axioms coveredLeaf331
#print axioms normalizedLeaf332
#print axioms numeric332
#print axioms coveredLeaf332
#print axioms normalizedLeaf333
#print axioms numeric333
#print axioms coveredLeaf333
#print axioms normalizedLeaf334
#print axioms numeric334
#print axioms coveredLeaf334
#print axioms normalizedLeaf335
#print axioms numeric335
#print axioms coveredLeaf335
#print axioms normalizedLeaf336
#print axioms numeric336
#print axioms coveredLeaf336
#print axioms normalizedLeaf337
#print axioms numeric337
#print axioms coveredLeaf337
#print axioms normalizedLeaf338
#print axioms numeric338
#print axioms coveredLeaf338
#print axioms normalizedLeaf339
#print axioms numeric339
#print axioms coveredLeaf339
#print axioms normalizedLeaf340
#print axioms numeric340
#print axioms coveredLeaf340
#print axioms normalizedLeaf341
#print axioms numeric341
#print axioms coveredLeaf341
#print axioms normalizedLeaf342
#print axioms numeric342
#print axioms coveredLeaf342
#print axioms normalizedLeaf343
#print axioms numeric343
#print axioms coveredLeaf343
#print axioms normalizedLeaf344
#print axioms numeric344
#print axioms coveredLeaf344
#print axioms normalizedLeaf345
#print axioms numeric345
#print axioms coveredLeaf345
#print axioms normalizedLeaf346
#print axioms numeric346
#print axioms coveredLeaf346
#print axioms normalizedLeaf347
#print axioms numeric347
#print axioms coveredLeaf347
#print axioms normalizedLeaf348
#print axioms numeric348
#print axioms coveredLeaf348
#print axioms normalizedLeaf349
#print axioms numeric349
#print axioms coveredLeaf349
#print axioms normalizedLeaf350
#print axioms numeric350
#print axioms coveredLeaf350
#print axioms normalizedLeaf351
#print axioms numeric351
#print axioms coveredLeaf351
end StructuralGoal20261016.W10Aux478
end
