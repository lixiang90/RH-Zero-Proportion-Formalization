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
theorem normalizedLeaf288 : AdaptiveCoverage.normalize SL cell590 = normal587 := by
  calc
    AdaptiveCoverage.normalize SL cell590 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell590)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell590)).symm
    _ = normal587 := by rfl

theorem numeric288 : ForcedCoverage2.dispatch (fun _ => payload288) normal587 46 = true := by
  decide +kernel

theorem coveredLeaf288 : CovBy 9 PR (Pg cN 9 BS TS) cell590 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf288]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload288) normal587 46 numeric288
theorem normalizedLeaf289 : AdaptiveCoverage.normalize SL cell603 = normal591 := by
  calc
    AdaptiveCoverage.normalize SL cell603 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell603)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell603)).symm
    _ = normal591 := by rfl

theorem numeric289 : ForcedCoverage2.dispatch (fun _ => payload289) normal591 46 = true := by
  decide +kernel

theorem coveredLeaf289 : CovBy 9 PR (Pg cN 9 BS TS) cell603 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf289]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload289) normal591 46 numeric289
theorem normalizedLeaf290 : AdaptiveCoverage.normalize SL cell604 = normal592 := by
  calc
    AdaptiveCoverage.normalize SL cell604 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell604)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell604)).symm
    _ = normal592 := by rfl

theorem numeric290 : ForcedCoverage2.dispatch (fun _ => payload290) normal592 46 = true := by
  decide +kernel

theorem coveredLeaf290 : CovBy 9 PR (Pg cN 9 BS TS) cell604 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf290]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload290) normal592 46 numeric290
theorem normalizedLeaf291 : AdaptiveCoverage.normalize SL cell611 = normal597 := by
  calc
    AdaptiveCoverage.normalize SL cell611 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell611)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell611)).symm
    _ = normal597 := by rfl

theorem numeric291 : ForcedCoverage2.dispatch (fun _ => payload291) normal597 46 = true := by
  decide +kernel

theorem coveredLeaf291 : CovBy 9 PR (Pg cN 9 BS TS) cell611 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf291]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload291) normal597 46 numeric291
theorem normalizedLeaf292 : AdaptiveCoverage.normalize SL cell612 = normal598 := by
  calc
    AdaptiveCoverage.normalize SL cell612 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell612)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell612)).symm
    _ = normal598 := by rfl

theorem numeric292 : ForcedCoverage2.dispatch (fun _ => payload292) normal598 46 = true := by
  decide +kernel

theorem coveredLeaf292 : CovBy 9 PR (Pg cN 9 BS TS) cell612 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf292]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload292) normal598 46 numeric292
theorem normalizedLeaf293 : AdaptiveCoverage.normalize SL cell610 = normal599 := by
  calc
    AdaptiveCoverage.normalize SL cell610 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell610)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell610)).symm
    _ = normal599 := by rfl

theorem numeric293 : ForcedCoverage2.dispatch (fun _ => payload293) normal599 46 = true := by
  decide +kernel

theorem coveredLeaf293 : CovBy 9 PR (Pg cN 9 BS TS) cell610 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf293]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload293) normal599 46 numeric293
theorem normalizedLeaf294 : AdaptiveCoverage.normalize SL cell613 = normal601 := by
  calc
    AdaptiveCoverage.normalize SL cell613 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell613)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell613)).symm
    _ = normal601 := by rfl

theorem numeric294 : ForcedCoverage2.dispatch (fun _ => payload294) normal601 46 = true := by
  decide +kernel

theorem coveredLeaf294 : CovBy 9 PR (Pg cN 9 BS TS) cell613 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf294]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload294) normal601 46 numeric294
theorem normalizedLeaf295 : AdaptiveCoverage.normalize SL cell614 = normal602 := by
  calc
    AdaptiveCoverage.normalize SL cell614 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell614)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell614)).symm
    _ = normal602 := by rfl

theorem numeric295 : ForcedCoverage2.dispatch (fun _ => payload295) normal602 46 = true := by
  decide +kernel

theorem coveredLeaf295 : CovBy 9 PR (Pg cN 9 BS TS) cell614 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf295]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload295) normal602 46 numeric295
theorem normalizedLeaf296 : AdaptiveCoverage.normalize SL cell606 = normal603 := by
  calc
    AdaptiveCoverage.normalize SL cell606 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell606)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell606)).symm
    _ = normal603 := by rfl

theorem numeric296 : ForcedCoverage2.dispatch (fun _ => payload296) normal603 46 = true := by
  decide +kernel

theorem coveredLeaf296 : CovBy 9 PR (Pg cN 9 BS TS) cell606 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf296]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload296) normal603 46 numeric296
theorem normalizedLeaf297 : AdaptiveCoverage.normalize SL cell623 = normal609 := by
  calc
    AdaptiveCoverage.normalize SL cell623 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell623)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell623)).symm
    _ = normal609 := by rfl

theorem numeric297 : ForcedCoverage2.dispatch (fun _ => payload297) normal609 46 = true := by
  decide +kernel

theorem coveredLeaf297 : CovBy 9 PR (Pg cN 9 BS TS) cell623 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf297]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload297) normal609 46 numeric297
theorem normalizedLeaf298 : AdaptiveCoverage.normalize SL cell624 = normal610 := by
  calc
    AdaptiveCoverage.normalize SL cell624 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell624)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell624)).symm
    _ = normal610 := by rfl

theorem numeric298 : ForcedCoverage2.dispatch (fun _ => payload298) normal610 46 = true := by
  decide +kernel

theorem coveredLeaf298 : CovBy 9 PR (Pg cN 9 BS TS) cell624 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf298]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload298) normal610 46 numeric298
theorem normalizedLeaf299 : AdaptiveCoverage.normalize SL cell622 = normal611 := by
  calc
    AdaptiveCoverage.normalize SL cell622 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell622)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell622)).symm
    _ = normal611 := by rfl

theorem numeric299 : ForcedCoverage2.dispatch (fun _ => payload299) normal611 46 = true := by
  decide +kernel

theorem coveredLeaf299 : CovBy 9 PR (Pg cN 9 BS TS) cell622 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf299]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload299) normal611 46 numeric299
theorem normalizedLeaf300 : AdaptiveCoverage.normalize SL cell625 = normal613 := by
  calc
    AdaptiveCoverage.normalize SL cell625 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell625)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell625)).symm
    _ = normal613 := by rfl

theorem numeric300 : ForcedCoverage2.dispatch (fun _ => payload300) normal613 46 = true := by
  decide +kernel

theorem coveredLeaf300 : CovBy 9 PR (Pg cN 9 BS TS) cell625 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf300]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload300) normal613 46 numeric300
theorem normalizedLeaf301 : AdaptiveCoverage.normalize SL cell626 = normal614 := by
  calc
    AdaptiveCoverage.normalize SL cell626 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell626)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell626)).symm
    _ = normal614 := by rfl

theorem numeric301 : ForcedCoverage2.dispatch (fun _ => payload301) normal614 46 = true := by
  decide +kernel

theorem coveredLeaf301 : CovBy 9 PR (Pg cN 9 BS TS) cell626 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf301]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload301) normal614 46 numeric301
theorem normalizedLeaf302 : AdaptiveCoverage.normalize SL cell618 = normal615 := by
  calc
    AdaptiveCoverage.normalize SL cell618 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell618)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell618)).symm
    _ = normal615 := by rfl

theorem numeric302 : ForcedCoverage2.dispatch (fun _ => payload302) normal615 46 = true := by
  decide +kernel

theorem coveredLeaf302 : CovBy 9 PR (Pg cN 9 BS TS) cell618 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf302]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload302) normal615 46 numeric302
theorem normalizedLeaf303 : AdaptiveCoverage.normalize SL cell633 = normal620 := by
  calc
    AdaptiveCoverage.normalize SL cell633 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell633)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell633)).symm
    _ = normal620 := by rfl

theorem numeric303 : ForcedCoverage2.dispatch (fun _ => payload303) normal620 46 = true := by
  decide +kernel

theorem coveredLeaf303 : CovBy 9 PR (Pg cN 9 BS TS) cell633 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf303]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload303) normal620 46 numeric303
theorem normalizedLeaf304 : AdaptiveCoverage.normalize SL cell634 = normal621 := by
  calc
    AdaptiveCoverage.normalize SL cell634 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell634)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell634)).symm
    _ = normal621 := by rfl

theorem numeric304 : ForcedCoverage2.dispatch (fun _ => payload304) normal621 46 = true := by
  decide +kernel

theorem coveredLeaf304 : CovBy 9 PR (Pg cN 9 BS TS) cell634 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf304]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload304) normal621 46 numeric304
theorem normalizedLeaf305 : AdaptiveCoverage.normalize SL cell635 = normal623 := by
  calc
    AdaptiveCoverage.normalize SL cell635 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell635)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell635)).symm
    _ = normal623 := by rfl

theorem numeric305 : ForcedCoverage2.dispatch (fun _ => payload305) normal623 46 = true := by
  decide +kernel

theorem coveredLeaf305 : CovBy 9 PR (Pg cN 9 BS TS) cell635 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf305]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload305) normal623 46 numeric305
theorem normalizedLeaf306 : AdaptiveCoverage.normalize SL cell636 = normal624 := by
  calc
    AdaptiveCoverage.normalize SL cell636 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell636)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell636)).symm
    _ = normal624 := by rfl

theorem numeric306 : ForcedCoverage2.dispatch (fun _ => payload306) normal624 46 = true := by
  decide +kernel

theorem coveredLeaf306 : CovBy 9 PR (Pg cN 9 BS TS) cell636 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf306]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload306) normal624 46 numeric306
theorem normalizedLeaf307 : AdaptiveCoverage.normalize SL cell637 = normal626 := by
  calc
    AdaptiveCoverage.normalize SL cell637 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell637)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell637)).symm
    _ = normal626 := by rfl

theorem numeric307 : ForcedCoverage2.dispatch (fun _ => payload307) normal626 46 = true := by
  decide +kernel

theorem coveredLeaf307 : CovBy 9 PR (Pg cN 9 BS TS) cell637 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf307]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload307) normal626 46 numeric307
theorem normalizedLeaf308 : AdaptiveCoverage.normalize SL cell638 = normal627 := by
  calc
    AdaptiveCoverage.normalize SL cell638 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell638)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell638)).symm
    _ = normal627 := by rfl

theorem numeric308 : ForcedCoverage2.dispatch (fun _ => payload308) normal627 46 = true := by
  decide +kernel

theorem coveredLeaf308 : CovBy 9 PR (Pg cN 9 BS TS) cell638 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf308]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload308) normal627 46 numeric308
theorem normalizedLeaf309 : AdaptiveCoverage.normalize SL cell628 = normal628 := by
  calc
    AdaptiveCoverage.normalize SL cell628 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell628)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell628)).symm
    _ = normal628 := by rfl

theorem numeric309 : ForcedCoverage2.dispatch (fun _ => payload309) normal628 46 = true := by
  decide +kernel

theorem coveredLeaf309 : CovBy 9 PR (Pg cN 9 BS TS) cell628 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf309]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload309) normal628 46 numeric309
theorem normalizedLeaf310 : AdaptiveCoverage.normalize SL cell641 = normal631 := by
  calc
    AdaptiveCoverage.normalize SL cell641 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell641)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell641)).symm
    _ = normal631 := by rfl

theorem numeric310 : ForcedCoverage2.dispatch (fun _ => payload310) normal631 46 = true := by
  decide +kernel

theorem coveredLeaf310 : CovBy 9 PR (Pg cN 9 BS TS) cell641 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf310]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload310) normal631 46 numeric310
theorem normalizedLeaf311 : AdaptiveCoverage.normalize SL cell642 = normal632 := by
  calc
    AdaptiveCoverage.normalize SL cell642 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell642)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell642)).symm
    _ = normal632 := by rfl

theorem numeric311 : ForcedCoverage2.dispatch (fun _ => payload311) normal632 46 = true := by
  decide +kernel

theorem coveredLeaf311 : CovBy 9 PR (Pg cN 9 BS TS) cell642 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf311]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload311) normal632 46 numeric311
theorem normalizedLeaf312 : AdaptiveCoverage.normalize SL cell640 = normal633 := by
  calc
    AdaptiveCoverage.normalize SL cell640 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell640)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell640)).symm
    _ = normal633 := by rfl

theorem numeric312 : ForcedCoverage2.dispatch (fun _ => payload312) normal633 46 = true := by
  decide +kernel

theorem coveredLeaf312 : CovBy 9 PR (Pg cN 9 BS TS) cell640 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf312]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload312) normal633 46 numeric312
theorem normalizedLeaf313 : AdaptiveCoverage.normalize SL cell651 = normal639 := by
  calc
    AdaptiveCoverage.normalize SL cell651 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell651)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell651)).symm
    _ = normal639 := by rfl

theorem numeric313 : ForcedCoverage2.dispatch (fun _ => payload313) normal639 46 = true := by
  decide +kernel

theorem coveredLeaf313 : CovBy 9 PR (Pg cN 9 BS TS) cell651 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf313]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload313) normal639 46 numeric313
theorem normalizedLeaf314 : AdaptiveCoverage.normalize SL cell652 = normal640 := by
  calc
    AdaptiveCoverage.normalize SL cell652 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell652)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell652)).symm
    _ = normal640 := by rfl

theorem numeric314 : ForcedCoverage2.dispatch (fun _ => payload314) normal640 46 = true := by
  decide +kernel

theorem coveredLeaf314 : CovBy 9 PR (Pg cN 9 BS TS) cell652 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf314]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload314) normal640 46 numeric314
theorem normalizedLeaf315 : AdaptiveCoverage.normalize SL cell650 = normal641 := by
  calc
    AdaptiveCoverage.normalize SL cell650 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell650)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell650)).symm
    _ = normal641 := by rfl

theorem numeric315 : ForcedCoverage2.dispatch (fun _ => payload315) normal641 46 = true := by
  decide +kernel

theorem coveredLeaf315 : CovBy 9 PR (Pg cN 9 BS TS) cell650 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf315]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload315) normal641 46 numeric315
theorem normalizedLeaf316 : AdaptiveCoverage.normalize SL cell648 = normal642 := by
  calc
    AdaptiveCoverage.normalize SL cell648 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell648)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell648)).symm
    _ = normal642 := by rfl

theorem numeric316 : ForcedCoverage2.dispatch (fun _ => payload316) normal642 46 = true := by
  decide +kernel

theorem coveredLeaf316 : CovBy 9 PR (Pg cN 9 BS TS) cell648 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf316]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload316) normal642 46 numeric316
theorem normalizedLeaf317 : AdaptiveCoverage.normalize SL cell646 = normal643 := by
  calc
    AdaptiveCoverage.normalize SL cell646 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell646)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell646)).symm
    _ = normal643 := by rfl

theorem numeric317 : ForcedCoverage2.dispatch (fun _ => payload317) normal643 46 = true := by
  decide +kernel

theorem coveredLeaf317 : CovBy 9 PR (Pg cN 9 BS TS) cell646 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf317]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload317) normal643 46 numeric317
theorem normalizedLeaf318 : AdaptiveCoverage.normalize SL cell644 = normal644 := by
  calc
    AdaptiveCoverage.normalize SL cell644 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell644)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell644)).symm
    _ = normal644 := by rfl

theorem numeric318 : ForcedCoverage2.dispatch (fun _ => payload318) normal644 46 = true := by
  decide +kernel

theorem coveredLeaf318 : CovBy 9 PR (Pg cN 9 BS TS) cell644 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf318]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload318) normal644 46 numeric318
theorem normalizedLeaf319 : AdaptiveCoverage.normalize SL cell661 = normal650 := by
  calc
    AdaptiveCoverage.normalize SL cell661 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell661)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell661)).symm
    _ = normal650 := by rfl

theorem numeric319 : ForcedCoverage2.dispatch (fun _ => payload319) normal650 46 = true := by
  decide +kernel

theorem coveredLeaf319 : CovBy 9 PR (Pg cN 9 BS TS) cell661 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf319]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload319) normal650 46 numeric319

set_option pp.fullNames true
#print axioms normalizedLeaf288
#print axioms numeric288
#print axioms coveredLeaf288
#print axioms normalizedLeaf289
#print axioms numeric289
#print axioms coveredLeaf289
#print axioms normalizedLeaf290
#print axioms numeric290
#print axioms coveredLeaf290
#print axioms normalizedLeaf291
#print axioms numeric291
#print axioms coveredLeaf291
#print axioms normalizedLeaf292
#print axioms numeric292
#print axioms coveredLeaf292
#print axioms normalizedLeaf293
#print axioms numeric293
#print axioms coveredLeaf293
#print axioms normalizedLeaf294
#print axioms numeric294
#print axioms coveredLeaf294
#print axioms normalizedLeaf295
#print axioms numeric295
#print axioms coveredLeaf295
#print axioms normalizedLeaf296
#print axioms numeric296
#print axioms coveredLeaf296
#print axioms normalizedLeaf297
#print axioms numeric297
#print axioms coveredLeaf297
#print axioms normalizedLeaf298
#print axioms numeric298
#print axioms coveredLeaf298
#print axioms normalizedLeaf299
#print axioms numeric299
#print axioms coveredLeaf299
#print axioms normalizedLeaf300
#print axioms numeric300
#print axioms coveredLeaf300
#print axioms normalizedLeaf301
#print axioms numeric301
#print axioms coveredLeaf301
#print axioms normalizedLeaf302
#print axioms numeric302
#print axioms coveredLeaf302
#print axioms normalizedLeaf303
#print axioms numeric303
#print axioms coveredLeaf303
#print axioms normalizedLeaf304
#print axioms numeric304
#print axioms coveredLeaf304
#print axioms normalizedLeaf305
#print axioms numeric305
#print axioms coveredLeaf305
#print axioms normalizedLeaf306
#print axioms numeric306
#print axioms coveredLeaf306
#print axioms normalizedLeaf307
#print axioms numeric307
#print axioms coveredLeaf307
#print axioms normalizedLeaf308
#print axioms numeric308
#print axioms coveredLeaf308
#print axioms normalizedLeaf309
#print axioms numeric309
#print axioms coveredLeaf309
#print axioms normalizedLeaf310
#print axioms numeric310
#print axioms coveredLeaf310
#print axioms normalizedLeaf311
#print axioms numeric311
#print axioms coveredLeaf311
#print axioms normalizedLeaf312
#print axioms numeric312
#print axioms coveredLeaf312
#print axioms normalizedLeaf313
#print axioms numeric313
#print axioms coveredLeaf313
#print axioms normalizedLeaf314
#print axioms numeric314
#print axioms coveredLeaf314
#print axioms normalizedLeaf315
#print axioms numeric315
#print axioms coveredLeaf315
#print axioms normalizedLeaf316
#print axioms numeric316
#print axioms coveredLeaf316
#print axioms normalizedLeaf317
#print axioms numeric317
#print axioms coveredLeaf317
#print axioms normalizedLeaf318
#print axioms numeric318
#print axioms coveredLeaf318
#print axioms normalizedLeaf319
#print axioms numeric319
#print axioms coveredLeaf319
end StructuralGoal20261016.W10Aux478
end
