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
theorem normalizedLeaf256 : AdaptiveCoverage.normalize SL cell537 = normal525 := by
  calc
    AdaptiveCoverage.normalize SL cell537 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell537)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell537)).symm
    _ = normal525 := by rfl

theorem numeric256 : ForcedCoverage2.dispatch (fun _ => payload256) normal525 46 = true := by
  decide +kernel

theorem coveredLeaf256 : CovBy 9 PR (Pg cN 9 BS TS) cell537 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf256]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload256) normal525 46 numeric256
theorem normalizedLeaf257 : AdaptiveCoverage.normalize SL cell538 = normal526 := by
  calc
    AdaptiveCoverage.normalize SL cell538 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell538)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell538)).symm
    _ = normal526 := by rfl

theorem numeric257 : ForcedCoverage2.dispatch (fun _ => payload257) normal526 46 = true := by
  decide +kernel

theorem coveredLeaf257 : CovBy 9 PR (Pg cN 9 BS TS) cell538 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf257]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload257) normal526 46 numeric257
theorem normalizedLeaf258 : AdaptiveCoverage.normalize SL cell536 = normal527 := by
  calc
    AdaptiveCoverage.normalize SL cell536 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell536)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell536)).symm
    _ = normal527 := by rfl

theorem numeric258 : ForcedCoverage2.dispatch (fun _ => payload258) normal527 46 = true := by
  decide +kernel

theorem coveredLeaf258 : CovBy 9 PR (Pg cN 9 BS TS) cell536 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf258]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload258) normal527 46 numeric258
theorem normalizedLeaf259 : AdaptiveCoverage.normalize SL cell541 = normal530 := by
  calc
    AdaptiveCoverage.normalize SL cell541 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell541)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell541)).symm
    _ = normal530 := by rfl

theorem numeric259 : ForcedCoverage2.dispatch (fun _ => payload259) normal530 46 = true := by
  decide +kernel

theorem coveredLeaf259 : CovBy 9 PR (Pg cN 9 BS TS) cell541 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf259]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload259) normal530 46 numeric259
theorem normalizedLeaf260 : AdaptiveCoverage.normalize SL cell543 = normal532 := by
  calc
    AdaptiveCoverage.normalize SL cell543 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell543)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell543)).symm
    _ = normal532 := by rfl

theorem numeric260 : ForcedCoverage2.dispatch (fun _ => payload260) normal532 46 = true := by
  decide +kernel

theorem coveredLeaf260 : CovBy 9 PR (Pg cN 9 BS TS) cell543 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf260]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload260) normal532 46 numeric260
theorem normalizedLeaf261 : AdaptiveCoverage.normalize SL cell545 = normal534 := by
  calc
    AdaptiveCoverage.normalize SL cell545 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell545)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell545)).symm
    _ = normal534 := by rfl

theorem numeric261 : ForcedCoverage2.dispatch (fun _ => payload261) normal534 46 = true := by
  decide +kernel

theorem coveredLeaf261 : CovBy 9 PR (Pg cN 9 BS TS) cell545 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf261]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload261) normal534 46 numeric261
theorem normalizedLeaf262 : AdaptiveCoverage.normalize SL cell547 = normal536 := by
  calc
    AdaptiveCoverage.normalize SL cell547 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell547)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell547)).symm
    _ = normal536 := by rfl

theorem numeric262 : ForcedCoverage2.dispatch (fun _ => payload262) normal536 46 = true := by
  decide +kernel

theorem coveredLeaf262 : CovBy 9 PR (Pg cN 9 BS TS) cell547 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf262]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload262) normal536 46 numeric262
theorem normalizedLeaf263 : AdaptiveCoverage.normalize SL cell551 = normal539 := by
  calc
    AdaptiveCoverage.normalize SL cell551 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell551)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell551)).symm
    _ = normal539 := by rfl

theorem numeric263 : ForcedCoverage2.dispatch (fun _ => payload263) normal539 46 = true := by
  decide +kernel

theorem coveredLeaf263 : CovBy 9 PR (Pg cN 9 BS TS) cell551 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf263]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload263) normal539 46 numeric263
theorem normalizedLeaf264 : AdaptiveCoverage.normalize SL cell552 = normal540 := by
  calc
    AdaptiveCoverage.normalize SL cell552 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell552)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell552)).symm
    _ = normal540 := by rfl

theorem numeric264 : ForcedCoverage2.dispatch (fun _ => payload264) normal540 46 = true := by
  decide +kernel

theorem coveredLeaf264 : CovBy 9 PR (Pg cN 9 BS TS) cell552 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf264]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload264) normal540 46 numeric264
theorem normalizedLeaf265 : AdaptiveCoverage.normalize SL cell550 = normal541 := by
  calc
    AdaptiveCoverage.normalize SL cell550 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell550)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell550)).symm
    _ = normal541 := by rfl

theorem numeric265 : ForcedCoverage2.dispatch (fun _ => payload265) normal541 46 = true := by
  decide +kernel

theorem coveredLeaf265 : CovBy 9 PR (Pg cN 9 BS TS) cell550 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf265]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload265) normal541 46 numeric265
theorem normalizedLeaf266 : AdaptiveCoverage.normalize SL cell553 = normal543 := by
  calc
    AdaptiveCoverage.normalize SL cell553 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell553)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell553)).symm
    _ = normal543 := by rfl

theorem numeric266 : ForcedCoverage2.dispatch (fun _ => payload266) normal543 46 = true := by
  decide +kernel

theorem coveredLeaf266 : CovBy 9 PR (Pg cN 9 BS TS) cell553 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf266]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload266) normal543 46 numeric266
theorem normalizedLeaf267 : AdaptiveCoverage.normalize SL cell555 = normal545 := by
  calc
    AdaptiveCoverage.normalize SL cell555 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell555)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell555)).symm
    _ = normal545 := by rfl

theorem numeric267 : ForcedCoverage2.dispatch (fun _ => payload267) normal545 46 = true := by
  decide +kernel

theorem coveredLeaf267 : CovBy 9 PR (Pg cN 9 BS TS) cell555 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf267]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload267) normal545 46 numeric267
theorem normalizedLeaf268 : AdaptiveCoverage.normalize SL cell557 = normal547 := by
  calc
    AdaptiveCoverage.normalize SL cell557 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell557)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell557)).symm
    _ = normal547 := by rfl

theorem numeric268 : ForcedCoverage2.dispatch (fun _ => payload268) normal547 46 = true := by
  decide +kernel

theorem coveredLeaf268 : CovBy 9 PR (Pg cN 9 BS TS) cell557 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf268]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload268) normal547 46 numeric268
theorem normalizedLeaf269 : AdaptiveCoverage.normalize SL cell559 = normal549 := by
  calc
    AdaptiveCoverage.normalize SL cell559 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell559)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell559)).symm
    _ = normal549 := by rfl

theorem numeric269 : ForcedCoverage2.dispatch (fun _ => payload269) normal549 46 = true := by
  decide +kernel

theorem coveredLeaf269 : CovBy 9 PR (Pg cN 9 BS TS) cell559 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf269]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload269) normal549 46 numeric269
theorem normalizedLeaf270 : AdaptiveCoverage.normalize SL cell560 = normal550 := by
  calc
    AdaptiveCoverage.normalize SL cell560 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell560)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell560)).symm
    _ = normal550 := by rfl

theorem numeric270 : ForcedCoverage2.dispatch (fun _ => payload270) normal550 46 = true := by
  decide +kernel

theorem coveredLeaf270 : CovBy 9 PR (Pg cN 9 BS TS) cell560 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf270]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload270) normal550 46 numeric270
theorem normalizedLeaf271 : AdaptiveCoverage.normalize SL cell524 = normal551 := by
  calc
    AdaptiveCoverage.normalize SL cell524 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell524)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell524)).symm
    _ = normal551 := by rfl

theorem numeric271 : ForcedCoverage2.dispatch (fun _ => payload271) normal551 46 = true := by
  decide +kernel

theorem coveredLeaf271 : CovBy 9 PR (Pg cN 9 BS TS) cell524 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf271]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload271) normal551 46 numeric271
theorem normalizedLeaf272 : AdaptiveCoverage.normalize SL cell522 = normal552 := by
  calc
    AdaptiveCoverage.normalize SL cell522 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell522)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell522)).symm
    _ = normal552 := by rfl

theorem numeric272 : ForcedCoverage2.dispatch (fun _ => payload272) normal552 46 = true := by
  decide +kernel

theorem coveredLeaf272 : CovBy 9 PR (Pg cN 9 BS TS) cell522 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf272]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload272) normal552 46 numeric272
theorem normalizedLeaf273 : AdaptiveCoverage.normalize SL cell561 = normal554 := by
  calc
    AdaptiveCoverage.normalize SL cell561 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell561)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell561)).symm
    _ = normal554 := by rfl

theorem numeric273 : ForcedCoverage2.dispatch (fun _ => payload273) normal554 46 = true := by
  decide +kernel

theorem coveredLeaf273 : CovBy 9 PR (Pg cN 9 BS TS) cell561 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf273]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload273) normal554 46 numeric273
theorem normalizedLeaf274 : AdaptiveCoverage.normalize SL cell563 = normal556 := by
  calc
    AdaptiveCoverage.normalize SL cell563 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell563)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell563)).symm
    _ = normal556 := by rfl

theorem numeric274 : ForcedCoverage2.dispatch (fun _ => payload274) normal556 46 = true := by
  decide +kernel

theorem coveredLeaf274 : CovBy 9 PR (Pg cN 9 BS TS) cell563 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf274]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload274) normal556 46 numeric274
theorem normalizedLeaf275 : AdaptiveCoverage.normalize SL cell575 = normal563 := by
  calc
    AdaptiveCoverage.normalize SL cell575 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell575)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell575)).symm
    _ = normal563 := by rfl

theorem numeric275 : ForcedCoverage2.dispatch (fun _ => payload275) normal563 46 = true := by
  decide +kernel

theorem coveredLeaf275 : CovBy 9 PR (Pg cN 9 BS TS) cell575 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf275]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload275) normal563 46 numeric275
theorem normalizedLeaf276 : AdaptiveCoverage.normalize SL cell581 = normal567 := by
  calc
    AdaptiveCoverage.normalize SL cell581 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell581)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell581)).symm
    _ = normal567 := by rfl

theorem numeric276 : ForcedCoverage2.dispatch (fun _ => payload276) normal567 46 = true := by
  decide +kernel

theorem coveredLeaf276 : CovBy 9 PR (Pg cN 9 BS TS) cell581 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf276]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload276) normal567 46 numeric276
theorem normalizedLeaf277 : AdaptiveCoverage.normalize SL cell582 = normal568 := by
  calc
    AdaptiveCoverage.normalize SL cell582 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell582)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell582)).symm
    _ = normal568 := by rfl

theorem numeric277 : ForcedCoverage2.dispatch (fun _ => payload277) normal568 46 = true := by
  decide +kernel

theorem coveredLeaf277 : CovBy 9 PR (Pg cN 9 BS TS) cell582 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf277]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload277) normal568 46 numeric277
theorem normalizedLeaf278 : AdaptiveCoverage.normalize SL cell580 = normal569 := by
  calc
    AdaptiveCoverage.normalize SL cell580 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell580)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell580)).symm
    _ = normal569 := by rfl

theorem numeric278 : ForcedCoverage2.dispatch (fun _ => payload278) normal569 46 = true := by
  decide +kernel

theorem coveredLeaf278 : CovBy 9 PR (Pg cN 9 BS TS) cell580 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf278]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload278) normal569 46 numeric278
theorem normalizedLeaf279 : AdaptiveCoverage.normalize SL cell578 = normal570 := by
  calc
    AdaptiveCoverage.normalize SL cell578 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell578)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell578)).symm
    _ = normal570 := by rfl

theorem numeric279 : ForcedCoverage2.dispatch (fun _ => payload279) normal570 46 = true := by
  decide +kernel

theorem coveredLeaf279 : CovBy 9 PR (Pg cN 9 BS TS) cell578 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf279]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload279) normal570 46 numeric279
theorem normalizedLeaf280 : AdaptiveCoverage.normalize SL cell587 = normal574 := by
  calc
    AdaptiveCoverage.normalize SL cell587 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell587)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell587)).symm
    _ = normal574 := by rfl

theorem numeric280 : ForcedCoverage2.dispatch (fun _ => payload280) normal574 46 = true := by
  decide +kernel

theorem coveredLeaf280 : CovBy 9 PR (Pg cN 9 BS TS) cell587 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf280]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload280) normal574 46 numeric280
theorem normalizedLeaf281 : AdaptiveCoverage.normalize SL cell588 = normal575 := by
  calc
    AdaptiveCoverage.normalize SL cell588 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell588)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell588)).symm
    _ = normal575 := by rfl

theorem numeric281 : ForcedCoverage2.dispatch (fun _ => payload281) normal575 46 = true := by
  decide +kernel

theorem coveredLeaf281 : CovBy 9 PR (Pg cN 9 BS TS) cell588 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf281]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload281) normal575 46 numeric281
theorem normalizedLeaf282 : AdaptiveCoverage.normalize SL cell586 = normal576 := by
  calc
    AdaptiveCoverage.normalize SL cell586 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell586)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell586)).symm
    _ = normal576 := by rfl

theorem numeric282 : ForcedCoverage2.dispatch (fun _ => payload282) normal576 46 = true := by
  decide +kernel

theorem coveredLeaf282 : CovBy 9 PR (Pg cN 9 BS TS) cell586 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf282]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload282) normal576 46 numeric282
theorem normalizedLeaf283 : AdaptiveCoverage.normalize SL cell597 = normal582 := by
  calc
    AdaptiveCoverage.normalize SL cell597 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell597)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell597)).symm
    _ = normal582 := by rfl

theorem numeric283 : ForcedCoverage2.dispatch (fun _ => payload283) normal582 46 = true := by
  decide +kernel

theorem coveredLeaf283 : CovBy 9 PR (Pg cN 9 BS TS) cell597 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf283]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload283) normal582 46 numeric283
theorem normalizedLeaf284 : AdaptiveCoverage.normalize SL cell598 = normal583 := by
  calc
    AdaptiveCoverage.normalize SL cell598 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell598)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell598)).symm
    _ = normal583 := by rfl

theorem numeric284 : ForcedCoverage2.dispatch (fun _ => payload284) normal583 46 = true := by
  decide +kernel

theorem coveredLeaf284 : CovBy 9 PR (Pg cN 9 BS TS) cell598 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf284]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload284) normal583 46 numeric284
theorem normalizedLeaf285 : AdaptiveCoverage.normalize SL cell596 = normal584 := by
  calc
    AdaptiveCoverage.normalize SL cell596 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell596)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell596)).symm
    _ = normal584 := by rfl

theorem numeric285 : ForcedCoverage2.dispatch (fun _ => payload285) normal584 46 = true := by
  decide +kernel

theorem coveredLeaf285 : CovBy 9 PR (Pg cN 9 BS TS) cell596 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf285]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload285) normal584 46 numeric285
theorem normalizedLeaf286 : AdaptiveCoverage.normalize SL cell594 = normal585 := by
  calc
    AdaptiveCoverage.normalize SL cell594 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell594)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell594)).symm
    _ = normal585 := by rfl

theorem numeric286 : ForcedCoverage2.dispatch (fun _ => payload286) normal585 46 = true := by
  decide +kernel

theorem coveredLeaf286 : CovBy 9 PR (Pg cN 9 BS TS) cell594 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf286]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload286) normal585 46 numeric286
theorem normalizedLeaf287 : AdaptiveCoverage.normalize SL cell592 = normal586 := by
  calc
    AdaptiveCoverage.normalize SL cell592 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell592)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell592)).symm
    _ = normal586 := by rfl

theorem numeric287 : ForcedCoverage2.dispatch (fun _ => payload287) normal586 46 = true := by
  decide +kernel

theorem coveredLeaf287 : CovBy 9 PR (Pg cN 9 BS TS) cell592 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf287]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload287) normal586 46 numeric287

set_option pp.fullNames true
#print axioms normalizedLeaf256
#print axioms numeric256
#print axioms coveredLeaf256
#print axioms normalizedLeaf257
#print axioms numeric257
#print axioms coveredLeaf257
#print axioms normalizedLeaf258
#print axioms numeric258
#print axioms coveredLeaf258
#print axioms normalizedLeaf259
#print axioms numeric259
#print axioms coveredLeaf259
#print axioms normalizedLeaf260
#print axioms numeric260
#print axioms coveredLeaf260
#print axioms normalizedLeaf261
#print axioms numeric261
#print axioms coveredLeaf261
#print axioms normalizedLeaf262
#print axioms numeric262
#print axioms coveredLeaf262
#print axioms normalizedLeaf263
#print axioms numeric263
#print axioms coveredLeaf263
#print axioms normalizedLeaf264
#print axioms numeric264
#print axioms coveredLeaf264
#print axioms normalizedLeaf265
#print axioms numeric265
#print axioms coveredLeaf265
#print axioms normalizedLeaf266
#print axioms numeric266
#print axioms coveredLeaf266
#print axioms normalizedLeaf267
#print axioms numeric267
#print axioms coveredLeaf267
#print axioms normalizedLeaf268
#print axioms numeric268
#print axioms coveredLeaf268
#print axioms normalizedLeaf269
#print axioms numeric269
#print axioms coveredLeaf269
#print axioms normalizedLeaf270
#print axioms numeric270
#print axioms coveredLeaf270
#print axioms normalizedLeaf271
#print axioms numeric271
#print axioms coveredLeaf271
#print axioms normalizedLeaf272
#print axioms numeric272
#print axioms coveredLeaf272
#print axioms normalizedLeaf273
#print axioms numeric273
#print axioms coveredLeaf273
#print axioms normalizedLeaf274
#print axioms numeric274
#print axioms coveredLeaf274
#print axioms normalizedLeaf275
#print axioms numeric275
#print axioms coveredLeaf275
#print axioms normalizedLeaf276
#print axioms numeric276
#print axioms coveredLeaf276
#print axioms normalizedLeaf277
#print axioms numeric277
#print axioms coveredLeaf277
#print axioms normalizedLeaf278
#print axioms numeric278
#print axioms coveredLeaf278
#print axioms normalizedLeaf279
#print axioms numeric279
#print axioms coveredLeaf279
#print axioms normalizedLeaf280
#print axioms numeric280
#print axioms coveredLeaf280
#print axioms normalizedLeaf281
#print axioms numeric281
#print axioms coveredLeaf281
#print axioms normalizedLeaf282
#print axioms numeric282
#print axioms coveredLeaf282
#print axioms normalizedLeaf283
#print axioms numeric283
#print axioms coveredLeaf283
#print axioms normalizedLeaf284
#print axioms numeric284
#print axioms coveredLeaf284
#print axioms normalizedLeaf285
#print axioms numeric285
#print axioms coveredLeaf285
#print axioms normalizedLeaf286
#print axioms numeric286
#print axioms coveredLeaf286
#print axioms normalizedLeaf287
#print axioms numeric287
#print axioms coveredLeaf287
end StructuralGoal20261016.W10Aux478
end
