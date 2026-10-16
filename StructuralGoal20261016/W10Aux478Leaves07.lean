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
theorem normalizedLeaf224 : AdaptiveCoverage.normalize SL cell471 = normal460 := by
  calc
    AdaptiveCoverage.normalize SL cell471 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell471)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell471)).symm
    _ = normal460 := by rfl

theorem numeric224 : ForcedCoverage2.dispatch (fun _ => payload224) normal460 46 = true := by
  decide +kernel

theorem coveredLeaf224 : CovBy 9 PR (Pg cN 9 BS TS) cell471 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf224]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload224) normal460 46 numeric224
theorem normalizedLeaf225 : AdaptiveCoverage.normalize SL cell473 = normal462 := by
  calc
    AdaptiveCoverage.normalize SL cell473 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell473)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell473)).symm
    _ = normal462 := by rfl

theorem numeric225 : ForcedCoverage2.dispatch (fun _ => payload225) normal462 46 = true := by
  decide +kernel

theorem coveredLeaf225 : CovBy 9 PR (Pg cN 9 BS TS) cell473 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf225]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload225) normal462 46 numeric225
theorem normalizedLeaf226 : AdaptiveCoverage.normalize SL cell475 = normal464 := by
  calc
    AdaptiveCoverage.normalize SL cell475 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell475)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell475)).symm
    _ = normal464 := by rfl

theorem numeric226 : ForcedCoverage2.dispatch (fun _ => payload226) normal464 46 = true := by
  decide +kernel

theorem coveredLeaf226 : CovBy 9 PR (Pg cN 9 BS TS) cell475 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf226]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload226) normal464 46 numeric226
theorem normalizedLeaf227 : AdaptiveCoverage.normalize SL cell477 = normal466 := by
  calc
    AdaptiveCoverage.normalize SL cell477 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell477)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell477)).symm
    _ = normal466 := by rfl

theorem numeric227 : ForcedCoverage2.dispatch (fun _ => payload227) normal466 46 = true := by
  decide +kernel

theorem coveredLeaf227 : CovBy 9 PR (Pg cN 9 BS TS) cell477 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf227]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload227) normal466 46 numeric227
theorem normalizedLeaf228 : AdaptiveCoverage.normalize SL cell483 = normal470 := by
  calc
    AdaptiveCoverage.normalize SL cell483 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell483)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell483)).symm
    _ = normal470 := by rfl

theorem numeric228 : ForcedCoverage2.dispatch (fun _ => payload228) normal470 46 = true := by
  decide +kernel

theorem coveredLeaf228 : CovBy 9 PR (Pg cN 9 BS TS) cell483 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf228]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload228) normal470 46 numeric228
theorem normalizedLeaf229 : AdaptiveCoverage.normalize SL cell484 = normal471 := by
  calc
    AdaptiveCoverage.normalize SL cell484 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell484)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell484)).symm
    _ = normal471 := by rfl

theorem numeric229 : ForcedCoverage2.dispatch (fun _ => payload229) normal471 46 = true := by
  decide +kernel

theorem coveredLeaf229 : CovBy 9 PR (Pg cN 9 BS TS) cell484 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf229]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload229) normal471 46 numeric229
theorem normalizedLeaf230 : AdaptiveCoverage.normalize SL cell482 = normal472 := by
  calc
    AdaptiveCoverage.normalize SL cell482 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell482)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell482)).symm
    _ = normal472 := by rfl

theorem numeric230 : ForcedCoverage2.dispatch (fun _ => payload230) normal472 46 = true := by
  decide +kernel

theorem coveredLeaf230 : CovBy 9 PR (Pg cN 9 BS TS) cell482 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf230]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload230) normal472 46 numeric230
theorem normalizedLeaf231 : AdaptiveCoverage.normalize SL cell487 = normal475 := by
  calc
    AdaptiveCoverage.normalize SL cell487 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell487)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell487)).symm
    _ = normal475 := by rfl

theorem numeric231 : ForcedCoverage2.dispatch (fun _ => payload231) normal475 46 = true := by
  decide +kernel

theorem coveredLeaf231 : CovBy 9 PR (Pg cN 9 BS TS) cell487 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf231]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload231) normal475 46 numeric231
theorem normalizedLeaf232 : AdaptiveCoverage.normalize SL cell488 = normal476 := by
  calc
    AdaptiveCoverage.normalize SL cell488 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell488)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell488)).symm
    _ = normal476 := by rfl

theorem numeric232 : ForcedCoverage2.dispatch (fun _ => payload232) normal476 46 = true := by
  decide +kernel

theorem coveredLeaf232 : CovBy 9 PR (Pg cN 9 BS TS) cell488 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf232]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload232) normal476 46 numeric232
theorem normalizedLeaf233 : AdaptiveCoverage.normalize SL cell486 = normal477 := by
  calc
    AdaptiveCoverage.normalize SL cell486 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell486)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell486)).symm
    _ = normal477 := by rfl

theorem numeric233 : ForcedCoverage2.dispatch (fun _ => payload233) normal477 46 = true := by
  decide +kernel

theorem coveredLeaf233 : CovBy 9 PR (Pg cN 9 BS TS) cell486 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf233]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload233) normal477 46 numeric233
theorem normalizedLeaf234 : AdaptiveCoverage.normalize SL cell489 = normal479 := by
  calc
    AdaptiveCoverage.normalize SL cell489 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell489)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell489)).symm
    _ = normal479 := by rfl

theorem numeric234 : ForcedCoverage2.dispatch (fun _ => payload234) normal479 46 = true := by
  decide +kernel

theorem coveredLeaf234 : CovBy 9 PR (Pg cN 9 BS TS) cell489 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf234]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload234) normal479 46 numeric234
theorem normalizedLeaf235 : AdaptiveCoverage.normalize SL cell490 = normal480 := by
  calc
    AdaptiveCoverage.normalize SL cell490 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell490)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell490)).symm
    _ = normal480 := by rfl

theorem numeric235 : ForcedCoverage2.dispatch (fun _ => payload235) normal480 46 = true := by
  decide +kernel

theorem coveredLeaf235 : CovBy 9 PR (Pg cN 9 BS TS) cell490 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf235]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload235) normal480 46 numeric235
theorem normalizedLeaf236 : AdaptiveCoverage.normalize SL cell493 = normal483 := by
  calc
    AdaptiveCoverage.normalize SL cell493 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell493)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell493)).symm
    _ = normal483 := by rfl

theorem numeric236 : ForcedCoverage2.dispatch (fun _ => payload236) normal483 46 = true := by
  decide +kernel

theorem coveredLeaf236 : CovBy 9 PR (Pg cN 9 BS TS) cell493 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf236]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload236) normal483 46 numeric236
theorem normalizedLeaf237 : AdaptiveCoverage.normalize SL cell495 = normal485 := by
  calc
    AdaptiveCoverage.normalize SL cell495 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell495)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell495)).symm
    _ = normal485 := by rfl

theorem numeric237 : ForcedCoverage2.dispatch (fun _ => payload237) normal485 46 = true := by
  decide +kernel

theorem coveredLeaf237 : CovBy 9 PR (Pg cN 9 BS TS) cell495 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf237]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload237) normal485 46 numeric237
theorem normalizedLeaf238 : AdaptiveCoverage.normalize SL cell497 = normal487 := by
  calc
    AdaptiveCoverage.normalize SL cell497 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell497)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell497)).symm
    _ = normal487 := by rfl

theorem numeric238 : ForcedCoverage2.dispatch (fun _ => payload238) normal487 46 = true := by
  decide +kernel

theorem coveredLeaf238 : CovBy 9 PR (Pg cN 9 BS TS) cell497 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf238]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload238) normal487 46 numeric238
theorem normalizedLeaf239 : AdaptiveCoverage.normalize SL cell498 = normal488 := by
  calc
    AdaptiveCoverage.normalize SL cell498 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell498)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell498)).symm
    _ = normal488 := by rfl

theorem numeric239 : ForcedCoverage2.dispatch (fun _ => payload239) normal488 46 = true := by
  decide +kernel

theorem coveredLeaf239 : CovBy 9 PR (Pg cN 9 BS TS) cell498 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf239]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload239) normal488 46 numeric239
theorem normalizedLeaf240 : AdaptiveCoverage.normalize SL cell492 = normal489 := by
  calc
    AdaptiveCoverage.normalize SL cell492 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell492)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell492)).symm
    _ = normal489 := by rfl

theorem numeric240 : ForcedCoverage2.dispatch (fun _ => payload240) normal489 46 = true := by
  decide +kernel

theorem coveredLeaf240 : CovBy 9 PR (Pg cN 9 BS TS) cell492 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf240]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload240) normal489 46 numeric240
theorem normalizedLeaf241 : AdaptiveCoverage.normalize SL cell499 = normal491 := by
  calc
    AdaptiveCoverage.normalize SL cell499 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell499)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell499)).symm
    _ = normal491 := by rfl

theorem numeric241 : ForcedCoverage2.dispatch (fun _ => payload241) normal491 46 = true := by
  decide +kernel

theorem coveredLeaf241 : CovBy 9 PR (Pg cN 9 BS TS) cell499 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf241]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload241) normal491 46 numeric241
theorem normalizedLeaf242 : AdaptiveCoverage.normalize SL cell509 = normal497 := by
  calc
    AdaptiveCoverage.normalize SL cell509 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell509)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell509)).symm
    _ = normal497 := by rfl

theorem numeric242 : ForcedCoverage2.dispatch (fun _ => payload242) normal497 46 = true := by
  decide +kernel

theorem coveredLeaf242 : CovBy 9 PR (Pg cN 9 BS TS) cell509 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf242]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload242) normal497 46 numeric242
theorem normalizedLeaf243 : AdaptiveCoverage.normalize SL cell510 = normal498 := by
  calc
    AdaptiveCoverage.normalize SL cell510 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell510)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell510)).symm
    _ = normal498 := by rfl

theorem numeric243 : ForcedCoverage2.dispatch (fun _ => payload243) normal498 46 = true := by
  decide +kernel

theorem coveredLeaf243 : CovBy 9 PR (Pg cN 9 BS TS) cell510 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf243]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload243) normal498 46 numeric243
theorem normalizedLeaf244 : AdaptiveCoverage.normalize SL cell508 = normal499 := by
  calc
    AdaptiveCoverage.normalize SL cell508 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell508)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell508)).symm
    _ = normal499 := by rfl

theorem numeric244 : ForcedCoverage2.dispatch (fun _ => payload244) normal499 46 = true := by
  decide +kernel

theorem coveredLeaf244 : CovBy 9 PR (Pg cN 9 BS TS) cell508 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf244]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload244) normal499 46 numeric244
theorem normalizedLeaf245 : AdaptiveCoverage.normalize SL cell506 = normal500 := by
  calc
    AdaptiveCoverage.normalize SL cell506 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell506)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell506)).symm
    _ = normal500 := by rfl

theorem numeric245 : ForcedCoverage2.dispatch (fun _ => payload245) normal500 46 = true := by
  decide +kernel

theorem coveredLeaf245 : CovBy 9 PR (Pg cN 9 BS TS) cell506 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf245]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload245) normal500 46 numeric245
theorem normalizedLeaf246 : AdaptiveCoverage.normalize SL cell504 = normal501 := by
  calc
    AdaptiveCoverage.normalize SL cell504 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell504)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell504)).symm
    _ = normal501 := by rfl

theorem numeric246 : ForcedCoverage2.dispatch (fun _ => payload246) normal501 46 = true := by
  decide +kernel

theorem coveredLeaf246 : CovBy 9 PR (Pg cN 9 BS TS) cell504 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf246]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload246) normal501 46 numeric246
theorem normalizedLeaf247 : AdaptiveCoverage.normalize SL cell519 = normal507 := by
  calc
    AdaptiveCoverage.normalize SL cell519 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell519)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell519)).symm
    _ = normal507 := by rfl

theorem numeric247 : ForcedCoverage2.dispatch (fun _ => payload247) normal507 46 = true := by
  decide +kernel

theorem coveredLeaf247 : CovBy 9 PR (Pg cN 9 BS TS) cell519 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf247]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload247) normal507 46 numeric247
theorem normalizedLeaf248 : AdaptiveCoverage.normalize SL cell520 = normal508 := by
  calc
    AdaptiveCoverage.normalize SL cell520 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell520)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell520)).symm
    _ = normal508 := by rfl

theorem numeric248 : ForcedCoverage2.dispatch (fun _ => payload248) normal508 46 = true := by
  decide +kernel

theorem coveredLeaf248 : CovBy 9 PR (Pg cN 9 BS TS) cell520 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf248]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload248) normal508 46 numeric248
theorem normalizedLeaf249 : AdaptiveCoverage.normalize SL cell518 = normal509 := by
  calc
    AdaptiveCoverage.normalize SL cell518 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell518)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell518)).symm
    _ = normal509 := by rfl

theorem numeric249 : ForcedCoverage2.dispatch (fun _ => payload249) normal509 46 = true := by
  decide +kernel

theorem coveredLeaf249 : CovBy 9 PR (Pg cN 9 BS TS) cell518 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf249]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload249) normal509 46 numeric249
theorem normalizedLeaf250 : AdaptiveCoverage.normalize SL cell516 = normal510 := by
  calc
    AdaptiveCoverage.normalize SL cell516 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell516)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell516)).symm
    _ = normal510 := by rfl

theorem numeric250 : ForcedCoverage2.dispatch (fun _ => payload250) normal510 46 = true := by
  decide +kernel

theorem coveredLeaf250 : CovBy 9 PR (Pg cN 9 BS TS) cell516 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf250]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload250) normal510 46 numeric250
theorem normalizedLeaf251 : AdaptiveCoverage.normalize SL cell514 = normal511 := by
  calc
    AdaptiveCoverage.normalize SL cell514 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell514)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell514)).symm
    _ = normal511 := by rfl

theorem numeric251 : ForcedCoverage2.dispatch (fun _ => payload251) normal511 46 = true := by
  decide +kernel

theorem coveredLeaf251 : CovBy 9 PR (Pg cN 9 BS TS) cell514 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf251]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload251) normal511 46 numeric251
theorem normalizedLeaf252 : AdaptiveCoverage.normalize SL cell527 = normal516 := by
  calc
    AdaptiveCoverage.normalize SL cell527 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell527)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell527)).symm
    _ = normal516 := by rfl

theorem numeric252 : ForcedCoverage2.dispatch (fun _ => payload252) normal516 46 = true := by
  decide +kernel

theorem coveredLeaf252 : CovBy 9 PR (Pg cN 9 BS TS) cell527 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf252]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload252) normal516 46 numeric252
theorem normalizedLeaf253 : AdaptiveCoverage.normalize SL cell529 = normal518 := by
  calc
    AdaptiveCoverage.normalize SL cell529 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell529)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell529)).symm
    _ = normal518 := by rfl

theorem numeric253 : ForcedCoverage2.dispatch (fun _ => payload253) normal518 46 = true := by
  decide +kernel

theorem coveredLeaf253 : CovBy 9 PR (Pg cN 9 BS TS) cell529 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf253]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload253) normal518 46 numeric253
theorem normalizedLeaf254 : AdaptiveCoverage.normalize SL cell531 = normal520 := by
  calc
    AdaptiveCoverage.normalize SL cell531 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell531)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell531)).symm
    _ = normal520 := by rfl

theorem numeric254 : ForcedCoverage2.dispatch (fun _ => payload254) normal520 46 = true := by
  decide +kernel

theorem coveredLeaf254 : CovBy 9 PR (Pg cN 9 BS TS) cell531 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf254]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload254) normal520 46 numeric254
theorem normalizedLeaf255 : AdaptiveCoverage.normalize SL cell533 = normal522 := by
  calc
    AdaptiveCoverage.normalize SL cell533 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell533)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell533)).symm
    _ = normal522 := by rfl

theorem numeric255 : ForcedCoverage2.dispatch (fun _ => payload255) normal522 46 = true := by
  decide +kernel

theorem coveredLeaf255 : CovBy 9 PR (Pg cN 9 BS TS) cell533 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf255]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload255) normal522 46 numeric255

set_option pp.fullNames true
#print axioms normalizedLeaf224
#print axioms numeric224
#print axioms coveredLeaf224
#print axioms normalizedLeaf225
#print axioms numeric225
#print axioms coveredLeaf225
#print axioms normalizedLeaf226
#print axioms numeric226
#print axioms coveredLeaf226
#print axioms normalizedLeaf227
#print axioms numeric227
#print axioms coveredLeaf227
#print axioms normalizedLeaf228
#print axioms numeric228
#print axioms coveredLeaf228
#print axioms normalizedLeaf229
#print axioms numeric229
#print axioms coveredLeaf229
#print axioms normalizedLeaf230
#print axioms numeric230
#print axioms coveredLeaf230
#print axioms normalizedLeaf231
#print axioms numeric231
#print axioms coveredLeaf231
#print axioms normalizedLeaf232
#print axioms numeric232
#print axioms coveredLeaf232
#print axioms normalizedLeaf233
#print axioms numeric233
#print axioms coveredLeaf233
#print axioms normalizedLeaf234
#print axioms numeric234
#print axioms coveredLeaf234
#print axioms normalizedLeaf235
#print axioms numeric235
#print axioms coveredLeaf235
#print axioms normalizedLeaf236
#print axioms numeric236
#print axioms coveredLeaf236
#print axioms normalizedLeaf237
#print axioms numeric237
#print axioms coveredLeaf237
#print axioms normalizedLeaf238
#print axioms numeric238
#print axioms coveredLeaf238
#print axioms normalizedLeaf239
#print axioms numeric239
#print axioms coveredLeaf239
#print axioms normalizedLeaf240
#print axioms numeric240
#print axioms coveredLeaf240
#print axioms normalizedLeaf241
#print axioms numeric241
#print axioms coveredLeaf241
#print axioms normalizedLeaf242
#print axioms numeric242
#print axioms coveredLeaf242
#print axioms normalizedLeaf243
#print axioms numeric243
#print axioms coveredLeaf243
#print axioms normalizedLeaf244
#print axioms numeric244
#print axioms coveredLeaf244
#print axioms normalizedLeaf245
#print axioms numeric245
#print axioms coveredLeaf245
#print axioms normalizedLeaf246
#print axioms numeric246
#print axioms coveredLeaf246
#print axioms normalizedLeaf247
#print axioms numeric247
#print axioms coveredLeaf247
#print axioms normalizedLeaf248
#print axioms numeric248
#print axioms coveredLeaf248
#print axioms normalizedLeaf249
#print axioms numeric249
#print axioms coveredLeaf249
#print axioms normalizedLeaf250
#print axioms numeric250
#print axioms coveredLeaf250
#print axioms normalizedLeaf251
#print axioms numeric251
#print axioms coveredLeaf251
#print axioms normalizedLeaf252
#print axioms numeric252
#print axioms coveredLeaf252
#print axioms normalizedLeaf253
#print axioms numeric253
#print axioms coveredLeaf253
#print axioms normalizedLeaf254
#print axioms numeric254
#print axioms coveredLeaf254
#print axioms normalizedLeaf255
#print axioms numeric255
#print axioms coveredLeaf255
end StructuralGoal20261016.W10Aux478
end
