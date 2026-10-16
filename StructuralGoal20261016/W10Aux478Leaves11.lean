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
theorem normalizedLeaf352 : AdaptiveCoverage.normalize SL cell721 = normal713 := by
  calc
    AdaptiveCoverage.normalize SL cell721 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell721)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell721)).symm
    _ = normal713 := by rfl

theorem numeric352 : ForcedCoverage2.dispatch (fun _ => payload352) normal713 46 = true := by
  decide +kernel

theorem coveredLeaf352 : CovBy 9 PR (Pg cN 9 BS TS) cell721 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf352]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload352) normal713 46 numeric352
theorem normalizedLeaf353 : AdaptiveCoverage.normalize SL cell722 = normal714 := by
  calc
    AdaptiveCoverage.normalize SL cell722 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell722)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell722)).symm
    _ = normal714 := by rfl

theorem numeric353 : ForcedCoverage2.dispatch (fun _ => payload353) normal714 46 = true := by
  decide +kernel

theorem coveredLeaf353 : CovBy 9 PR (Pg cN 9 BS TS) cell722 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf353]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload353) normal714 46 numeric353
theorem normalizedLeaf354 : AdaptiveCoverage.normalize SL cell714 = normal715 := by
  calc
    AdaptiveCoverage.normalize SL cell714 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell714)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell714)).symm
    _ = normal715 := by rfl

theorem numeric354 : ForcedCoverage2.dispatch (fun _ => payload354) normal715 46 = true := by
  decide +kernel

theorem coveredLeaf354 : CovBy 9 PR (Pg cN 9 BS TS) cell714 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf354]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload354) normal715 46 numeric354
theorem normalizedLeaf355 : AdaptiveCoverage.normalize SL cell725 = normal718 := by
  calc
    AdaptiveCoverage.normalize SL cell725 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell725)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell725)).symm
    _ = normal718 := by rfl

theorem numeric355 : ForcedCoverage2.dispatch (fun _ => payload355) normal718 46 = true := by
  decide +kernel

theorem coveredLeaf355 : CovBy 9 PR (Pg cN 9 BS TS) cell725 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf355]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload355) normal718 46 numeric355
theorem normalizedLeaf356 : AdaptiveCoverage.normalize SL cell729 = normal721 := by
  calc
    AdaptiveCoverage.normalize SL cell729 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell729)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell729)).symm
    _ = normal721 := by rfl

theorem numeric356 : ForcedCoverage2.dispatch (fun _ => payload356) normal721 46 = true := by
  decide +kernel

theorem coveredLeaf356 : CovBy 9 PR (Pg cN 9 BS TS) cell729 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf356]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload356) normal721 46 numeric356
theorem normalizedLeaf357 : AdaptiveCoverage.normalize SL cell731 = normal723 := by
  calc
    AdaptiveCoverage.normalize SL cell731 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell731)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell731)).symm
    _ = normal723 := by rfl

theorem numeric357 : ForcedCoverage2.dispatch (fun _ => payload357) normal723 46 = true := by
  decide +kernel

theorem coveredLeaf357 : CovBy 9 PR (Pg cN 9 BS TS) cell731 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf357]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload357) normal723 46 numeric357
theorem normalizedLeaf358 : AdaptiveCoverage.normalize SL cell732 = normal724 := by
  calc
    AdaptiveCoverage.normalize SL cell732 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell732)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell732)).symm
    _ = normal724 := by rfl

theorem numeric358 : ForcedCoverage2.dispatch (fun _ => payload358) normal724 46 = true := by
  decide +kernel

theorem coveredLeaf358 : CovBy 9 PR (Pg cN 9 BS TS) cell732 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf358]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload358) normal724 46 numeric358
theorem normalizedLeaf359 : AdaptiveCoverage.normalize SL cell728 = normal725 := by
  calc
    AdaptiveCoverage.normalize SL cell728 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell728)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell728)).symm
    _ = normal725 := by rfl

theorem numeric359 : ForcedCoverage2.dispatch (fun _ => payload359) normal725 46 = true := by
  decide +kernel

theorem coveredLeaf359 : CovBy 9 PR (Pg cN 9 BS TS) cell728 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf359]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload359) normal725 46 numeric359
theorem normalizedLeaf360 : AdaptiveCoverage.normalize SL cell733 = normal727 := by
  calc
    AdaptiveCoverage.normalize SL cell733 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell733)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell733)).symm
    _ = normal727 := by rfl

theorem numeric360 : ForcedCoverage2.dispatch (fun _ => payload360) normal727 46 = true := by
  decide +kernel

theorem coveredLeaf360 : CovBy 9 PR (Pg cN 9 BS TS) cell733 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf360]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload360) normal727 46 numeric360
theorem normalizedLeaf361 : AdaptiveCoverage.normalize SL cell737 = normal730 := by
  calc
    AdaptiveCoverage.normalize SL cell737 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell737)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell737)).symm
    _ = normal730 := by rfl

theorem numeric361 : ForcedCoverage2.dispatch (fun _ => payload361) normal730 46 = true := by
  decide +kernel

theorem coveredLeaf361 : CovBy 9 PR (Pg cN 9 BS TS) cell737 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf361]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload361) normal730 46 numeric361
theorem normalizedLeaf362 : AdaptiveCoverage.normalize SL cell739 = normal732 := by
  calc
    AdaptiveCoverage.normalize SL cell739 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell739)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell739)).symm
    _ = normal732 := by rfl

theorem numeric362 : ForcedCoverage2.dispatch (fun _ => payload362) normal732 46 = true := by
  decide +kernel

theorem coveredLeaf362 : CovBy 9 PR (Pg cN 9 BS TS) cell739 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf362]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload362) normal732 46 numeric362
theorem normalizedLeaf363 : AdaptiveCoverage.normalize SL cell741 = normal734 := by
  calc
    AdaptiveCoverage.normalize SL cell741 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell741)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell741)).symm
    _ = normal734 := by rfl

theorem numeric363 : ForcedCoverage2.dispatch (fun _ => payload363) normal734 46 = true := by
  decide +kernel

theorem coveredLeaf363 : CovBy 9 PR (Pg cN 9 BS TS) cell741 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf363]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload363) normal734 46 numeric363
theorem normalizedLeaf364 : AdaptiveCoverage.normalize SL cell743 = normal736 := by
  calc
    AdaptiveCoverage.normalize SL cell743 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell743)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell743)).symm
    _ = normal736 := by rfl

theorem numeric364 : ForcedCoverage2.dispatch (fun _ => payload364) normal736 46 = true := by
  decide +kernel

theorem coveredLeaf364 : CovBy 9 PR (Pg cN 9 BS TS) cell743 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf364]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload364) normal736 46 numeric364
theorem normalizedLeaf365 : AdaptiveCoverage.normalize SL cell744 = normal737 := by
  calc
    AdaptiveCoverage.normalize SL cell744 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell744)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell744)).symm
    _ = normal737 := by rfl

theorem numeric365 : ForcedCoverage2.dispatch (fun _ => payload365) normal737 46 = true := by
  decide +kernel

theorem coveredLeaf365 : CovBy 9 PR (Pg cN 9 BS TS) cell744 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf365]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload365) normal737 46 numeric365
theorem normalizedLeaf366 : AdaptiveCoverage.normalize SL cell736 = normal738 := by
  calc
    AdaptiveCoverage.normalize SL cell736 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell736)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell736)).symm
    _ = normal738 := by rfl

theorem numeric366 : ForcedCoverage2.dispatch (fun _ => payload366) normal738 46 = true := by
  decide +kernel

theorem coveredLeaf366 : CovBy 9 PR (Pg cN 9 BS TS) cell736 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf366]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload366) normal738 46 numeric366
theorem normalizedLeaf367 : AdaptiveCoverage.normalize SL cell747 = normal741 := by
  calc
    AdaptiveCoverage.normalize SL cell747 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell747)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell747)).symm
    _ = normal741 := by rfl

theorem numeric367 : ForcedCoverage2.dispatch (fun _ => payload367) normal741 46 = true := by
  decide +kernel

theorem coveredLeaf367 : CovBy 9 PR (Pg cN 9 BS TS) cell747 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf367]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload367) normal741 46 numeric367
theorem normalizedLeaf368 : AdaptiveCoverage.normalize SL cell748 = normal742 := by
  calc
    AdaptiveCoverage.normalize SL cell748 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell748)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell748)).symm
    _ = normal742 := by rfl

theorem numeric368 : ForcedCoverage2.dispatch (fun _ => payload368) normal742 46 = true := by
  decide +kernel

theorem coveredLeaf368 : CovBy 9 PR (Pg cN 9 BS TS) cell748 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf368]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload368) normal742 46 numeric368
theorem normalizedLeaf369 : AdaptiveCoverage.normalize SL cell749 = normal744 := by
  calc
    AdaptiveCoverage.normalize SL cell749 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell749)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell749)).symm
    _ = normal744 := by rfl

theorem numeric369 : ForcedCoverage2.dispatch (fun _ => payload369) normal744 46 = true := by
  decide +kernel

theorem coveredLeaf369 : CovBy 9 PR (Pg cN 9 BS TS) cell749 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf369]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload369) normal744 46 numeric369
theorem normalizedLeaf370 : AdaptiveCoverage.normalize SL cell750 = normal745 := by
  calc
    AdaptiveCoverage.normalize SL cell750 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell750)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell750)).symm
    _ = normal745 := by rfl

theorem numeric370 : ForcedCoverage2.dispatch (fun _ => payload370) normal745 46 = true := by
  decide +kernel

theorem coveredLeaf370 : CovBy 9 PR (Pg cN 9 BS TS) cell750 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf370]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload370) normal745 46 numeric370
theorem normalizedLeaf371 : AdaptiveCoverage.normalize SL cell769 = normal756 := by
  calc
    AdaptiveCoverage.normalize SL cell769 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell769)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell769)).symm
    _ = normal756 := by rfl

theorem numeric371 : ForcedCoverage2.dispatch (fun _ => payload371) normal756 46 = true := by
  decide +kernel

theorem coveredLeaf371 : CovBy 9 PR (Pg cN 9 BS TS) cell769 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf371]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload371) normal756 46 numeric371
theorem normalizedLeaf372 : AdaptiveCoverage.normalize SL cell770 = normal757 := by
  calc
    AdaptiveCoverage.normalize SL cell770 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell770)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell770)).symm
    _ = normal757 := by rfl

theorem numeric372 : ForcedCoverage2.dispatch (fun _ => payload372) normal757 46 = true := by
  decide +kernel

theorem coveredLeaf372 : CovBy 9 PR (Pg cN 9 BS TS) cell770 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf372]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload372) normal757 46 numeric372
theorem normalizedLeaf373 : AdaptiveCoverage.normalize SL cell771 = normal759 := by
  calc
    AdaptiveCoverage.normalize SL cell771 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell771)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell771)).symm
    _ = normal759 := by rfl

theorem numeric373 : ForcedCoverage2.dispatch (fun _ => payload373) normal759 46 = true := by
  decide +kernel

theorem coveredLeaf373 : CovBy 9 PR (Pg cN 9 BS TS) cell771 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf373]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload373) normal759 46 numeric373
theorem normalizedLeaf374 : AdaptiveCoverage.normalize SL cell772 = normal760 := by
  calc
    AdaptiveCoverage.normalize SL cell772 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell772)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell772)).symm
    _ = normal760 := by rfl

theorem numeric374 : ForcedCoverage2.dispatch (fun _ => payload374) normal760 46 = true := by
  decide +kernel

theorem coveredLeaf374 : CovBy 9 PR (Pg cN 9 BS TS) cell772 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf374]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload374) normal760 46 numeric374
theorem normalizedLeaf375 : AdaptiveCoverage.normalize SL cell779 = normal765 := by
  calc
    AdaptiveCoverage.normalize SL cell779 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell779)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell779)).symm
    _ = normal765 := by rfl

theorem numeric375 : ForcedCoverage2.dispatch (fun _ => payload375) normal765 46 = true := by
  decide +kernel

theorem coveredLeaf375 : CovBy 9 PR (Pg cN 9 BS TS) cell779 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf375]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload375) normal765 46 numeric375
theorem normalizedLeaf376 : AdaptiveCoverage.normalize SL cell781 = normal767 := by
  calc
    AdaptiveCoverage.normalize SL cell781 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell781)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell781)).symm
    _ = normal767 := by rfl

theorem numeric376 : ForcedCoverage2.dispatch (fun _ => payload376) normal767 46 = true := by
  decide +kernel

theorem coveredLeaf376 : CovBy 9 PR (Pg cN 9 BS TS) cell781 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf376]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload376) normal767 46 numeric376
theorem normalizedLeaf377 : AdaptiveCoverage.normalize SL cell782 = normal768 := by
  calc
    AdaptiveCoverage.normalize SL cell782 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell782)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell782)).symm
    _ = normal768 := by rfl

theorem numeric377 : ForcedCoverage2.dispatch (fun _ => payload377) normal768 46 = true := by
  decide +kernel

theorem coveredLeaf377 : CovBy 9 PR (Pg cN 9 BS TS) cell782 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf377]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload377) normal768 46 numeric377
theorem normalizedLeaf378 : AdaptiveCoverage.normalize SL cell783 = normal770 := by
  calc
    AdaptiveCoverage.normalize SL cell783 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell783)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell783)).symm
    _ = normal770 := by rfl

theorem numeric378 : ForcedCoverage2.dispatch (fun _ => payload378) normal770 46 = true := by
  decide +kernel

theorem coveredLeaf378 : CovBy 9 PR (Pg cN 9 BS TS) cell783 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf378]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload378) normal770 46 numeric378
theorem normalizedLeaf379 : AdaptiveCoverage.normalize SL cell785 = normal772 := by
  calc
    AdaptiveCoverage.normalize SL cell785 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell785)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell785)).symm
    _ = normal772 := by rfl

theorem numeric379 : ForcedCoverage2.dispatch (fun _ => payload379) normal772 46 = true := by
  decide +kernel

theorem coveredLeaf379 : CovBy 9 PR (Pg cN 9 BS TS) cell785 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf379]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload379) normal772 46 numeric379
theorem normalizedLeaf380 : AdaptiveCoverage.normalize SL cell786 = normal773 := by
  calc
    AdaptiveCoverage.normalize SL cell786 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell786)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell786)).symm
    _ = normal773 := by rfl

theorem numeric380 : ForcedCoverage2.dispatch (fun _ => payload380) normal773 46 = true := by
  decide +kernel

theorem coveredLeaf380 : CovBy 9 PR (Pg cN 9 BS TS) cell786 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf380]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload380) normal773 46 numeric380
theorem normalizedLeaf381 : AdaptiveCoverage.normalize SL cell776 = normal774 := by
  calc
    AdaptiveCoverage.normalize SL cell776 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell776)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell776)).symm
    _ = normal774 := by rfl

theorem numeric381 : ForcedCoverage2.dispatch (fun _ => payload381) normal774 46 = true := by
  decide +kernel

theorem coveredLeaf381 : CovBy 9 PR (Pg cN 9 BS TS) cell776 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf381]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload381) normal774 46 numeric381
theorem normalizedLeaf382 : AdaptiveCoverage.normalize SL cell787 = normal776 := by
  calc
    AdaptiveCoverage.normalize SL cell787 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell787)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell787)).symm
    _ = normal776 := by rfl

theorem numeric382 : ForcedCoverage2.dispatch (fun _ => payload382) normal776 46 = true := by
  decide +kernel

theorem coveredLeaf382 : CovBy 9 PR (Pg cN 9 BS TS) cell787 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf382]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload382) normal776 46 numeric382
theorem normalizedLeaf383 : AdaptiveCoverage.normalize SL cell789 = normal778 := by
  calc
    AdaptiveCoverage.normalize SL cell789 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell789)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell789)).symm
    _ = normal778 := by rfl

theorem numeric383 : ForcedCoverage2.dispatch (fun _ => payload383) normal778 46 = true := by
  decide +kernel

theorem coveredLeaf383 : CovBy 9 PR (Pg cN 9 BS TS) cell789 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf383]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload383) normal778 46 numeric383

set_option pp.fullNames true
#print axioms normalizedLeaf352
#print axioms numeric352
#print axioms coveredLeaf352
#print axioms normalizedLeaf353
#print axioms numeric353
#print axioms coveredLeaf353
#print axioms normalizedLeaf354
#print axioms numeric354
#print axioms coveredLeaf354
#print axioms normalizedLeaf355
#print axioms numeric355
#print axioms coveredLeaf355
#print axioms normalizedLeaf356
#print axioms numeric356
#print axioms coveredLeaf356
#print axioms normalizedLeaf357
#print axioms numeric357
#print axioms coveredLeaf357
#print axioms normalizedLeaf358
#print axioms numeric358
#print axioms coveredLeaf358
#print axioms normalizedLeaf359
#print axioms numeric359
#print axioms coveredLeaf359
#print axioms normalizedLeaf360
#print axioms numeric360
#print axioms coveredLeaf360
#print axioms normalizedLeaf361
#print axioms numeric361
#print axioms coveredLeaf361
#print axioms normalizedLeaf362
#print axioms numeric362
#print axioms coveredLeaf362
#print axioms normalizedLeaf363
#print axioms numeric363
#print axioms coveredLeaf363
#print axioms normalizedLeaf364
#print axioms numeric364
#print axioms coveredLeaf364
#print axioms normalizedLeaf365
#print axioms numeric365
#print axioms coveredLeaf365
#print axioms normalizedLeaf366
#print axioms numeric366
#print axioms coveredLeaf366
#print axioms normalizedLeaf367
#print axioms numeric367
#print axioms coveredLeaf367
#print axioms normalizedLeaf368
#print axioms numeric368
#print axioms coveredLeaf368
#print axioms normalizedLeaf369
#print axioms numeric369
#print axioms coveredLeaf369
#print axioms normalizedLeaf370
#print axioms numeric370
#print axioms coveredLeaf370
#print axioms normalizedLeaf371
#print axioms numeric371
#print axioms coveredLeaf371
#print axioms normalizedLeaf372
#print axioms numeric372
#print axioms coveredLeaf372
#print axioms normalizedLeaf373
#print axioms numeric373
#print axioms coveredLeaf373
#print axioms normalizedLeaf374
#print axioms numeric374
#print axioms coveredLeaf374
#print axioms normalizedLeaf375
#print axioms numeric375
#print axioms coveredLeaf375
#print axioms normalizedLeaf376
#print axioms numeric376
#print axioms coveredLeaf376
#print axioms normalizedLeaf377
#print axioms numeric377
#print axioms coveredLeaf377
#print axioms normalizedLeaf378
#print axioms numeric378
#print axioms coveredLeaf378
#print axioms normalizedLeaf379
#print axioms numeric379
#print axioms coveredLeaf379
#print axioms normalizedLeaf380
#print axioms numeric380
#print axioms coveredLeaf380
#print axioms normalizedLeaf381
#print axioms numeric381
#print axioms coveredLeaf381
#print axioms normalizedLeaf382
#print axioms numeric382
#print axioms coveredLeaf382
#print axioms normalizedLeaf383
#print axioms numeric383
#print axioms coveredLeaf383
end StructuralGoal20261016.W10Aux478
end
