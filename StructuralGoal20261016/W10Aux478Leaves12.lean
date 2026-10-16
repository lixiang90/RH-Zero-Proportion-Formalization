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
theorem normalizedLeaf384 : AdaptiveCoverage.normalize SL cell790 = normal779 := by
  calc
    AdaptiveCoverage.normalize SL cell790 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell790)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell790)).symm
    _ = normal779 := by rfl

theorem numeric384 : ForcedCoverage2.dispatch (fun _ => payload384) normal779 46 = true := by
  decide +kernel

theorem coveredLeaf384 : CovBy 9 PR (Pg cN 9 BS TS) cell790 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf384]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload384) normal779 46 numeric384
theorem normalizedLeaf385 : AdaptiveCoverage.normalize SL cell799 = normal785 := by
  calc
    AdaptiveCoverage.normalize SL cell799 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell799)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell799)).symm
    _ = normal785 := by rfl

theorem numeric385 : ForcedCoverage2.dispatch (fun _ => payload385) normal785 46 = true := by
  decide +kernel

theorem coveredLeaf385 : CovBy 9 PR (Pg cN 9 BS TS) cell799 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf385]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload385) normal785 46 numeric385
theorem normalizedLeaf386 : AdaptiveCoverage.normalize SL cell801 = normal787 := by
  calc
    AdaptiveCoverage.normalize SL cell801 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell801)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell801)).symm
    _ = normal787 := by rfl

theorem numeric386 : ForcedCoverage2.dispatch (fun _ => payload386) normal787 46 = true := by
  decide +kernel

theorem coveredLeaf386 : CovBy 9 PR (Pg cN 9 BS TS) cell801 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf386]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload386) normal787 46 numeric386
theorem normalizedLeaf387 : AdaptiveCoverage.normalize SL cell802 = normal788 := by
  calc
    AdaptiveCoverage.normalize SL cell802 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell802)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell802)).symm
    _ = normal788 := by rfl

theorem numeric387 : ForcedCoverage2.dispatch (fun _ => payload387) normal788 46 = true := by
  decide +kernel

theorem coveredLeaf387 : CovBy 9 PR (Pg cN 9 BS TS) cell802 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf387]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload387) normal788 46 numeric387
theorem normalizedLeaf388 : AdaptiveCoverage.normalize SL cell803 = normal790 := by
  calc
    AdaptiveCoverage.normalize SL cell803 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell803)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell803)).symm
    _ = normal790 := by rfl

theorem numeric388 : ForcedCoverage2.dispatch (fun _ => payload388) normal790 46 = true := by
  decide +kernel

theorem coveredLeaf388 : CovBy 9 PR (Pg cN 9 BS TS) cell803 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf388]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload388) normal790 46 numeric388
theorem normalizedLeaf389 : AdaptiveCoverage.normalize SL cell805 = normal792 := by
  calc
    AdaptiveCoverage.normalize SL cell805 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell805)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell805)).symm
    _ = normal792 := by rfl

theorem numeric389 : ForcedCoverage2.dispatch (fun _ => payload389) normal792 46 = true := by
  decide +kernel

theorem coveredLeaf389 : CovBy 9 PR (Pg cN 9 BS TS) cell805 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf389]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload389) normal792 46 numeric389
theorem normalizedLeaf390 : AdaptiveCoverage.normalize SL cell806 = normal793 := by
  calc
    AdaptiveCoverage.normalize SL cell806 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell806)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell806)).symm
    _ = normal793 := by rfl

theorem numeric390 : ForcedCoverage2.dispatch (fun _ => payload390) normal793 46 = true := by
  decide +kernel

theorem coveredLeaf390 : CovBy 9 PR (Pg cN 9 BS TS) cell806 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf390]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload390) normal793 46 numeric390
theorem normalizedLeaf391 : AdaptiveCoverage.normalize SL cell796 = normal794 := by
  calc
    AdaptiveCoverage.normalize SL cell796 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell796)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell796)).symm
    _ = normal794 := by rfl

theorem numeric391 : ForcedCoverage2.dispatch (fun _ => payload391) normal794 46 = true := by
  decide +kernel

theorem coveredLeaf391 : CovBy 9 PR (Pg cN 9 BS TS) cell796 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf391]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload391) normal794 46 numeric391
theorem normalizedLeaf392 : AdaptiveCoverage.normalize SL cell794 = normal795 := by
  calc
    AdaptiveCoverage.normalize SL cell794 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell794)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell794)).symm
    _ = normal795 := by rfl

theorem numeric392 : ForcedCoverage2.dispatch (fun _ => payload392) normal795 46 = true := by
  decide +kernel

theorem coveredLeaf392 : CovBy 9 PR (Pg cN 9 BS TS) cell794 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf392]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload392) normal795 46 numeric392
theorem normalizedLeaf393 : AdaptiveCoverage.normalize SL cell807 = normal797 := by
  calc
    AdaptiveCoverage.normalize SL cell807 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell807)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell807)).symm
    _ = normal797 := by rfl

theorem numeric393 : ForcedCoverage2.dispatch (fun _ => payload393) normal797 46 = true := by
  decide +kernel

theorem coveredLeaf393 : CovBy 9 PR (Pg cN 9 BS TS) cell807 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf393]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload393) normal797 46 numeric393
theorem normalizedLeaf394 : AdaptiveCoverage.normalize SL cell809 = normal799 := by
  calc
    AdaptiveCoverage.normalize SL cell809 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell809)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell809)).symm
    _ = normal799 := by rfl

theorem numeric394 : ForcedCoverage2.dispatch (fun _ => payload394) normal799 46 = true := by
  decide +kernel

theorem coveredLeaf394 : CovBy 9 PR (Pg cN 9 BS TS) cell809 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf394]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload394) normal799 46 numeric394
theorem normalizedLeaf395 : AdaptiveCoverage.normalize SL cell810 = normal800 := by
  calc
    AdaptiveCoverage.normalize SL cell810 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell810)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell810)).symm
    _ = normal800 := by rfl

theorem numeric395 : ForcedCoverage2.dispatch (fun _ => payload395) normal800 46 = true := by
  decide +kernel

theorem coveredLeaf395 : CovBy 9 PR (Pg cN 9 BS TS) cell810 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf395]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload395) normal800 46 numeric395
theorem normalizedLeaf396 : AdaptiveCoverage.normalize SL cell821 = normal807 := by
  calc
    AdaptiveCoverage.normalize SL cell821 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell821)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell821)).symm
    _ = normal807 := by rfl

theorem numeric396 : ForcedCoverage2.dispatch (fun _ => payload396) normal807 46 = true := by
  decide +kernel

theorem coveredLeaf396 : CovBy 9 PR (Pg cN 9 BS TS) cell821 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf396]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload396) normal807 46 numeric396
theorem normalizedLeaf397 : AdaptiveCoverage.normalize SL cell823 = normal809 := by
  calc
    AdaptiveCoverage.normalize SL cell823 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell823)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell823)).symm
    _ = normal809 := by rfl

theorem numeric397 : ForcedCoverage2.dispatch (fun _ => payload397) normal809 46 = true := by
  decide +kernel

theorem coveredLeaf397 : CovBy 9 PR (Pg cN 9 BS TS) cell823 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf397]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload397) normal809 46 numeric397
theorem normalizedLeaf398 : AdaptiveCoverage.normalize SL cell824 = normal810 := by
  calc
    AdaptiveCoverage.normalize SL cell824 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell824)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell824)).symm
    _ = normal810 := by rfl

theorem numeric398 : ForcedCoverage2.dispatch (fun _ => payload398) normal810 46 = true := by
  decide +kernel

theorem coveredLeaf398 : CovBy 9 PR (Pg cN 9 BS TS) cell824 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf398]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload398) normal810 46 numeric398
theorem normalizedLeaf399 : AdaptiveCoverage.normalize SL cell825 = normal812 := by
  calc
    AdaptiveCoverage.normalize SL cell825 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell825)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell825)).symm
    _ = normal812 := by rfl

theorem numeric399 : ForcedCoverage2.dispatch (fun _ => payload399) normal812 46 = true := by
  decide +kernel

theorem coveredLeaf399 : CovBy 9 PR (Pg cN 9 BS TS) cell825 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf399]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload399) normal812 46 numeric399
theorem normalizedLeaf400 : AdaptiveCoverage.normalize SL cell827 = normal814 := by
  calc
    AdaptiveCoverage.normalize SL cell827 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell827)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell827)).symm
    _ = normal814 := by rfl

theorem numeric400 : ForcedCoverage2.dispatch (fun _ => payload400) normal814 46 = true := by
  decide +kernel

theorem coveredLeaf400 : CovBy 9 PR (Pg cN 9 BS TS) cell827 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf400]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload400) normal814 46 numeric400
theorem normalizedLeaf401 : AdaptiveCoverage.normalize SL cell828 = normal815 := by
  calc
    AdaptiveCoverage.normalize SL cell828 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell828)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell828)).symm
    _ = normal815 := by rfl

theorem numeric401 : ForcedCoverage2.dispatch (fun _ => payload401) normal815 46 = true := by
  decide +kernel

theorem coveredLeaf401 : CovBy 9 PR (Pg cN 9 BS TS) cell828 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf401]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload401) normal815 46 numeric401
theorem normalizedLeaf402 : AdaptiveCoverage.normalize SL cell818 = normal816 := by
  calc
    AdaptiveCoverage.normalize SL cell818 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell818)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell818)).symm
    _ = normal816 := by rfl

theorem numeric402 : ForcedCoverage2.dispatch (fun _ => payload402) normal816 46 = true := by
  decide +kernel

theorem coveredLeaf402 : CovBy 9 PR (Pg cN 9 BS TS) cell818 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf402]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload402) normal816 46 numeric402
theorem normalizedLeaf403 : AdaptiveCoverage.normalize SL cell816 = normal817 := by
  calc
    AdaptiveCoverage.normalize SL cell816 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell816)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell816)).symm
    _ = normal817 := by rfl

theorem numeric403 : ForcedCoverage2.dispatch (fun _ => payload403) normal817 46 = true := by
  decide +kernel

theorem coveredLeaf403 : CovBy 9 PR (Pg cN 9 BS TS) cell816 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf403]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload403) normal817 46 numeric403
theorem normalizedLeaf404 : AdaptiveCoverage.normalize SL cell814 = normal818 := by
  calc
    AdaptiveCoverage.normalize SL cell814 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell814)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell814)).symm
    _ = normal818 := by rfl

theorem numeric404 : ForcedCoverage2.dispatch (fun _ => payload404) normal818 46 = true := by
  decide +kernel

theorem coveredLeaf404 : CovBy 9 PR (Pg cN 9 BS TS) cell814 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf404]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload404) normal818 46 numeric404
theorem normalizedLeaf405 : AdaptiveCoverage.normalize SL cell829 = normal820 := by
  calc
    AdaptiveCoverage.normalize SL cell829 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell829)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell829)).symm
    _ = normal820 := by rfl

theorem numeric405 : ForcedCoverage2.dispatch (fun _ => payload405) normal820 46 = true := by
  decide +kernel

theorem coveredLeaf405 : CovBy 9 PR (Pg cN 9 BS TS) cell829 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf405]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload405) normal820 46 numeric405
theorem normalizedLeaf406 : AdaptiveCoverage.normalize SL cell831 = normal822 := by
  calc
    AdaptiveCoverage.normalize SL cell831 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell831)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell831)).symm
    _ = normal822 := by rfl

theorem numeric406 : ForcedCoverage2.dispatch (fun _ => payload406) normal822 46 = true := by
  decide +kernel

theorem coveredLeaf406 : CovBy 9 PR (Pg cN 9 BS TS) cell831 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf406]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload406) normal822 46 numeric406
theorem normalizedLeaf407 : AdaptiveCoverage.normalize SL cell832 = normal823 := by
  calc
    AdaptiveCoverage.normalize SL cell832 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell832)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell832)).symm
    _ = normal823 := by rfl

theorem numeric407 : ForcedCoverage2.dispatch (fun _ => payload407) normal823 46 = true := by
  decide +kernel

theorem coveredLeaf407 : CovBy 9 PR (Pg cN 9 BS TS) cell832 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf407]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload407) normal823 46 numeric407
theorem normalizedLeaf408 : AdaptiveCoverage.normalize SL cell845 = normal831 := by
  calc
    AdaptiveCoverage.normalize SL cell845 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell845)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell845)).symm
    _ = normal831 := by rfl

theorem numeric408 : ForcedCoverage2.dispatch (fun _ => payload408) normal831 46 = true := by
  decide +kernel

theorem coveredLeaf408 : CovBy 9 PR (Pg cN 9 BS TS) cell845 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf408]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload408) normal831 46 numeric408
theorem normalizedLeaf409 : AdaptiveCoverage.normalize SL cell846 = normal832 := by
  calc
    AdaptiveCoverage.normalize SL cell846 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell846)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell846)).symm
    _ = normal832 := by rfl

theorem numeric409 : ForcedCoverage2.dispatch (fun _ => payload409) normal832 46 = true := by
  decide +kernel

theorem coveredLeaf409 : CovBy 9 PR (Pg cN 9 BS TS) cell846 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf409]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload409) normal832 46 numeric409
theorem normalizedLeaf410 : AdaptiveCoverage.normalize SL cell847 = normal834 := by
  calc
    AdaptiveCoverage.normalize SL cell847 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell847)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell847)).symm
    _ = normal834 := by rfl

theorem numeric410 : ForcedCoverage2.dispatch (fun _ => payload410) normal834 46 = true := by
  decide +kernel

theorem coveredLeaf410 : CovBy 9 PR (Pg cN 9 BS TS) cell847 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf410]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload410) normal834 46 numeric410
theorem normalizedLeaf411 : AdaptiveCoverage.normalize SL cell848 = normal835 := by
  calc
    AdaptiveCoverage.normalize SL cell848 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell848)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell848)).symm
    _ = normal835 := by rfl

theorem numeric411 : ForcedCoverage2.dispatch (fun _ => payload411) normal835 46 = true := by
  decide +kernel

theorem coveredLeaf411 : CovBy 9 PR (Pg cN 9 BS TS) cell848 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf411]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload411) normal835 46 numeric411
theorem normalizedLeaf412 : AdaptiveCoverage.normalize SL cell842 = normal836 := by
  calc
    AdaptiveCoverage.normalize SL cell842 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell842)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell842)).symm
    _ = normal836 := by rfl

theorem numeric412 : ForcedCoverage2.dispatch (fun _ => payload412) normal836 46 = true := by
  decide +kernel

theorem coveredLeaf412 : CovBy 9 PR (Pg cN 9 BS TS) cell842 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf412]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload412) normal836 46 numeric412
theorem normalizedLeaf413 : AdaptiveCoverage.normalize SL cell840 = normal837 := by
  calc
    AdaptiveCoverage.normalize SL cell840 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell840)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell840)).symm
    _ = normal837 := by rfl

theorem numeric413 : ForcedCoverage2.dispatch (fun _ => payload413) normal837 46 = true := by
  decide +kernel

theorem coveredLeaf413 : CovBy 9 PR (Pg cN 9 BS TS) cell840 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf413]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload413) normal837 46 numeric413
theorem normalizedLeaf414 : AdaptiveCoverage.normalize SL cell838 = normal838 := by
  calc
    AdaptiveCoverage.normalize SL cell838 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell838)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell838)).symm
    _ = normal838 := by rfl

theorem numeric414 : ForcedCoverage2.dispatch (fun _ => payload414) normal838 46 = true := by
  decide +kernel

theorem coveredLeaf414 : CovBy 9 PR (Pg cN 9 BS TS) cell838 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf414]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload414) normal838 46 numeric414
theorem normalizedLeaf415 : AdaptiveCoverage.normalize SL cell849 = normal840 := by
  calc
    AdaptiveCoverage.normalize SL cell849 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell849)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell849)).symm
    _ = normal840 := by rfl

theorem numeric415 : ForcedCoverage2.dispatch (fun _ => payload415) normal840 46 = true := by
  decide +kernel

theorem coveredLeaf415 : CovBy 9 PR (Pg cN 9 BS TS) cell849 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf415]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload415) normal840 46 numeric415

set_option pp.fullNames true
#print axioms normalizedLeaf384
#print axioms numeric384
#print axioms coveredLeaf384
#print axioms normalizedLeaf385
#print axioms numeric385
#print axioms coveredLeaf385
#print axioms normalizedLeaf386
#print axioms numeric386
#print axioms coveredLeaf386
#print axioms normalizedLeaf387
#print axioms numeric387
#print axioms coveredLeaf387
#print axioms normalizedLeaf388
#print axioms numeric388
#print axioms coveredLeaf388
#print axioms normalizedLeaf389
#print axioms numeric389
#print axioms coveredLeaf389
#print axioms normalizedLeaf390
#print axioms numeric390
#print axioms coveredLeaf390
#print axioms normalizedLeaf391
#print axioms numeric391
#print axioms coveredLeaf391
#print axioms normalizedLeaf392
#print axioms numeric392
#print axioms coveredLeaf392
#print axioms normalizedLeaf393
#print axioms numeric393
#print axioms coveredLeaf393
#print axioms normalizedLeaf394
#print axioms numeric394
#print axioms coveredLeaf394
#print axioms normalizedLeaf395
#print axioms numeric395
#print axioms coveredLeaf395
#print axioms normalizedLeaf396
#print axioms numeric396
#print axioms coveredLeaf396
#print axioms normalizedLeaf397
#print axioms numeric397
#print axioms coveredLeaf397
#print axioms normalizedLeaf398
#print axioms numeric398
#print axioms coveredLeaf398
#print axioms normalizedLeaf399
#print axioms numeric399
#print axioms coveredLeaf399
#print axioms normalizedLeaf400
#print axioms numeric400
#print axioms coveredLeaf400
#print axioms normalizedLeaf401
#print axioms numeric401
#print axioms coveredLeaf401
#print axioms normalizedLeaf402
#print axioms numeric402
#print axioms coveredLeaf402
#print axioms normalizedLeaf403
#print axioms numeric403
#print axioms coveredLeaf403
#print axioms normalizedLeaf404
#print axioms numeric404
#print axioms coveredLeaf404
#print axioms normalizedLeaf405
#print axioms numeric405
#print axioms coveredLeaf405
#print axioms normalizedLeaf406
#print axioms numeric406
#print axioms coveredLeaf406
#print axioms normalizedLeaf407
#print axioms numeric407
#print axioms coveredLeaf407
#print axioms normalizedLeaf408
#print axioms numeric408
#print axioms coveredLeaf408
#print axioms normalizedLeaf409
#print axioms numeric409
#print axioms coveredLeaf409
#print axioms normalizedLeaf410
#print axioms numeric410
#print axioms coveredLeaf410
#print axioms normalizedLeaf411
#print axioms numeric411
#print axioms coveredLeaf411
#print axioms normalizedLeaf412
#print axioms numeric412
#print axioms coveredLeaf412
#print axioms normalizedLeaf413
#print axioms numeric413
#print axioms coveredLeaf413
#print axioms normalizedLeaf414
#print axioms numeric414
#print axioms coveredLeaf414
#print axioms normalizedLeaf415
#print axioms numeric415
#print axioms coveredLeaf415
end StructuralGoal20261016.W10Aux478
end
