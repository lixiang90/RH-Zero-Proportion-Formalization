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
theorem normalizedLeaf416 : AdaptiveCoverage.normalize SL cell850 = normal841 := by
  calc
    AdaptiveCoverage.normalize SL cell850 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell850)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell850)).symm
    _ = normal841 := by rfl

theorem numeric416 : ForcedCoverage2.dispatch (fun _ => payload416) normal841 46 = true := by
  decide +kernel

theorem coveredLeaf416 : CovBy 9 PR (Pg cN 9 BS TS) cell850 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf416]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload416) normal841 46 numeric416
theorem normalizedLeaf417 : AdaptiveCoverage.normalize SL cell851 = normal843 := by
  calc
    AdaptiveCoverage.normalize SL cell851 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell851)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell851)).symm
    _ = normal843 := by rfl

theorem numeric417 : ForcedCoverage2.dispatch (fun _ => payload417) normal843 46 = true := by
  decide +kernel

theorem coveredLeaf417 : CovBy 9 PR (Pg cN 9 BS TS) cell851 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf417]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload417) normal843 46 numeric417
theorem normalizedLeaf418 : AdaptiveCoverage.normalize SL cell853 = normal845 := by
  calc
    AdaptiveCoverage.normalize SL cell853 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell853)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell853)).symm
    _ = normal845 := by rfl

theorem numeric418 : ForcedCoverage2.dispatch (fun _ => payload418) normal845 46 = true := by
  decide +kernel

theorem coveredLeaf418 : CovBy 9 PR (Pg cN 9 BS TS) cell853 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf418]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload418) normal845 46 numeric418
theorem normalizedLeaf419 : AdaptiveCoverage.normalize SL cell854 = normal846 := by
  calc
    AdaptiveCoverage.normalize SL cell854 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell854)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell854)).symm
    _ = normal846 := by rfl

theorem numeric419 : ForcedCoverage2.dispatch (fun _ => payload419) normal846 46 = true := by
  decide +kernel

theorem coveredLeaf419 : CovBy 9 PR (Pg cN 9 BS TS) cell854 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf419]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload419) normal846 46 numeric419
theorem normalizedLeaf420 : AdaptiveCoverage.normalize SL cell869 = normal855 := by
  calc
    AdaptiveCoverage.normalize SL cell869 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell869)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell869)).symm
    _ = normal855 := by rfl

theorem numeric420 : ForcedCoverage2.dispatch (fun _ => payload420) normal855 46 = true := by
  decide +kernel

theorem coveredLeaf420 : CovBy 9 PR (Pg cN 9 BS TS) cell869 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf420]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload420) normal855 46 numeric420
theorem normalizedLeaf421 : AdaptiveCoverage.normalize SL cell870 = normal856 := by
  calc
    AdaptiveCoverage.normalize SL cell870 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell870)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell870)).symm
    _ = normal856 := by rfl

theorem numeric421 : ForcedCoverage2.dispatch (fun _ => payload421) normal856 46 = true := by
  decide +kernel

theorem coveredLeaf421 : CovBy 9 PR (Pg cN 9 BS TS) cell870 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf421]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload421) normal856 46 numeric421
theorem normalizedLeaf422 : AdaptiveCoverage.normalize SL cell871 = normal858 := by
  calc
    AdaptiveCoverage.normalize SL cell871 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell871)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell871)).symm
    _ = normal858 := by rfl

theorem numeric422 : ForcedCoverage2.dispatch (fun _ => payload422) normal858 46 = true := by
  decide +kernel

theorem coveredLeaf422 : CovBy 9 PR (Pg cN 9 BS TS) cell871 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf422]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload422) normal858 46 numeric422
theorem normalizedLeaf423 : AdaptiveCoverage.normalize SL cell872 = normal859 := by
  calc
    AdaptiveCoverage.normalize SL cell872 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell872)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell872)).symm
    _ = normal859 := by rfl

theorem numeric423 : ForcedCoverage2.dispatch (fun _ => payload423) normal859 46 = true := by
  decide +kernel

theorem coveredLeaf423 : CovBy 9 PR (Pg cN 9 BS TS) cell872 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf423]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload423) normal859 46 numeric423
theorem normalizedLeaf424 : AdaptiveCoverage.normalize SL cell866 = normal860 := by
  calc
    AdaptiveCoverage.normalize SL cell866 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell866)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell866)).symm
    _ = normal860 := by rfl

theorem numeric424 : ForcedCoverage2.dispatch (fun _ => payload424) normal860 46 = true := by
  decide +kernel

theorem coveredLeaf424 : CovBy 9 PR (Pg cN 9 BS TS) cell866 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf424]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload424) normal860 46 numeric424
theorem normalizedLeaf425 : AdaptiveCoverage.normalize SL cell864 = normal861 := by
  calc
    AdaptiveCoverage.normalize SL cell864 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell864)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell864)).symm
    _ = normal861 := by rfl

theorem numeric425 : ForcedCoverage2.dispatch (fun _ => payload425) normal861 46 = true := by
  decide +kernel

theorem coveredLeaf425 : CovBy 9 PR (Pg cN 9 BS TS) cell864 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf425]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload425) normal861 46 numeric425
theorem normalizedLeaf426 : AdaptiveCoverage.normalize SL cell862 = normal862 := by
  calc
    AdaptiveCoverage.normalize SL cell862 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell862)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell862)).symm
    _ = normal862 := by rfl

theorem numeric426 : ForcedCoverage2.dispatch (fun _ => payload426) normal862 46 = true := by
  decide +kernel

theorem coveredLeaf426 : CovBy 9 PR (Pg cN 9 BS TS) cell862 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf426]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload426) normal862 46 numeric426
theorem normalizedLeaf427 : AdaptiveCoverage.normalize SL cell860 = normal863 := by
  calc
    AdaptiveCoverage.normalize SL cell860 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell860)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell860)).symm
    _ = normal863 := by rfl

theorem numeric427 : ForcedCoverage2.dispatch (fun _ => payload427) normal863 46 = true := by
  decide +kernel

theorem coveredLeaf427 : CovBy 9 PR (Pg cN 9 BS TS) cell860 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf427]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload427) normal863 46 numeric427
theorem normalizedLeaf428 : AdaptiveCoverage.normalize SL cell873 = normal865 := by
  calc
    AdaptiveCoverage.normalize SL cell873 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell873)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell873)).symm
    _ = normal865 := by rfl

theorem numeric428 : ForcedCoverage2.dispatch (fun _ => payload428) normal865 46 = true := by
  decide +kernel

theorem coveredLeaf428 : CovBy 9 PR (Pg cN 9 BS TS) cell873 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf428]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload428) normal865 46 numeric428
theorem normalizedLeaf429 : AdaptiveCoverage.normalize SL cell874 = normal866 := by
  calc
    AdaptiveCoverage.normalize SL cell874 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell874)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell874)).symm
    _ = normal866 := by rfl

theorem numeric429 : ForcedCoverage2.dispatch (fun _ => payload429) normal866 46 = true := by
  decide +kernel

theorem coveredLeaf429 : CovBy 9 PR (Pg cN 9 BS TS) cell874 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf429]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload429) normal866 46 numeric429
theorem normalizedLeaf430 : AdaptiveCoverage.normalize SL cell875 = normal868 := by
  calc
    AdaptiveCoverage.normalize SL cell875 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell875)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell875)).symm
    _ = normal868 := by rfl

theorem numeric430 : ForcedCoverage2.dispatch (fun _ => payload430) normal868 46 = true := by
  decide +kernel

theorem coveredLeaf430 : CovBy 9 PR (Pg cN 9 BS TS) cell875 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf430]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload430) normal868 46 numeric430
theorem normalizedLeaf431 : AdaptiveCoverage.normalize SL cell877 = normal870 := by
  calc
    AdaptiveCoverage.normalize SL cell877 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell877)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell877)).symm
    _ = normal870 := by rfl

theorem numeric431 : ForcedCoverage2.dispatch (fun _ => payload431) normal870 46 = true := by
  decide +kernel

theorem coveredLeaf431 : CovBy 9 PR (Pg cN 9 BS TS) cell877 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf431]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload431) normal870 46 numeric431
theorem normalizedLeaf432 : AdaptiveCoverage.normalize SL cell878 = normal871 := by
  calc
    AdaptiveCoverage.normalize SL cell878 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell878)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell878)).symm
    _ = normal871 := by rfl

theorem numeric432 : ForcedCoverage2.dispatch (fun _ => payload432) normal871 46 = true := by
  decide +kernel

theorem coveredLeaf432 : CovBy 9 PR (Pg cN 9 BS TS) cell878 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf432]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload432) normal871 46 numeric432
theorem normalizedLeaf433 : AdaptiveCoverage.normalize SL cell895 = normal881 := by
  calc
    AdaptiveCoverage.normalize SL cell895 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell895)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell895)).symm
    _ = normal881 := by rfl

theorem numeric433 : ForcedCoverage2.dispatch (fun _ => payload433) normal881 46 = true := by
  decide +kernel

theorem coveredLeaf433 : CovBy 9 PR (Pg cN 9 BS TS) cell895 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf433]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload433) normal881 46 numeric433
theorem normalizedLeaf434 : AdaptiveCoverage.normalize SL cell896 = normal882 := by
  calc
    AdaptiveCoverage.normalize SL cell896 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell896)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell896)).symm
    _ = normal882 := by rfl

theorem numeric434 : ForcedCoverage2.dispatch (fun _ => payload434) normal882 46 = true := by
  decide +kernel

theorem coveredLeaf434 : CovBy 9 PR (Pg cN 9 BS TS) cell896 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf434]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload434) normal882 46 numeric434
theorem normalizedLeaf435 : AdaptiveCoverage.normalize SL cell897 = normal884 := by
  calc
    AdaptiveCoverage.normalize SL cell897 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell897)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell897)).symm
    _ = normal884 := by rfl

theorem numeric435 : ForcedCoverage2.dispatch (fun _ => payload435) normal884 46 = true := by
  decide +kernel

theorem coveredLeaf435 : CovBy 9 PR (Pg cN 9 BS TS) cell897 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf435]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload435) normal884 46 numeric435
theorem normalizedLeaf436 : AdaptiveCoverage.normalize SL cell898 = normal885 := by
  calc
    AdaptiveCoverage.normalize SL cell898 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell898)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell898)).symm
    _ = normal885 := by rfl

theorem numeric436 : ForcedCoverage2.dispatch (fun _ => payload436) normal885 46 = true := by
  decide +kernel

theorem coveredLeaf436 : CovBy 9 PR (Pg cN 9 BS TS) cell898 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf436]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload436) normal885 46 numeric436
theorem normalizedLeaf437 : AdaptiveCoverage.normalize SL cell892 = normal886 := by
  calc
    AdaptiveCoverage.normalize SL cell892 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell892)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell892)).symm
    _ = normal886 := by rfl

theorem numeric437 : ForcedCoverage2.dispatch (fun _ => payload437) normal886 46 = true := by
  decide +kernel

theorem coveredLeaf437 : CovBy 9 PR (Pg cN 9 BS TS) cell892 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf437]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload437) normal886 46 numeric437
theorem normalizedLeaf438 : AdaptiveCoverage.normalize SL cell890 = normal887 := by
  calc
    AdaptiveCoverage.normalize SL cell890 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell890)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell890)).symm
    _ = normal887 := by rfl

theorem numeric438 : ForcedCoverage2.dispatch (fun _ => payload438) normal887 46 = true := by
  decide +kernel

theorem coveredLeaf438 : CovBy 9 PR (Pg cN 9 BS TS) cell890 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf438]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload438) normal887 46 numeric438
theorem normalizedLeaf439 : AdaptiveCoverage.normalize SL cell888 = normal888 := by
  calc
    AdaptiveCoverage.normalize SL cell888 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell888)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell888)).symm
    _ = normal888 := by rfl

theorem numeric439 : ForcedCoverage2.dispatch (fun _ => payload439) normal888 46 = true := by
  decide +kernel

theorem coveredLeaf439 : CovBy 9 PR (Pg cN 9 BS TS) cell888 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf439]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload439) normal888 46 numeric439
theorem normalizedLeaf440 : AdaptiveCoverage.normalize SL cell899 = normal890 := by
  calc
    AdaptiveCoverage.normalize SL cell899 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell899)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell899)).symm
    _ = normal890 := by rfl

theorem numeric440 : ForcedCoverage2.dispatch (fun _ => payload440) normal890 46 = true := by
  decide +kernel

theorem coveredLeaf440 : CovBy 9 PR (Pg cN 9 BS TS) cell899 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf440]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload440) normal890 46 numeric440
theorem normalizedLeaf441 : AdaptiveCoverage.normalize SL cell900 = normal891 := by
  calc
    AdaptiveCoverage.normalize SL cell900 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell900)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell900)).symm
    _ = normal891 := by rfl

theorem numeric441 : ForcedCoverage2.dispatch (fun _ => payload441) normal891 46 = true := by
  decide +kernel

theorem coveredLeaf441 : CovBy 9 PR (Pg cN 9 BS TS) cell900 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf441]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload441) normal891 46 numeric441
theorem normalizedLeaf442 : AdaptiveCoverage.normalize SL cell901 = normal893 := by
  calc
    AdaptiveCoverage.normalize SL cell901 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell901)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell901)).symm
    _ = normal893 := by rfl

theorem numeric442 : ForcedCoverage2.dispatch (fun _ => payload442) normal893 46 = true := by
  decide +kernel

theorem coveredLeaf442 : CovBy 9 PR (Pg cN 9 BS TS) cell901 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf442]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload442) normal893 46 numeric442
theorem normalizedLeaf443 : AdaptiveCoverage.normalize SL cell902 = normal894 := by
  calc
    AdaptiveCoverage.normalize SL cell902 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell902)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell902)).symm
    _ = normal894 := by rfl

theorem numeric443 : ForcedCoverage2.dispatch (fun _ => payload443) normal894 46 = true := by
  decide +kernel

theorem coveredLeaf443 : CovBy 9 PR (Pg cN 9 BS TS) cell902 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf443]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload443) normal894 46 numeric443
theorem normalizedLeaf444 : AdaptiveCoverage.normalize SL cell905 = normal897 := by
  calc
    AdaptiveCoverage.normalize SL cell905 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell905)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell905)).symm
    _ = normal897 := by rfl

theorem numeric444 : ForcedCoverage2.dispatch (fun _ => payload444) normal897 46 = true := by
  decide +kernel

theorem coveredLeaf444 : CovBy 9 PR (Pg cN 9 BS TS) cell905 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf444]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload444) normal897 46 numeric444
theorem normalizedLeaf445 : AdaptiveCoverage.normalize SL cell906 = normal898 := by
  calc
    AdaptiveCoverage.normalize SL cell906 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell906)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell906)).symm
    _ = normal898 := by rfl

theorem numeric445 : ForcedCoverage2.dispatch (fun _ => payload445) normal898 46 = true := by
  decide +kernel

theorem coveredLeaf445 : CovBy 9 PR (Pg cN 9 BS TS) cell906 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf445]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload445) normal898 46 numeric445
theorem normalizedLeaf446 : AdaptiveCoverage.normalize SL cell907 = normal900 := by
  calc
    AdaptiveCoverage.normalize SL cell907 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell907)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell907)).symm
    _ = normal900 := by rfl

theorem numeric446 : ForcedCoverage2.dispatch (fun _ => payload446) normal900 46 = true := by
  decide +kernel

theorem coveredLeaf446 : CovBy 9 PR (Pg cN 9 BS TS) cell907 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf446]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload446) normal900 46 numeric446
theorem normalizedLeaf447 : AdaptiveCoverage.normalize SL cell908 = normal901 := by
  calc
    AdaptiveCoverage.normalize SL cell908 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell908)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell908)).symm
    _ = normal901 := by rfl

theorem numeric447 : ForcedCoverage2.dispatch (fun _ => payload447) normal901 46 = true := by
  decide +kernel

theorem coveredLeaf447 : CovBy 9 PR (Pg cN 9 BS TS) cell908 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf447]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload447) normal901 46 numeric447

set_option pp.fullNames true
#print axioms normalizedLeaf416
#print axioms numeric416
#print axioms coveredLeaf416
#print axioms normalizedLeaf417
#print axioms numeric417
#print axioms coveredLeaf417
#print axioms normalizedLeaf418
#print axioms numeric418
#print axioms coveredLeaf418
#print axioms normalizedLeaf419
#print axioms numeric419
#print axioms coveredLeaf419
#print axioms normalizedLeaf420
#print axioms numeric420
#print axioms coveredLeaf420
#print axioms normalizedLeaf421
#print axioms numeric421
#print axioms coveredLeaf421
#print axioms normalizedLeaf422
#print axioms numeric422
#print axioms coveredLeaf422
#print axioms normalizedLeaf423
#print axioms numeric423
#print axioms coveredLeaf423
#print axioms normalizedLeaf424
#print axioms numeric424
#print axioms coveredLeaf424
#print axioms normalizedLeaf425
#print axioms numeric425
#print axioms coveredLeaf425
#print axioms normalizedLeaf426
#print axioms numeric426
#print axioms coveredLeaf426
#print axioms normalizedLeaf427
#print axioms numeric427
#print axioms coveredLeaf427
#print axioms normalizedLeaf428
#print axioms numeric428
#print axioms coveredLeaf428
#print axioms normalizedLeaf429
#print axioms numeric429
#print axioms coveredLeaf429
#print axioms normalizedLeaf430
#print axioms numeric430
#print axioms coveredLeaf430
#print axioms normalizedLeaf431
#print axioms numeric431
#print axioms coveredLeaf431
#print axioms normalizedLeaf432
#print axioms numeric432
#print axioms coveredLeaf432
#print axioms normalizedLeaf433
#print axioms numeric433
#print axioms coveredLeaf433
#print axioms normalizedLeaf434
#print axioms numeric434
#print axioms coveredLeaf434
#print axioms normalizedLeaf435
#print axioms numeric435
#print axioms coveredLeaf435
#print axioms normalizedLeaf436
#print axioms numeric436
#print axioms coveredLeaf436
#print axioms normalizedLeaf437
#print axioms numeric437
#print axioms coveredLeaf437
#print axioms normalizedLeaf438
#print axioms numeric438
#print axioms coveredLeaf438
#print axioms normalizedLeaf439
#print axioms numeric439
#print axioms coveredLeaf439
#print axioms normalizedLeaf440
#print axioms numeric440
#print axioms coveredLeaf440
#print axioms normalizedLeaf441
#print axioms numeric441
#print axioms coveredLeaf441
#print axioms normalizedLeaf442
#print axioms numeric442
#print axioms coveredLeaf442
#print axioms normalizedLeaf443
#print axioms numeric443
#print axioms coveredLeaf443
#print axioms normalizedLeaf444
#print axioms numeric444
#print axioms coveredLeaf444
#print axioms normalizedLeaf445
#print axioms numeric445
#print axioms coveredLeaf445
#print axioms normalizedLeaf446
#print axioms numeric446
#print axioms coveredLeaf446
#print axioms normalizedLeaf447
#print axioms numeric447
#print axioms coveredLeaf447
end StructuralGoal20261016.W10Aux478
end
