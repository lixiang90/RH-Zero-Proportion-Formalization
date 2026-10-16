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
theorem normalizedLeaf448 : AdaptiveCoverage.normalize SL cell909 = normal903 := by
  calc
    AdaptiveCoverage.normalize SL cell909 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell909)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell909)).symm
    _ = normal903 := by rfl

theorem numeric448 : ForcedCoverage2.dispatch (fun _ => payload448) normal903 46 = true := by
  decide +kernel

theorem coveredLeaf448 : CovBy 9 PR (Pg cN 9 BS TS) cell909 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf448]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload448) normal903 46 numeric448
theorem normalizedLeaf449 : AdaptiveCoverage.normalize SL cell911 = normal905 := by
  calc
    AdaptiveCoverage.normalize SL cell911 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell911)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell911)).symm
    _ = normal905 := by rfl

theorem numeric449 : ForcedCoverage2.dispatch (fun _ => payload449) normal905 46 = true := by
  decide +kernel

theorem coveredLeaf449 : CovBy 9 PR (Pg cN 9 BS TS) cell911 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf449]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload449) normal905 46 numeric449
theorem normalizedLeaf450 : AdaptiveCoverage.normalize SL cell912 = normal906 := by
  calc
    AdaptiveCoverage.normalize SL cell912 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell912)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell912)).symm
    _ = normal906 := by rfl

theorem numeric450 : ForcedCoverage2.dispatch (fun _ => payload450) normal906 46 = true := by
  decide +kernel

theorem coveredLeaf450 : CovBy 9 PR (Pg cN 9 BS TS) cell912 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf450]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload450) normal906 46 numeric450
theorem normalizedLeaf451 : AdaptiveCoverage.normalize SL cell931 = normal917 := by
  calc
    AdaptiveCoverage.normalize SL cell931 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell931)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell931)).symm
    _ = normal917 := by rfl

theorem numeric451 : ForcedCoverage2.dispatch (fun _ => payload451) normal917 46 = true := by
  decide +kernel

theorem coveredLeaf451 : CovBy 9 PR (Pg cN 9 BS TS) cell931 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf451]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload451) normal917 46 numeric451
theorem normalizedLeaf452 : AdaptiveCoverage.normalize SL cell932 = normal918 := by
  calc
    AdaptiveCoverage.normalize SL cell932 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell932)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell932)).symm
    _ = normal918 := by rfl

theorem numeric452 : ForcedCoverage2.dispatch (fun _ => payload452) normal918 46 = true := by
  decide +kernel

theorem coveredLeaf452 : CovBy 9 PR (Pg cN 9 BS TS) cell932 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf452]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload452) normal918 46 numeric452
theorem normalizedLeaf453 : AdaptiveCoverage.normalize SL cell933 = normal920 := by
  calc
    AdaptiveCoverage.normalize SL cell933 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell933)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell933)).symm
    _ = normal920 := by rfl

theorem numeric453 : ForcedCoverage2.dispatch (fun _ => payload453) normal920 46 = true := by
  decide +kernel

theorem coveredLeaf453 : CovBy 9 PR (Pg cN 9 BS TS) cell933 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf453]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload453) normal920 46 numeric453
theorem normalizedLeaf454 : AdaptiveCoverage.normalize SL cell934 = normal921 := by
  calc
    AdaptiveCoverage.normalize SL cell934 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell934)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell934)).symm
    _ = normal921 := by rfl

theorem numeric454 : ForcedCoverage2.dispatch (fun _ => payload454) normal921 46 = true := by
  decide +kernel

theorem coveredLeaf454 : CovBy 9 PR (Pg cN 9 BS TS) cell934 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf454]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload454) normal921 46 numeric454
theorem normalizedLeaf455 : AdaptiveCoverage.normalize SL cell928 = normal922 := by
  calc
    AdaptiveCoverage.normalize SL cell928 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell928)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell928)).symm
    _ = normal922 := by rfl

theorem numeric455 : ForcedCoverage2.dispatch (fun _ => payload455) normal922 46 = true := by
  decide +kernel

theorem coveredLeaf455 : CovBy 9 PR (Pg cN 9 BS TS) cell928 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf455]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload455) normal922 46 numeric455
theorem normalizedLeaf456 : AdaptiveCoverage.normalize SL cell926 = normal923 := by
  calc
    AdaptiveCoverage.normalize SL cell926 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell926)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell926)).symm
    _ = normal923 := by rfl

theorem numeric456 : ForcedCoverage2.dispatch (fun _ => payload456) normal923 46 = true := by
  decide +kernel

theorem coveredLeaf456 : CovBy 9 PR (Pg cN 9 BS TS) cell926 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf456]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload456) normal923 46 numeric456
theorem normalizedLeaf457 : AdaptiveCoverage.normalize SL cell924 = normal924 := by
  calc
    AdaptiveCoverage.normalize SL cell924 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell924)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell924)).symm
    _ = normal924 := by rfl

theorem numeric457 : ForcedCoverage2.dispatch (fun _ => payload457) normal924 46 = true := by
  decide +kernel

theorem coveredLeaf457 : CovBy 9 PR (Pg cN 9 BS TS) cell924 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf457]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload457) normal924 46 numeric457
theorem normalizedLeaf458 : AdaptiveCoverage.normalize SL cell935 = normal926 := by
  calc
    AdaptiveCoverage.normalize SL cell935 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell935)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell935)).symm
    _ = normal926 := by rfl

theorem numeric458 : ForcedCoverage2.dispatch (fun _ => payload458) normal926 46 = true := by
  decide +kernel

theorem coveredLeaf458 : CovBy 9 PR (Pg cN 9 BS TS) cell935 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf458]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload458) normal926 46 numeric458
theorem normalizedLeaf459 : AdaptiveCoverage.normalize SL cell936 = normal927 := by
  calc
    AdaptiveCoverage.normalize SL cell936 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell936)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell936)).symm
    _ = normal927 := by rfl

theorem numeric459 : ForcedCoverage2.dispatch (fun _ => payload459) normal927 46 = true := by
  decide +kernel

theorem coveredLeaf459 : CovBy 9 PR (Pg cN 9 BS TS) cell936 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf459]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload459) normal927 46 numeric459
theorem normalizedLeaf460 : AdaptiveCoverage.normalize SL cell937 = normal929 := by
  calc
    AdaptiveCoverage.normalize SL cell937 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell937)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell937)).symm
    _ = normal929 := by rfl

theorem numeric460 : ForcedCoverage2.dispatch (fun _ => payload460) normal929 46 = true := by
  decide +kernel

theorem coveredLeaf460 : CovBy 9 PR (Pg cN 9 BS TS) cell937 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf460]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload460) normal929 46 numeric460
theorem normalizedLeaf461 : AdaptiveCoverage.normalize SL cell938 = normal930 := by
  calc
    AdaptiveCoverage.normalize SL cell938 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell938)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell938)).symm
    _ = normal930 := by rfl

theorem numeric461 : ForcedCoverage2.dispatch (fun _ => payload461) normal930 46 = true := by
  decide +kernel

theorem coveredLeaf461 : CovBy 9 PR (Pg cN 9 BS TS) cell938 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf461]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload461) normal930 46 numeric461
theorem normalizedLeaf462 : AdaptiveCoverage.normalize SL cell939 = normal932 := by
  calc
    AdaptiveCoverage.normalize SL cell939 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell939)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell939)).symm
    _ = normal932 := by rfl

theorem numeric462 : ForcedCoverage2.dispatch (fun _ => payload462) normal932 46 = true := by
  decide +kernel

theorem coveredLeaf462 : CovBy 9 PR (Pg cN 9 BS TS) cell939 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf462]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload462) normal932 46 numeric462
theorem normalizedLeaf463 : AdaptiveCoverage.normalize SL cell940 = normal933 := by
  calc
    AdaptiveCoverage.normalize SL cell940 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell940)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell940)).symm
    _ = normal933 := by rfl

theorem numeric463 : ForcedCoverage2.dispatch (fun _ => payload463) normal933 46 = true := by
  decide +kernel

theorem coveredLeaf463 : CovBy 9 PR (Pg cN 9 BS TS) cell940 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf463]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload463) normal933 46 numeric463
theorem normalizedLeaf464 : AdaptiveCoverage.normalize SL cell943 = normal936 := by
  calc
    AdaptiveCoverage.normalize SL cell943 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell943)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell943)).symm
    _ = normal936 := by rfl

theorem numeric464 : ForcedCoverage2.dispatch (fun _ => payload464) normal936 46 = true := by
  decide +kernel

theorem coveredLeaf464 : CovBy 9 PR (Pg cN 9 BS TS) cell943 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf464]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload464) normal936 46 numeric464
theorem normalizedLeaf465 : AdaptiveCoverage.normalize SL cell944 = normal937 := by
  calc
    AdaptiveCoverage.normalize SL cell944 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell944)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell944)).symm
    _ = normal937 := by rfl

theorem numeric465 : ForcedCoverage2.dispatch (fun _ => payload465) normal937 46 = true := by
  decide +kernel

theorem coveredLeaf465 : CovBy 9 PR (Pg cN 9 BS TS) cell944 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf465]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload465) normal937 46 numeric465
theorem normalizedLeaf466 : AdaptiveCoverage.normalize SL cell945 = normal939 := by
  calc
    AdaptiveCoverage.normalize SL cell945 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell945)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell945)).symm
    _ = normal939 := by rfl

theorem numeric466 : ForcedCoverage2.dispatch (fun _ => payload466) normal939 46 = true := by
  decide +kernel

theorem coveredLeaf466 : CovBy 9 PR (Pg cN 9 BS TS) cell945 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf466]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload466) normal939 46 numeric466
theorem normalizedLeaf467 : AdaptiveCoverage.normalize SL cell946 = normal940 := by
  calc
    AdaptiveCoverage.normalize SL cell946 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell946)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell946)).symm
    _ = normal940 := by rfl

theorem numeric467 : ForcedCoverage2.dispatch (fun _ => payload467) normal940 46 = true := by
  decide +kernel

theorem coveredLeaf467 : CovBy 9 PR (Pg cN 9 BS TS) cell946 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf467]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload467) normal940 46 numeric467
theorem normalizedLeaf468 : AdaptiveCoverage.normalize SL cell949 = normal943 := by
  calc
    AdaptiveCoverage.normalize SL cell949 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell949)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell949)).symm
    _ = normal943 := by rfl

theorem numeric468 : ForcedCoverage2.dispatch (fun _ => payload468) normal943 46 = true := by
  decide +kernel

theorem coveredLeaf468 : CovBy 9 PR (Pg cN 9 BS TS) cell949 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf468]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload468) normal943 46 numeric468
theorem normalizedLeaf469 : AdaptiveCoverage.normalize SL cell950 = normal944 := by
  calc
    AdaptiveCoverage.normalize SL cell950 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell950)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell950)).symm
    _ = normal944 := by rfl

theorem numeric469 : ForcedCoverage2.dispatch (fun _ => payload469) normal944 46 = true := by
  decide +kernel

theorem coveredLeaf469 : CovBy 9 PR (Pg cN 9 BS TS) cell950 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf469]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload469) normal944 46 numeric469
theorem normalizedLeaf470 : AdaptiveCoverage.normalize SL cell951 = normal946 := by
  calc
    AdaptiveCoverage.normalize SL cell951 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell951)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell951)).symm
    _ = normal946 := by rfl

theorem numeric470 : ForcedCoverage2.dispatch (fun _ => payload470) normal946 46 = true := by
  decide +kernel

theorem coveredLeaf470 : CovBy 9 PR (Pg cN 9 BS TS) cell951 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf470]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload470) normal946 46 numeric470
theorem normalizedLeaf471 : AdaptiveCoverage.normalize SL cell952 = normal947 := by
  calc
    AdaptiveCoverage.normalize SL cell952 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell952)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell952)).symm
    _ = normal947 := by rfl

theorem numeric471 : ForcedCoverage2.dispatch (fun _ => payload471) normal947 46 = true := by
  decide +kernel

theorem coveredLeaf471 : CovBy 9 PR (Pg cN 9 BS TS) cell952 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf471]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload471) normal947 46 numeric471
theorem normalizedLeaf472 : AdaptiveCoverage.normalize SL cell955 = normal950 := by
  calc
    AdaptiveCoverage.normalize SL cell955 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell955)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell955)).symm
    _ = normal950 := by rfl

theorem numeric472 : ForcedCoverage2.dispatch (fun _ => payload472) normal950 46 = true := by
  decide +kernel

theorem coveredLeaf472 : CovBy 9 PR (Pg cN 9 BS TS) cell955 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf472]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload472) normal950 46 numeric472
theorem normalizedLeaf473 : AdaptiveCoverage.normalize SL cell957 = normal952 := by
  calc
    AdaptiveCoverage.normalize SL cell957 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell957)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell957)).symm
    _ = normal952 := by rfl

theorem numeric473 : ForcedCoverage2.dispatch (fun _ => payload473) normal952 46 = true := by
  decide +kernel

theorem coveredLeaf473 : CovBy 9 PR (Pg cN 9 BS TS) cell957 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf473]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload473) normal952 46 numeric473
theorem normalizedLeaf474 : AdaptiveCoverage.normalize SL cell958 = normal953 := by
  calc
    AdaptiveCoverage.normalize SL cell958 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell958)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell958)).symm
    _ = normal953 := by rfl

theorem numeric474 : ForcedCoverage2.dispatch (fun _ => payload474) normal953 46 = true := by
  decide +kernel

theorem coveredLeaf474 : CovBy 9 PR (Pg cN 9 BS TS) cell958 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf474]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload474) normal953 46 numeric474
theorem normalizedLeaf475 : AdaptiveCoverage.normalize SL cell959 = normal955 := by
  calc
    AdaptiveCoverage.normalize SL cell959 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell959)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell959)).symm
    _ = normal955 := by rfl

theorem numeric475 : ForcedCoverage2.dispatch (fun _ => payload475) normal955 46 = true := by
  decide +kernel

theorem coveredLeaf475 : CovBy 9 PR (Pg cN 9 BS TS) cell959 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf475]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload475) normal955 46 numeric475
theorem normalizedLeaf476 : AdaptiveCoverage.normalize SL cell961 = normal957 := by
  calc
    AdaptiveCoverage.normalize SL cell961 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell961)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell961)).symm
    _ = normal957 := by rfl

theorem numeric476 : ForcedCoverage2.dispatch (fun _ => payload476) normal957 46 = true := by
  decide +kernel

theorem coveredLeaf476 : CovBy 9 PR (Pg cN 9 BS TS) cell961 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf476]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload476) normal957 46 numeric476
theorem normalizedLeaf477 : AdaptiveCoverage.normalize SL cell962 = normal958 := by
  calc
    AdaptiveCoverage.normalize SL cell962 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell962)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell962)).symm
    _ = normal958 := by rfl

theorem numeric477 : ForcedCoverage2.dispatch (fun _ => payload477) normal958 46 = true := by
  decide +kernel

theorem coveredLeaf477 : CovBy 9 PR (Pg cN 9 BS TS) cell962 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf477]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload477) normal958 46 numeric477

set_option pp.fullNames true
#print axioms normalizedLeaf448
#print axioms numeric448
#print axioms coveredLeaf448
#print axioms normalizedLeaf449
#print axioms numeric449
#print axioms coveredLeaf449
#print axioms normalizedLeaf450
#print axioms numeric450
#print axioms coveredLeaf450
#print axioms normalizedLeaf451
#print axioms numeric451
#print axioms coveredLeaf451
#print axioms normalizedLeaf452
#print axioms numeric452
#print axioms coveredLeaf452
#print axioms normalizedLeaf453
#print axioms numeric453
#print axioms coveredLeaf453
#print axioms normalizedLeaf454
#print axioms numeric454
#print axioms coveredLeaf454
#print axioms normalizedLeaf455
#print axioms numeric455
#print axioms coveredLeaf455
#print axioms normalizedLeaf456
#print axioms numeric456
#print axioms coveredLeaf456
#print axioms normalizedLeaf457
#print axioms numeric457
#print axioms coveredLeaf457
#print axioms normalizedLeaf458
#print axioms numeric458
#print axioms coveredLeaf458
#print axioms normalizedLeaf459
#print axioms numeric459
#print axioms coveredLeaf459
#print axioms normalizedLeaf460
#print axioms numeric460
#print axioms coveredLeaf460
#print axioms normalizedLeaf461
#print axioms numeric461
#print axioms coveredLeaf461
#print axioms normalizedLeaf462
#print axioms numeric462
#print axioms coveredLeaf462
#print axioms normalizedLeaf463
#print axioms numeric463
#print axioms coveredLeaf463
#print axioms normalizedLeaf464
#print axioms numeric464
#print axioms coveredLeaf464
#print axioms normalizedLeaf465
#print axioms numeric465
#print axioms coveredLeaf465
#print axioms normalizedLeaf466
#print axioms numeric466
#print axioms coveredLeaf466
#print axioms normalizedLeaf467
#print axioms numeric467
#print axioms coveredLeaf467
#print axioms normalizedLeaf468
#print axioms numeric468
#print axioms coveredLeaf468
#print axioms normalizedLeaf469
#print axioms numeric469
#print axioms coveredLeaf469
#print axioms normalizedLeaf470
#print axioms numeric470
#print axioms coveredLeaf470
#print axioms normalizedLeaf471
#print axioms numeric471
#print axioms coveredLeaf471
#print axioms normalizedLeaf472
#print axioms numeric472
#print axioms coveredLeaf472
#print axioms normalizedLeaf473
#print axioms numeric473
#print axioms coveredLeaf473
#print axioms normalizedLeaf474
#print axioms numeric474
#print axioms coveredLeaf474
#print axioms normalizedLeaf475
#print axioms numeric475
#print axioms coveredLeaf475
#print axioms normalizedLeaf476
#print axioms numeric476
#print axioms coveredLeaf476
#print axioms normalizedLeaf477
#print axioms numeric477
#print axioms coveredLeaf477
end StructuralGoal20261016.W10Aux478
end
