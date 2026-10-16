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
theorem normalizedLeaf000 : AdaptiveCoverage.normalize SL cell013 = normal007 := by
  calc
    AdaptiveCoverage.normalize SL cell013 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell013)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell013)).symm
    _ = normal007 := by rfl

theorem numeric000 : ForcedCoverage2.dispatch (fun _ => payload000) normal007 46 = true := by
  decide +kernel

theorem coveredLeaf000 : CovBy 9 PR (Pg cN 9 BS TS) cell013 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf000]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload000) normal007 46 numeric000
theorem normalizedLeaf001 : AdaptiveCoverage.normalize SL cell014 = normal008 := by
  calc
    AdaptiveCoverage.normalize SL cell014 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell014)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell014)).symm
    _ = normal008 := by rfl

theorem numeric001 : ForcedCoverage2.dispatch (fun _ => payload001) normal008 46 = true := by
  decide +kernel

theorem coveredLeaf001 : CovBy 9 PR (Pg cN 9 BS TS) cell014 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf001]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload001) normal008 46 numeric001
theorem normalizedLeaf002 : AdaptiveCoverage.normalize SL cell017 = normal011 := by
  calc
    AdaptiveCoverage.normalize SL cell017 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell017)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell017)).symm
    _ = normal011 := by rfl

theorem numeric002 : ForcedCoverage2.dispatch (fun _ => payload002) normal011 46 = true := by
  decide +kernel

theorem coveredLeaf002 : CovBy 9 PR (Pg cN 9 BS TS) cell017 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf002]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload002) normal011 46 numeric002
theorem normalizedLeaf003 : AdaptiveCoverage.normalize SL cell019 = normal013 := by
  calc
    AdaptiveCoverage.normalize SL cell019 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell019)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell019)).symm
    _ = normal013 := by rfl

theorem numeric003 : ForcedCoverage2.dispatch (fun _ => payload003) normal013 46 = true := by
  decide +kernel

theorem coveredLeaf003 : CovBy 9 PR (Pg cN 9 BS TS) cell019 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf003]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload003) normal013 46 numeric003
theorem normalizedLeaf004 : AdaptiveCoverage.normalize SL cell021 = normal015 := by
  calc
    AdaptiveCoverage.normalize SL cell021 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell021)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell021)).symm
    _ = normal015 := by rfl

theorem numeric004 : ForcedCoverage2.dispatch (fun _ => payload004) normal015 46 = true := by
  decide +kernel

theorem coveredLeaf004 : CovBy 9 PR (Pg cN 9 BS TS) cell021 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf004]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload004) normal015 46 numeric004
theorem normalizedLeaf005 : AdaptiveCoverage.normalize SL cell027 = normal019 := by
  calc
    AdaptiveCoverage.normalize SL cell027 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell027)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell027)).symm
    _ = normal019 := by rfl

theorem numeric005 : ForcedCoverage2.dispatch (fun _ => payload005) normal019 46 = true := by
  decide +kernel

theorem coveredLeaf005 : CovBy 9 PR (Pg cN 9 BS TS) cell027 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf005]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload005) normal019 46 numeric005
theorem normalizedLeaf006 : AdaptiveCoverage.normalize SL cell035 = normal024 := by
  calc
    AdaptiveCoverage.normalize SL cell035 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell035)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell035)).symm
    _ = normal024 := by rfl

theorem numeric006 : ForcedCoverage2.dispatch (fun _ => payload006) normal024 46 = true := by
  decide +kernel

theorem coveredLeaf006 : CovBy 9 PR (Pg cN 9 BS TS) cell035 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf006]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload006) normal024 46 numeric006
theorem normalizedLeaf007 : AdaptiveCoverage.normalize SL cell037 = normal026 := by
  calc
    AdaptiveCoverage.normalize SL cell037 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell037)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell037)).symm
    _ = normal026 := by rfl

theorem numeric007 : ForcedCoverage2.dispatch (fun _ => payload007) normal026 46 = true := by
  decide +kernel

theorem coveredLeaf007 : CovBy 9 PR (Pg cN 9 BS TS) cell037 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf007]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload007) normal026 46 numeric007
theorem normalizedLeaf008 : AdaptiveCoverage.normalize SL cell038 = normal027 := by
  calc
    AdaptiveCoverage.normalize SL cell038 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell038)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell038)).symm
    _ = normal027 := by rfl

theorem numeric008 : ForcedCoverage2.dispatch (fun _ => payload008) normal027 46 = true := by
  decide +kernel

theorem coveredLeaf008 : CovBy 9 PR (Pg cN 9 BS TS) cell038 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf008]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload008) normal027 46 numeric008
theorem normalizedLeaf009 : AdaptiveCoverage.normalize SL cell034 = normal028 := by
  calc
    AdaptiveCoverage.normalize SL cell034 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell034)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell034)).symm
    _ = normal028 := by rfl

theorem numeric009 : ForcedCoverage2.dispatch (fun _ => payload009) normal028 46 = true := by
  decide +kernel

theorem coveredLeaf009 : CovBy 9 PR (Pg cN 9 BS TS) cell034 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf009]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload009) normal028 46 numeric009
theorem normalizedLeaf010 : AdaptiveCoverage.normalize SL cell032 = normal029 := by
  calc
    AdaptiveCoverage.normalize SL cell032 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell032)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell032)).symm
    _ = normal029 := by rfl

theorem numeric010 : ForcedCoverage2.dispatch (fun _ => payload010) normal029 46 = true := by
  decide +kernel

theorem coveredLeaf010 : CovBy 9 PR (Pg cN 9 BS TS) cell032 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf010]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload010) normal029 46 numeric010
theorem normalizedLeaf011 : AdaptiveCoverage.normalize SL cell030 = normal030 := by
  calc
    AdaptiveCoverage.normalize SL cell030 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell030)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell030)).symm
    _ = normal030 := by rfl

theorem numeric011 : ForcedCoverage2.dispatch (fun _ => payload011) normal030 46 = true := by
  decide +kernel

theorem coveredLeaf011 : CovBy 9 PR (Pg cN 9 BS TS) cell030 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf011]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload011) normal030 46 numeric011
theorem normalizedLeaf012 : AdaptiveCoverage.normalize SL cell026 = normal031 := by
  calc
    AdaptiveCoverage.normalize SL cell026 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell026)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell026)).symm
    _ = normal031 := by rfl

theorem numeric012 : ForcedCoverage2.dispatch (fun _ => payload012) normal031 46 = true := by
  decide +kernel

theorem coveredLeaf012 : CovBy 9 PR (Pg cN 9 BS TS) cell026 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf012]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload012) normal031 46 numeric012
theorem normalizedLeaf013 : AdaptiveCoverage.normalize SL cell024 = normal032 := by
  calc
    AdaptiveCoverage.normalize SL cell024 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell024)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell024)).symm
    _ = normal032 := by rfl

theorem numeric013 : ForcedCoverage2.dispatch (fun _ => payload013) normal032 46 = true := by
  decide +kernel

theorem coveredLeaf013 : CovBy 9 PR (Pg cN 9 BS TS) cell024 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf013]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload013) normal032 46 numeric013
theorem normalizedLeaf014 : AdaptiveCoverage.normalize SL cell039 = normal034 := by
  calc
    AdaptiveCoverage.normalize SL cell039 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell039)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell039)).symm
    _ = normal034 := by rfl

theorem numeric014 : ForcedCoverage2.dispatch (fun _ => payload014) normal034 46 = true := by
  decide +kernel

theorem coveredLeaf014 : CovBy 9 PR (Pg cN 9 BS TS) cell039 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf014]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload014) normal034 46 numeric014
theorem normalizedLeaf015 : AdaptiveCoverage.normalize SL cell041 = normal036 := by
  calc
    AdaptiveCoverage.normalize SL cell041 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell041)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell041)).symm
    _ = normal036 := by rfl

theorem numeric015 : ForcedCoverage2.dispatch (fun _ => payload015) normal036 46 = true := by
  decide +kernel

theorem coveredLeaf015 : CovBy 9 PR (Pg cN 9 BS TS) cell041 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf015]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload015) normal036 46 numeric015
theorem normalizedLeaf016 : AdaptiveCoverage.normalize SL cell043 = normal038 := by
  calc
    AdaptiveCoverage.normalize SL cell043 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell043)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell043)).symm
    _ = normal038 := by rfl

theorem numeric016 : ForcedCoverage2.dispatch (fun _ => payload016) normal038 46 = true := by
  decide +kernel

theorem coveredLeaf016 : CovBy 9 PR (Pg cN 9 BS TS) cell043 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf016]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload016) normal038 46 numeric016
theorem normalizedLeaf017 : AdaptiveCoverage.normalize SL cell049 = normal042 := by
  calc
    AdaptiveCoverage.normalize SL cell049 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell049)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell049)).symm
    _ = normal042 := by rfl

theorem numeric017 : ForcedCoverage2.dispatch (fun _ => payload017) normal042 46 = true := by
  decide +kernel

theorem coveredLeaf017 : CovBy 9 PR (Pg cN 9 BS TS) cell049 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf017]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload017) normal042 46 numeric017
theorem normalizedLeaf018 : AdaptiveCoverage.normalize SL cell051 = normal044 := by
  calc
    AdaptiveCoverage.normalize SL cell051 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell051)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell051)).symm
    _ = normal044 := by rfl

theorem numeric018 : ForcedCoverage2.dispatch (fun _ => payload018) normal044 46 = true := by
  decide +kernel

theorem coveredLeaf018 : CovBy 9 PR (Pg cN 9 BS TS) cell051 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf018]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload018) normal044 46 numeric018
theorem normalizedLeaf019 : AdaptiveCoverage.normalize SL cell059 = normal049 := by
  calc
    AdaptiveCoverage.normalize SL cell059 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell059)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell059)).symm
    _ = normal049 := by rfl

theorem numeric019 : ForcedCoverage2.dispatch (fun _ => payload019) normal049 46 = true := by
  decide +kernel

theorem coveredLeaf019 : CovBy 9 PR (Pg cN 9 BS TS) cell059 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf019]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload019) normal049 46 numeric019
theorem normalizedLeaf020 : AdaptiveCoverage.normalize SL cell061 = normal051 := by
  calc
    AdaptiveCoverage.normalize SL cell061 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell061)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell061)).symm
    _ = normal051 := by rfl

theorem numeric020 : ForcedCoverage2.dispatch (fun _ => payload020) normal051 46 = true := by
  decide +kernel

theorem coveredLeaf020 : CovBy 9 PR (Pg cN 9 BS TS) cell061 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf020]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload020) normal051 46 numeric020
theorem normalizedLeaf021 : AdaptiveCoverage.normalize SL cell065 = normal054 := by
  calc
    AdaptiveCoverage.normalize SL cell065 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell065)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell065)).symm
    _ = normal054 := by rfl

theorem numeric021 : ForcedCoverage2.dispatch (fun _ => payload021) normal054 46 = true := by
  decide +kernel

theorem coveredLeaf021 : CovBy 9 PR (Pg cN 9 BS TS) cell065 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf021]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload021) normal054 46 numeric021
theorem normalizedLeaf022 : AdaptiveCoverage.normalize SL cell066 = normal055 := by
  calc
    AdaptiveCoverage.normalize SL cell066 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell066)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell066)).symm
    _ = normal055 := by rfl

theorem numeric022 : ForcedCoverage2.dispatch (fun _ => payload022) normal055 46 = true := by
  decide +kernel

theorem coveredLeaf022 : CovBy 9 PR (Pg cN 9 BS TS) cell066 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf022]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload022) normal055 46 numeric022
theorem normalizedLeaf023 : AdaptiveCoverage.normalize SL cell064 = normal056 := by
  calc
    AdaptiveCoverage.normalize SL cell064 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell064)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell064)).symm
    _ = normal056 := by rfl

theorem numeric023 : ForcedCoverage2.dispatch (fun _ => payload023) normal056 46 = true := by
  decide +kernel

theorem coveredLeaf023 : CovBy 9 PR (Pg cN 9 BS TS) cell064 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf023]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload023) normal056 46 numeric023
theorem normalizedLeaf024 : AdaptiveCoverage.normalize SL cell058 = normal057 := by
  calc
    AdaptiveCoverage.normalize SL cell058 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell058)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell058)).symm
    _ = normal057 := by rfl

theorem numeric024 : ForcedCoverage2.dispatch (fun _ => payload024) normal057 46 = true := by
  decide +kernel

theorem coveredLeaf024 : CovBy 9 PR (Pg cN 9 BS TS) cell058 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf024]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload024) normal057 46 numeric024
theorem normalizedLeaf025 : AdaptiveCoverage.normalize SL cell056 = normal058 := by
  calc
    AdaptiveCoverage.normalize SL cell056 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell056)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell056)).symm
    _ = normal058 := by rfl

theorem numeric025 : ForcedCoverage2.dispatch (fun _ => payload025) normal058 46 = true := by
  decide +kernel

theorem coveredLeaf025 : CovBy 9 PR (Pg cN 9 BS TS) cell056 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf025]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload025) normal058 46 numeric025
theorem normalizedLeaf026 : AdaptiveCoverage.normalize SL cell054 = normal059 := by
  calc
    AdaptiveCoverage.normalize SL cell054 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell054)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell054)).symm
    _ = normal059 := by rfl

theorem numeric026 : ForcedCoverage2.dispatch (fun _ => payload026) normal059 46 = true := by
  decide +kernel

theorem coveredLeaf026 : CovBy 9 PR (Pg cN 9 BS TS) cell054 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf026]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload026) normal059 46 numeric026
theorem normalizedLeaf027 : AdaptiveCoverage.normalize SL cell048 = normal060 := by
  calc
    AdaptiveCoverage.normalize SL cell048 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell048)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell048)).symm
    _ = normal060 := by rfl

theorem numeric027 : ForcedCoverage2.dispatch (fun _ => payload027) normal060 46 = true := by
  decide +kernel

theorem coveredLeaf027 : CovBy 9 PR (Pg cN 9 BS TS) cell048 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf027]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload027) normal060 46 numeric027
theorem normalizedLeaf028 : AdaptiveCoverage.normalize SL cell046 = normal061 := by
  calc
    AdaptiveCoverage.normalize SL cell046 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell046)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell046)).symm
    _ = normal061 := by rfl

theorem numeric028 : ForcedCoverage2.dispatch (fun _ => payload028) normal061 46 = true := by
  decide +kernel

theorem coveredLeaf028 : CovBy 9 PR (Pg cN 9 BS TS) cell046 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf028]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload028) normal061 46 numeric028
theorem normalizedLeaf029 : AdaptiveCoverage.normalize SL cell067 = normal063 := by
  calc
    AdaptiveCoverage.normalize SL cell067 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell067)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell067)).symm
    _ = normal063 := by rfl

theorem numeric029 : ForcedCoverage2.dispatch (fun _ => payload029) normal063 46 = true := by
  decide +kernel

theorem coveredLeaf029 : CovBy 9 PR (Pg cN 9 BS TS) cell067 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf029]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload029) normal063 46 numeric029
theorem normalizedLeaf030 : AdaptiveCoverage.normalize SL cell077 = normal069 := by
  calc
    AdaptiveCoverage.normalize SL cell077 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell077)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell077)).symm
    _ = normal069 := by rfl

theorem numeric030 : ForcedCoverage2.dispatch (fun _ => payload030) normal069 46 = true := by
  decide +kernel

theorem coveredLeaf030 : CovBy 9 PR (Pg cN 9 BS TS) cell077 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf030]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload030) normal069 46 numeric030
theorem normalizedLeaf031 : AdaptiveCoverage.normalize SL cell079 = normal071 := by
  calc
    AdaptiveCoverage.normalize SL cell079 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell079)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell079)).symm
    _ = normal071 := by rfl

theorem numeric031 : ForcedCoverage2.dispatch (fun _ => payload031) normal071 46 = true := by
  decide +kernel

theorem coveredLeaf031 : CovBy 9 PR (Pg cN 9 BS TS) cell079 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf031]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload031) normal071 46 numeric031

set_option pp.fullNames true
#print axioms normalizedLeaf000
#print axioms numeric000
#print axioms coveredLeaf000
#print axioms normalizedLeaf001
#print axioms numeric001
#print axioms coveredLeaf001
#print axioms normalizedLeaf002
#print axioms numeric002
#print axioms coveredLeaf002
#print axioms normalizedLeaf003
#print axioms numeric003
#print axioms coveredLeaf003
#print axioms normalizedLeaf004
#print axioms numeric004
#print axioms coveredLeaf004
#print axioms normalizedLeaf005
#print axioms numeric005
#print axioms coveredLeaf005
#print axioms normalizedLeaf006
#print axioms numeric006
#print axioms coveredLeaf006
#print axioms normalizedLeaf007
#print axioms numeric007
#print axioms coveredLeaf007
#print axioms normalizedLeaf008
#print axioms numeric008
#print axioms coveredLeaf008
#print axioms normalizedLeaf009
#print axioms numeric009
#print axioms coveredLeaf009
#print axioms normalizedLeaf010
#print axioms numeric010
#print axioms coveredLeaf010
#print axioms normalizedLeaf011
#print axioms numeric011
#print axioms coveredLeaf011
#print axioms normalizedLeaf012
#print axioms numeric012
#print axioms coveredLeaf012
#print axioms normalizedLeaf013
#print axioms numeric013
#print axioms coveredLeaf013
#print axioms normalizedLeaf014
#print axioms numeric014
#print axioms coveredLeaf014
#print axioms normalizedLeaf015
#print axioms numeric015
#print axioms coveredLeaf015
#print axioms normalizedLeaf016
#print axioms numeric016
#print axioms coveredLeaf016
#print axioms normalizedLeaf017
#print axioms numeric017
#print axioms coveredLeaf017
#print axioms normalizedLeaf018
#print axioms numeric018
#print axioms coveredLeaf018
#print axioms normalizedLeaf019
#print axioms numeric019
#print axioms coveredLeaf019
#print axioms normalizedLeaf020
#print axioms numeric020
#print axioms coveredLeaf020
#print axioms normalizedLeaf021
#print axioms numeric021
#print axioms coveredLeaf021
#print axioms normalizedLeaf022
#print axioms numeric022
#print axioms coveredLeaf022
#print axioms normalizedLeaf023
#print axioms numeric023
#print axioms coveredLeaf023
#print axioms normalizedLeaf024
#print axioms numeric024
#print axioms coveredLeaf024
#print axioms normalizedLeaf025
#print axioms numeric025
#print axioms coveredLeaf025
#print axioms normalizedLeaf026
#print axioms numeric026
#print axioms coveredLeaf026
#print axioms normalizedLeaf027
#print axioms numeric027
#print axioms coveredLeaf027
#print axioms normalizedLeaf028
#print axioms numeric028
#print axioms coveredLeaf028
#print axioms normalizedLeaf029
#print axioms numeric029
#print axioms coveredLeaf029
#print axioms normalizedLeaf030
#print axioms numeric030
#print axioms coveredLeaf030
#print axioms normalizedLeaf031
#print axioms numeric031
#print axioms coveredLeaf031
end StructuralGoal20261016.W10Aux478
end
