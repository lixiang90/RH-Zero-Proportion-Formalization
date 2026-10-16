/- Frozen 127-leaf W10 subtree; complete global coverage is not asserted. -/
import StructuralGoal20261016.W10Aux127Data
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
namespace StructuralGoal20261016.W10Aux127
theorem normalizedLeaf000 : AdaptiveCoverage.normalize SL cell009 = normal005 := by
  calc
    AdaptiveCoverage.normalize SL cell009 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell009)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell009)).symm
    _ = normal005 := by rfl

theorem numeric000 : ForcedCoverage2.dispatch (fun _ => payload000) normal005 46 = true := by
  decide +kernel

theorem coveredLeaf000 : CovBy 9 PR (Pg cN 9 BS TS) cell009 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf000]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload000) normal005 46 numeric000
theorem normalizedLeaf001 : AdaptiveCoverage.normalize SL cell011 = normal007 := by
  calc
    AdaptiveCoverage.normalize SL cell011 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell011)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell011)).symm
    _ = normal007 := by rfl

theorem numeric001 : ForcedCoverage2.dispatch (fun _ => payload001) normal007 46 = true := by
  decide +kernel

theorem coveredLeaf001 : CovBy 9 PR (Pg cN 9 BS TS) cell011 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf001]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload001) normal007 46 numeric001
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
theorem normalizedLeaf003 : AdaptiveCoverage.normalize SL cell021 = normal014 := by
  calc
    AdaptiveCoverage.normalize SL cell021 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell021)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell021)).symm
    _ = normal014 := by rfl

theorem numeric003 : ForcedCoverage2.dispatch (fun _ => payload003) normal014 46 = true := by
  decide +kernel

theorem coveredLeaf003 : CovBy 9 PR (Pg cN 9 BS TS) cell021 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf003]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload003) normal014 46 numeric003
theorem normalizedLeaf004 : AdaptiveCoverage.normalize SL cell023 = normal016 := by
  calc
    AdaptiveCoverage.normalize SL cell023 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell023)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell023)).symm
    _ = normal016 := by rfl

theorem numeric004 : ForcedCoverage2.dispatch (fun _ => payload004) normal016 46 = true := by
  decide +kernel

theorem coveredLeaf004 : CovBy 9 PR (Pg cN 9 BS TS) cell023 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf004]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload004) normal016 46 numeric004
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
theorem normalizedLeaf006 : AdaptiveCoverage.normalize SL cell028 = normal020 := by
  calc
    AdaptiveCoverage.normalize SL cell028 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell028)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell028)).symm
    _ = normal020 := by rfl

theorem numeric006 : ForcedCoverage2.dispatch (fun _ => payload006) normal020 46 = true := by
  decide +kernel

theorem coveredLeaf006 : CovBy 9 PR (Pg cN 9 BS TS) cell028 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf006]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload006) normal020 46 numeric006
theorem normalizedLeaf007 : AdaptiveCoverage.normalize SL cell029 = normal022 := by
  calc
    AdaptiveCoverage.normalize SL cell029 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell029)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell029)).symm
    _ = normal022 := by rfl

theorem numeric007 : ForcedCoverage2.dispatch (fun _ => payload007) normal022 46 = true := by
  decide +kernel

theorem coveredLeaf007 : CovBy 9 PR (Pg cN 9 BS TS) cell029 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf007]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload007) normal022 46 numeric007
theorem normalizedLeaf008 : AdaptiveCoverage.normalize SL cell031 = normal024 := by
  calc
    AdaptiveCoverage.normalize SL cell031 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell031)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell031)).symm
    _ = normal024 := by rfl

theorem numeric008 : ForcedCoverage2.dispatch (fun _ => payload008) normal024 46 = true := by
  decide +kernel

theorem coveredLeaf008 : CovBy 9 PR (Pg cN 9 BS TS) cell031 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf008]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload008) normal024 46 numeric008
theorem normalizedLeaf009 : AdaptiveCoverage.normalize SL cell033 = normal026 := by
  calc
    AdaptiveCoverage.normalize SL cell033 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell033)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell033)).symm
    _ = normal026 := by rfl

theorem numeric009 : ForcedCoverage2.dispatch (fun _ => payload009) normal026 46 = true := by
  decide +kernel

theorem coveredLeaf009 : CovBy 9 PR (Pg cN 9 BS TS) cell033 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf009]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload009) normal026 46 numeric009
theorem normalizedLeaf010 : AdaptiveCoverage.normalize SL cell037 = normal029 := by
  calc
    AdaptiveCoverage.normalize SL cell037 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell037)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell037)).symm
    _ = normal029 := by rfl

theorem numeric010 : ForcedCoverage2.dispatch (fun _ => payload010) normal029 46 = true := by
  decide +kernel

theorem coveredLeaf010 : CovBy 9 PR (Pg cN 9 BS TS) cell037 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf010]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload010) normal029 46 numeric010
theorem normalizedLeaf011 : AdaptiveCoverage.normalize SL cell039 = normal031 := by
  calc
    AdaptiveCoverage.normalize SL cell039 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell039)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell039)).symm
    _ = normal031 := by rfl

theorem numeric011 : ForcedCoverage2.dispatch (fun _ => payload011) normal031 46 = true := by
  decide +kernel

theorem coveredLeaf011 : CovBy 9 PR (Pg cN 9 BS TS) cell039 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf011]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload011) normal031 46 numeric011
theorem normalizedLeaf012 : AdaptiveCoverage.normalize SL cell041 = normal033 := by
  calc
    AdaptiveCoverage.normalize SL cell041 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell041)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell041)).symm
    _ = normal033 := by rfl

theorem numeric012 : ForcedCoverage2.dispatch (fun _ => payload012) normal033 46 = true := by
  decide +kernel

theorem coveredLeaf012 : CovBy 9 PR (Pg cN 9 BS TS) cell041 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf012]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload012) normal033 46 numeric012
theorem normalizedLeaf013 : AdaptiveCoverage.normalize SL cell043 = normal035 := by
  calc
    AdaptiveCoverage.normalize SL cell043 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell043)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell043)).symm
    _ = normal035 := by rfl

theorem numeric013 : ForcedCoverage2.dispatch (fun _ => payload013) normal035 46 = true := by
  decide +kernel

theorem coveredLeaf013 : CovBy 9 PR (Pg cN 9 BS TS) cell043 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf013]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload013) normal035 46 numeric013
theorem normalizedLeaf014 : AdaptiveCoverage.normalize SL cell045 = normal037 := by
  calc
    AdaptiveCoverage.normalize SL cell045 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell045)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell045)).symm
    _ = normal037 := by rfl

theorem numeric014 : ForcedCoverage2.dispatch (fun _ => payload014) normal037 46 = true := by
  decide +kernel

theorem coveredLeaf014 : CovBy 9 PR (Pg cN 9 BS TS) cell045 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf014]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload014) normal037 46 numeric014
theorem normalizedLeaf015 : AdaptiveCoverage.normalize SL cell047 = normal039 := by
  calc
    AdaptiveCoverage.normalize SL cell047 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell047)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell047)).symm
    _ = normal039 := by rfl

theorem numeric015 : ForcedCoverage2.dispatch (fun _ => payload015) normal039 46 = true := by
  decide +kernel

theorem coveredLeaf015 : CovBy 9 PR (Pg cN 9 BS TS) cell047 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf015]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload015) normal039 46 numeric015
theorem normalizedLeaf016 : AdaptiveCoverage.normalize SL cell048 = normal040 := by
  calc
    AdaptiveCoverage.normalize SL cell048 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell048)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell048)).symm
    _ = normal040 := by rfl

theorem numeric016 : ForcedCoverage2.dispatch (fun _ => payload016) normal040 46 = true := by
  decide +kernel

theorem coveredLeaf016 : CovBy 9 PR (Pg cN 9 BS TS) cell048 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf016]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload016) normal040 46 numeric016
theorem normalizedLeaf017 : AdaptiveCoverage.normalize SL cell036 = normal041 := by
  calc
    AdaptiveCoverage.normalize SL cell036 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell036)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell036)).symm
    _ = normal041 := by rfl

theorem numeric017 : ForcedCoverage2.dispatch (fun _ => payload017) normal041 46 = true := by
  decide +kernel

theorem coveredLeaf017 : CovBy 9 PR (Pg cN 9 BS TS) cell036 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf017]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload017) normal041 46 numeric017
theorem normalizedLeaf018 : AdaptiveCoverage.normalize SL cell049 = normal043 := by
  calc
    AdaptiveCoverage.normalize SL cell049 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell049)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell049)).symm
    _ = normal043 := by rfl

theorem numeric018 : ForcedCoverage2.dispatch (fun _ => payload018) normal043 46 = true := by
  decide +kernel

theorem coveredLeaf018 : CovBy 9 PR (Pg cN 9 BS TS) cell049 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf018]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload018) normal043 46 numeric018
theorem normalizedLeaf019 : AdaptiveCoverage.normalize SL cell053 = normal046 := by
  calc
    AdaptiveCoverage.normalize SL cell053 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell053)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell053)).symm
    _ = normal046 := by rfl

theorem numeric019 : ForcedCoverage2.dispatch (fun _ => payload019) normal046 46 = true := by
  decide +kernel

theorem coveredLeaf019 : CovBy 9 PR (Pg cN 9 BS TS) cell053 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf019]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload019) normal046 46 numeric019
theorem normalizedLeaf020 : AdaptiveCoverage.normalize SL cell054 = normal047 := by
  calc
    AdaptiveCoverage.normalize SL cell054 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell054)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell054)).symm
    _ = normal047 := by rfl

theorem numeric020 : ForcedCoverage2.dispatch (fun _ => payload020) normal047 46 = true := by
  decide +kernel

theorem coveredLeaf020 : CovBy 9 PR (Pg cN 9 BS TS) cell054 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf020]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload020) normal047 46 numeric020
theorem normalizedLeaf021 : AdaptiveCoverage.normalize SL cell057 = normal050 := by
  calc
    AdaptiveCoverage.normalize SL cell057 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell057)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell057)).symm
    _ = normal050 := by rfl

theorem numeric021 : ForcedCoverage2.dispatch (fun _ => payload021) normal050 46 = true := by
  decide +kernel

theorem coveredLeaf021 : CovBy 9 PR (Pg cN 9 BS TS) cell057 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf021]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload021) normal050 46 numeric021
theorem normalizedLeaf022 : AdaptiveCoverage.normalize SL cell061 = normal053 := by
  calc
    AdaptiveCoverage.normalize SL cell061 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell061)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell061)).symm
    _ = normal053 := by rfl

theorem numeric022 : ForcedCoverage2.dispatch (fun _ => payload022) normal053 46 = true := by
  decide +kernel

theorem coveredLeaf022 : CovBy 9 PR (Pg cN 9 BS TS) cell061 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf022]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload022) normal053 46 numeric022
theorem normalizedLeaf023 : AdaptiveCoverage.normalize SL cell063 = normal055 := by
  calc
    AdaptiveCoverage.normalize SL cell063 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell063)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell063)).symm
    _ = normal055 := by rfl

theorem numeric023 : ForcedCoverage2.dispatch (fun _ => payload023) normal055 46 = true := by
  decide +kernel

theorem coveredLeaf023 : CovBy 9 PR (Pg cN 9 BS TS) cell063 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf023]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload023) normal055 46 numeric023
theorem normalizedLeaf024 : AdaptiveCoverage.normalize SL cell065 = normal057 := by
  calc
    AdaptiveCoverage.normalize SL cell065 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell065)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell065)).symm
    _ = normal057 := by rfl

theorem numeric024 : ForcedCoverage2.dispatch (fun _ => payload024) normal057 46 = true := by
  decide +kernel

theorem coveredLeaf024 : CovBy 9 PR (Pg cN 9 BS TS) cell065 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf024]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload024) normal057 46 numeric024
theorem normalizedLeaf025 : AdaptiveCoverage.normalize SL cell067 = normal059 := by
  calc
    AdaptiveCoverage.normalize SL cell067 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell067)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell067)).symm
    _ = normal059 := by rfl

theorem numeric025 : ForcedCoverage2.dispatch (fun _ => payload025) normal059 46 = true := by
  decide +kernel

theorem coveredLeaf025 : CovBy 9 PR (Pg cN 9 BS TS) cell067 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf025]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload025) normal059 46 numeric025
theorem normalizedLeaf026 : AdaptiveCoverage.normalize SL cell069 = normal061 := by
  calc
    AdaptiveCoverage.normalize SL cell069 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell069)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell069)).symm
    _ = normal061 := by rfl

theorem numeric026 : ForcedCoverage2.dispatch (fun _ => payload026) normal061 46 = true := by
  decide +kernel

theorem coveredLeaf026 : CovBy 9 PR (Pg cN 9 BS TS) cell069 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf026]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload026) normal061 46 numeric026
theorem normalizedLeaf027 : AdaptiveCoverage.normalize SL cell071 = normal063 := by
  calc
    AdaptiveCoverage.normalize SL cell071 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell071)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell071)).symm
    _ = normal063 := by rfl

theorem numeric027 : ForcedCoverage2.dispatch (fun _ => payload027) normal063 46 = true := by
  decide +kernel

theorem coveredLeaf027 : CovBy 9 PR (Pg cN 9 BS TS) cell071 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf027]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload027) normal063 46 numeric027
theorem normalizedLeaf028 : AdaptiveCoverage.normalize SL cell073 = normal065 := by
  calc
    AdaptiveCoverage.normalize SL cell073 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell073)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell073)).symm
    _ = normal065 := by rfl

theorem numeric028 : ForcedCoverage2.dispatch (fun _ => payload028) normal065 46 = true := by
  decide +kernel

theorem coveredLeaf028 : CovBy 9 PR (Pg cN 9 BS TS) cell073 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf028]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload028) normal065 46 numeric028
theorem normalizedLeaf029 : AdaptiveCoverage.normalize SL cell075 = normal067 := by
  calc
    AdaptiveCoverage.normalize SL cell075 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell075)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell075)).symm
    _ = normal067 := by rfl

theorem numeric029 : ForcedCoverage2.dispatch (fun _ => payload029) normal067 46 = true := by
  decide +kernel

theorem coveredLeaf029 : CovBy 9 PR (Pg cN 9 BS TS) cell075 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf029]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload029) normal067 46 numeric029
theorem normalizedLeaf030 : AdaptiveCoverage.normalize SL cell076 = normal068 := by
  calc
    AdaptiveCoverage.normalize SL cell076 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell076)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell076)).symm
    _ = normal068 := by rfl

theorem numeric030 : ForcedCoverage2.dispatch (fun _ => payload030) normal068 46 = true := by
  decide +kernel

theorem coveredLeaf030 : CovBy 9 PR (Pg cN 9 BS TS) cell076 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf030]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload030) normal068 46 numeric030
theorem normalizedLeaf031 : AdaptiveCoverage.normalize SL cell060 = normal069 := by
  calc
    AdaptiveCoverage.normalize SL cell060 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell060)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell060)).symm
    _ = normal069 := by rfl

theorem numeric031 : ForcedCoverage2.dispatch (fun _ => payload031) normal069 46 = true := by
  decide +kernel

theorem coveredLeaf031 : CovBy 9 PR (Pg cN 9 BS TS) cell060 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf031]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload031) normal069 46 numeric031

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
end StructuralGoal20261016.W10Aux127
end
