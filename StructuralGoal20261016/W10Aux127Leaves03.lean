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
theorem normalizedLeaf096 : AdaptiveCoverage.normalize SL cell204 = normal200 := by
  calc
    AdaptiveCoverage.normalize SL cell204 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell204)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell204)).symm
    _ = normal200 := by rfl

theorem numeric096 : ForcedCoverage2.dispatch (fun _ => payload096) normal200 46 = true := by
  decide +kernel

theorem coveredLeaf096 : CovBy 9 PR (Pg cN 9 BS TS) cell204 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf096]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload096) normal200 46 numeric096
theorem normalizedLeaf097 : AdaptiveCoverage.normalize SL cell170 = normal201 := by
  calc
    AdaptiveCoverage.normalize SL cell170 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell170)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell170)).symm
    _ = normal201 := by rfl

theorem numeric097 : ForcedCoverage2.dispatch (fun _ => payload097) normal201 46 = true := by
  decide +kernel

theorem coveredLeaf097 : CovBy 9 PR (Pg cN 9 BS TS) cell170 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf097]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload097) normal201 46 numeric097
theorem normalizedLeaf098 : AdaptiveCoverage.normalize SL cell209 = normal203 := by
  calc
    AdaptiveCoverage.normalize SL cell209 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell209)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell209)).symm
    _ = normal203 := by rfl

theorem numeric098 : ForcedCoverage2.dispatch (fun _ => payload098) normal203 46 = true := by
  decide +kernel

theorem coveredLeaf098 : CovBy 9 PR (Pg cN 9 BS TS) cell209 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf098]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload098) normal203 46 numeric098
theorem normalizedLeaf099 : AdaptiveCoverage.normalize SL cell211 = normal205 := by
  calc
    AdaptiveCoverage.normalize SL cell211 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell211)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell211)).symm
    _ = normal205 := by rfl

theorem numeric099 : ForcedCoverage2.dispatch (fun _ => payload099) normal205 46 = true := by
  decide +kernel

theorem coveredLeaf099 : CovBy 9 PR (Pg cN 9 BS TS) cell211 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf099]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload099) normal205 46 numeric099
theorem normalizedLeaf100 : AdaptiveCoverage.normalize SL cell217 = normal209 := by
  calc
    AdaptiveCoverage.normalize SL cell217 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell217)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell217)).symm
    _ = normal209 := by rfl

theorem numeric100 : ForcedCoverage2.dispatch (fun _ => payload100) normal209 46 = true := by
  decide +kernel

theorem coveredLeaf100 : CovBy 9 PR (Pg cN 9 BS TS) cell217 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf100]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload100) normal209 46 numeric100
theorem normalizedLeaf101 : AdaptiveCoverage.normalize SL cell219 = normal211 := by
  calc
    AdaptiveCoverage.normalize SL cell219 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell219)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell219)).symm
    _ = normal211 := by rfl

theorem numeric101 : ForcedCoverage2.dispatch (fun _ => payload101) normal211 46 = true := by
  decide +kernel

theorem coveredLeaf101 : CovBy 9 PR (Pg cN 9 BS TS) cell219 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf101]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload101) normal211 46 numeric101
theorem normalizedLeaf102 : AdaptiveCoverage.normalize SL cell223 = normal214 := by
  calc
    AdaptiveCoverage.normalize SL cell223 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell223)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell223)).symm
    _ = normal214 := by rfl

theorem numeric102 : ForcedCoverage2.dispatch (fun _ => payload102) normal214 46 = true := by
  decide +kernel

theorem coveredLeaf102 : CovBy 9 PR (Pg cN 9 BS TS) cell223 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf102]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload102) normal214 46 numeric102
theorem normalizedLeaf103 : AdaptiveCoverage.normalize SL cell225 = normal216 := by
  calc
    AdaptiveCoverage.normalize SL cell225 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell225)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell225)).symm
    _ = normal216 := by rfl

theorem numeric103 : ForcedCoverage2.dispatch (fun _ => payload103) normal216 46 = true := by
  decide +kernel

theorem coveredLeaf103 : CovBy 9 PR (Pg cN 9 BS TS) cell225 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf103]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload103) normal216 46 numeric103
theorem normalizedLeaf104 : AdaptiveCoverage.normalize SL cell226 = normal217 := by
  calc
    AdaptiveCoverage.normalize SL cell226 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell226)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell226)).symm
    _ = normal217 := by rfl

theorem numeric104 : ForcedCoverage2.dispatch (fun _ => payload104) normal217 46 = true := by
  decide +kernel

theorem coveredLeaf104 : CovBy 9 PR (Pg cN 9 BS TS) cell226 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf104]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload104) normal217 46 numeric104
theorem normalizedLeaf105 : AdaptiveCoverage.normalize SL cell227 = normal219 := by
  calc
    AdaptiveCoverage.normalize SL cell227 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell227)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell227)).symm
    _ = normal219 := by rfl

theorem numeric105 : ForcedCoverage2.dispatch (fun _ => payload105) normal219 46 = true := by
  decide +kernel

theorem coveredLeaf105 : CovBy 9 PR (Pg cN 9 BS TS) cell227 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf105]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload105) normal219 46 numeric105
theorem normalizedLeaf106 : AdaptiveCoverage.normalize SL cell228 = normal220 := by
  calc
    AdaptiveCoverage.normalize SL cell228 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell228)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell228)).symm
    _ = normal220 := by rfl

theorem numeric106 : ForcedCoverage2.dispatch (fun _ => payload106) normal220 46 = true := by
  decide +kernel

theorem coveredLeaf106 : CovBy 9 PR (Pg cN 9 BS TS) cell228 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf106]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload106) normal220 46 numeric106
theorem normalizedLeaf107 : AdaptiveCoverage.normalize SL cell229 = normal222 := by
  calc
    AdaptiveCoverage.normalize SL cell229 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell229)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell229)).symm
    _ = normal222 := by rfl

theorem numeric107 : ForcedCoverage2.dispatch (fun _ => payload107) normal222 46 = true := by
  decide +kernel

theorem coveredLeaf107 : CovBy 9 PR (Pg cN 9 BS TS) cell229 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf107]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload107) normal222 46 numeric107
theorem normalizedLeaf108 : AdaptiveCoverage.normalize SL cell231 = normal224 := by
  calc
    AdaptiveCoverage.normalize SL cell231 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell231)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell231)).symm
    _ = normal224 := by rfl

theorem numeric108 : ForcedCoverage2.dispatch (fun _ => payload108) normal224 46 = true := by
  decide +kernel

theorem coveredLeaf108 : CovBy 9 PR (Pg cN 9 BS TS) cell231 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf108]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload108) normal224 46 numeric108
theorem normalizedLeaf109 : AdaptiveCoverage.normalize SL cell237 = normal228 := by
  calc
    AdaptiveCoverage.normalize SL cell237 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell237)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell237)).symm
    _ = normal228 := by rfl

theorem numeric109 : ForcedCoverage2.dispatch (fun _ => payload109) normal228 46 = true := by
  decide +kernel

theorem coveredLeaf109 : CovBy 9 PR (Pg cN 9 BS TS) cell237 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf109]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload109) normal228 46 numeric109
theorem normalizedLeaf110 : AdaptiveCoverage.normalize SL cell238 = normal229 := by
  calc
    AdaptiveCoverage.normalize SL cell238 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell238)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell238)).symm
    _ = normal229 := by rfl

theorem numeric110 : ForcedCoverage2.dispatch (fun _ => payload110) normal229 46 = true := by
  decide +kernel

theorem coveredLeaf110 : CovBy 9 PR (Pg cN 9 BS TS) cell238 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf110]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload110) normal229 46 numeric110
theorem normalizedLeaf111 : AdaptiveCoverage.normalize SL cell236 = normal230 := by
  calc
    AdaptiveCoverage.normalize SL cell236 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell236)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell236)).symm
    _ = normal230 := by rfl

theorem numeric111 : ForcedCoverage2.dispatch (fun _ => payload111) normal230 46 = true := by
  decide +kernel

theorem coveredLeaf111 : CovBy 9 PR (Pg cN 9 BS TS) cell236 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf111]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload111) normal230 46 numeric111
theorem normalizedLeaf112 : AdaptiveCoverage.normalize SL cell234 = normal231 := by
  calc
    AdaptiveCoverage.normalize SL cell234 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell234)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell234)).symm
    _ = normal231 := by rfl

theorem numeric112 : ForcedCoverage2.dispatch (fun _ => payload112) normal231 46 = true := by
  decide +kernel

theorem coveredLeaf112 : CovBy 9 PR (Pg cN 9 BS TS) cell234 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf112]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload112) normal231 46 numeric112
theorem normalizedLeaf113 : AdaptiveCoverage.normalize SL cell241 = normal234 := by
  calc
    AdaptiveCoverage.normalize SL cell241 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell241)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell241)).symm
    _ = normal234 := by rfl

theorem numeric113 : ForcedCoverage2.dispatch (fun _ => payload113) normal234 46 = true := by
  decide +kernel

theorem coveredLeaf113 : CovBy 9 PR (Pg cN 9 BS TS) cell241 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf113]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload113) normal234 46 numeric113
theorem normalizedLeaf114 : AdaptiveCoverage.normalize SL cell243 = normal236 := by
  calc
    AdaptiveCoverage.normalize SL cell243 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell243)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell243)).symm
    _ = normal236 := by rfl

theorem numeric114 : ForcedCoverage2.dispatch (fun _ => payload114) normal236 46 = true := by
  decide +kernel

theorem coveredLeaf114 : CovBy 9 PR (Pg cN 9 BS TS) cell243 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf114]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload114) normal236 46 numeric114
theorem normalizedLeaf115 : AdaptiveCoverage.normalize SL cell249 = normal240 := by
  calc
    AdaptiveCoverage.normalize SL cell249 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell249)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell249)).symm
    _ = normal240 := by rfl

theorem numeric115 : ForcedCoverage2.dispatch (fun _ => payload115) normal240 46 = true := by
  decide +kernel

theorem coveredLeaf115 : CovBy 9 PR (Pg cN 9 BS TS) cell249 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf115]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload115) normal240 46 numeric115
theorem normalizedLeaf116 : AdaptiveCoverage.normalize SL cell250 = normal241 := by
  calc
    AdaptiveCoverage.normalize SL cell250 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell250)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell250)).symm
    _ = normal241 := by rfl

theorem numeric116 : ForcedCoverage2.dispatch (fun _ => payload116) normal241 46 = true := by
  decide +kernel

theorem coveredLeaf116 : CovBy 9 PR (Pg cN 9 BS TS) cell250 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf116]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload116) normal241 46 numeric116
theorem normalizedLeaf117 : AdaptiveCoverage.normalize SL cell248 = normal242 := by
  calc
    AdaptiveCoverage.normalize SL cell248 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell248)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell248)).symm
    _ = normal242 := by rfl

theorem numeric117 : ForcedCoverage2.dispatch (fun _ => payload117) normal242 46 = true := by
  decide +kernel

theorem coveredLeaf117 : CovBy 9 PR (Pg cN 9 BS TS) cell248 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf117]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload117) normal242 46 numeric117
theorem normalizedLeaf118 : AdaptiveCoverage.normalize SL cell246 = normal243 := by
  calc
    AdaptiveCoverage.normalize SL cell246 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell246)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell246)).symm
    _ = normal243 := by rfl

theorem numeric118 : ForcedCoverage2.dispatch (fun _ => payload118) normal243 46 = true := by
  decide +kernel

theorem coveredLeaf118 : CovBy 9 PR (Pg cN 9 BS TS) cell246 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf118]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload118) normal243 46 numeric118
theorem normalizedLeaf119 : AdaptiveCoverage.normalize SL cell251 = normal245 := by
  calc
    AdaptiveCoverage.normalize SL cell251 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell251)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell251)).symm
    _ = normal245 := by rfl

theorem numeric119 : ForcedCoverage2.dispatch (fun _ => payload119) normal245 46 = true := by
  decide +kernel

theorem coveredLeaf119 : CovBy 9 PR (Pg cN 9 BS TS) cell251 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf119]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload119) normal245 46 numeric119
theorem normalizedLeaf120 : AdaptiveCoverage.normalize SL cell255 = normal248 := by
  calc
    AdaptiveCoverage.normalize SL cell255 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell255)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell255)).symm
    _ = normal248 := by rfl

theorem numeric120 : ForcedCoverage2.dispatch (fun _ => payload120) normal248 46 = true := by
  decide +kernel

theorem coveredLeaf120 : CovBy 9 PR (Pg cN 9 BS TS) cell255 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf120]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload120) normal248 46 numeric120
theorem normalizedLeaf121 : AdaptiveCoverage.normalize SL cell257 = normal250 := by
  calc
    AdaptiveCoverage.normalize SL cell257 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell257)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell257)).symm
    _ = normal250 := by rfl

theorem numeric121 : ForcedCoverage2.dispatch (fun _ => payload121) normal250 46 = true := by
  decide +kernel

theorem coveredLeaf121 : CovBy 9 PR (Pg cN 9 BS TS) cell257 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf121]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload121) normal250 46 numeric121
theorem normalizedLeaf122 : AdaptiveCoverage.normalize SL cell258 = normal251 := by
  calc
    AdaptiveCoverage.normalize SL cell258 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell258)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell258)).symm
    _ = normal251 := by rfl

theorem numeric122 : ForcedCoverage2.dispatch (fun _ => payload122) normal251 46 = true := by
  decide +kernel

theorem coveredLeaf122 : CovBy 9 PR (Pg cN 9 BS TS) cell258 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf122]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload122) normal251 46 numeric122
theorem normalizedLeaf123 : AdaptiveCoverage.normalize SL cell259 = normal253 := by
  calc
    AdaptiveCoverage.normalize SL cell259 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell259)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell259)).symm
    _ = normal253 := by rfl

theorem numeric123 : ForcedCoverage2.dispatch (fun _ => payload123) normal253 46 = true := by
  decide +kernel

theorem coveredLeaf123 : CovBy 9 PR (Pg cN 9 BS TS) cell259 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf123]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload123) normal253 46 numeric123
theorem normalizedLeaf124 : AdaptiveCoverage.normalize SL cell260 = normal254 := by
  calc
    AdaptiveCoverage.normalize SL cell260 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell260)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell260)).symm
    _ = normal254 := by rfl

theorem numeric124 : ForcedCoverage2.dispatch (fun _ => payload124) normal254 46 = true := by
  decide +kernel

theorem coveredLeaf124 : CovBy 9 PR (Pg cN 9 BS TS) cell260 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf124]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload124) normal254 46 numeric124
theorem normalizedLeaf125 : AdaptiveCoverage.normalize SL cell138 = normal255 := by
  calc
    AdaptiveCoverage.normalize SL cell138 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell138)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell138)).symm
    _ = normal255 := by rfl

theorem numeric125 : ForcedCoverage2.dispatch (fun _ => payload125) normal255 46 = true := by
  decide +kernel

theorem coveredLeaf125 : CovBy 9 PR (Pg cN 9 BS TS) cell138 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf125]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload125) normal255 46 numeric125
theorem normalizedLeaf126 : AdaptiveCoverage.normalize SL cell136 = normal256 := by
  calc
    AdaptiveCoverage.normalize SL cell136 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell136)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell136)).symm
    _ = normal256 := by rfl

theorem numeric126 : ForcedCoverage2.dispatch (fun _ => payload126) normal256 46 = true := by
  decide +kernel

theorem coveredLeaf126 : CovBy 9 PR (Pg cN 9 BS TS) cell136 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf126]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload126) normal256 46 numeric126

set_option pp.fullNames true
#print axioms normalizedLeaf096
#print axioms numeric096
#print axioms coveredLeaf096
#print axioms normalizedLeaf097
#print axioms numeric097
#print axioms coveredLeaf097
#print axioms normalizedLeaf098
#print axioms numeric098
#print axioms coveredLeaf098
#print axioms normalizedLeaf099
#print axioms numeric099
#print axioms coveredLeaf099
#print axioms normalizedLeaf100
#print axioms numeric100
#print axioms coveredLeaf100
#print axioms normalizedLeaf101
#print axioms numeric101
#print axioms coveredLeaf101
#print axioms normalizedLeaf102
#print axioms numeric102
#print axioms coveredLeaf102
#print axioms normalizedLeaf103
#print axioms numeric103
#print axioms coveredLeaf103
#print axioms normalizedLeaf104
#print axioms numeric104
#print axioms coveredLeaf104
#print axioms normalizedLeaf105
#print axioms numeric105
#print axioms coveredLeaf105
#print axioms normalizedLeaf106
#print axioms numeric106
#print axioms coveredLeaf106
#print axioms normalizedLeaf107
#print axioms numeric107
#print axioms coveredLeaf107
#print axioms normalizedLeaf108
#print axioms numeric108
#print axioms coveredLeaf108
#print axioms normalizedLeaf109
#print axioms numeric109
#print axioms coveredLeaf109
#print axioms normalizedLeaf110
#print axioms numeric110
#print axioms coveredLeaf110
#print axioms normalizedLeaf111
#print axioms numeric111
#print axioms coveredLeaf111
#print axioms normalizedLeaf112
#print axioms numeric112
#print axioms coveredLeaf112
#print axioms normalizedLeaf113
#print axioms numeric113
#print axioms coveredLeaf113
#print axioms normalizedLeaf114
#print axioms numeric114
#print axioms coveredLeaf114
#print axioms normalizedLeaf115
#print axioms numeric115
#print axioms coveredLeaf115
#print axioms normalizedLeaf116
#print axioms numeric116
#print axioms coveredLeaf116
#print axioms normalizedLeaf117
#print axioms numeric117
#print axioms coveredLeaf117
#print axioms normalizedLeaf118
#print axioms numeric118
#print axioms coveredLeaf118
#print axioms normalizedLeaf119
#print axioms numeric119
#print axioms coveredLeaf119
#print axioms normalizedLeaf120
#print axioms numeric120
#print axioms coveredLeaf120
#print axioms normalizedLeaf121
#print axioms numeric121
#print axioms coveredLeaf121
#print axioms normalizedLeaf122
#print axioms numeric122
#print axioms coveredLeaf122
#print axioms normalizedLeaf123
#print axioms numeric123
#print axioms coveredLeaf123
#print axioms normalizedLeaf124
#print axioms numeric124
#print axioms coveredLeaf124
#print axioms normalizedLeaf125
#print axioms numeric125
#print axioms coveredLeaf125
#print axioms normalizedLeaf126
#print axioms numeric126
#print axioms coveredLeaf126
end StructuralGoal20261016.W10Aux127
end
