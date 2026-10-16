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
theorem normalizedLeaf096 : AdaptiveCoverage.normalize SL cell217 = normal205 := by
  calc
    AdaptiveCoverage.normalize SL cell217 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell217)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell217)).symm
    _ = normal205 := by rfl

theorem numeric096 : ForcedCoverage2.dispatch (fun _ => payload096) normal205 46 = true := by
  decide +kernel

theorem coveredLeaf096 : CovBy 9 PR (Pg cN 9 BS TS) cell217 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf096]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload096) normal205 46 numeric096
theorem normalizedLeaf097 : AdaptiveCoverage.normalize SL cell218 = normal206 := by
  calc
    AdaptiveCoverage.normalize SL cell218 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell218)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell218)).symm
    _ = normal206 := by rfl

theorem numeric097 : ForcedCoverage2.dispatch (fun _ => payload097) normal206 46 = true := by
  decide +kernel

theorem coveredLeaf097 : CovBy 9 PR (Pg cN 9 BS TS) cell218 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf097]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload097) normal206 46 numeric097
theorem normalizedLeaf098 : AdaptiveCoverage.normalize SL cell214 = normal207 := by
  calc
    AdaptiveCoverage.normalize SL cell214 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell214)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell214)).symm
    _ = normal207 := by rfl

theorem numeric098 : ForcedCoverage2.dispatch (fun _ => payload098) normal207 46 = true := by
  decide +kernel

theorem coveredLeaf098 : CovBy 9 PR (Pg cN 9 BS TS) cell214 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf098]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload098) normal207 46 numeric098
theorem normalizedLeaf099 : AdaptiveCoverage.normalize SL cell221 = normal210 := by
  calc
    AdaptiveCoverage.normalize SL cell221 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell221)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell221)).symm
    _ = normal210 := by rfl

theorem numeric099 : ForcedCoverage2.dispatch (fun _ => payload099) normal210 46 = true := by
  decide +kernel

theorem coveredLeaf099 : CovBy 9 PR (Pg cN 9 BS TS) cell221 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf099]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload099) normal210 46 numeric099
theorem normalizedLeaf100 : AdaptiveCoverage.normalize SL cell223 = normal212 := by
  calc
    AdaptiveCoverage.normalize SL cell223 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell223)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell223)).symm
    _ = normal212 := by rfl

theorem numeric100 : ForcedCoverage2.dispatch (fun _ => payload100) normal212 46 = true := by
  decide +kernel

theorem coveredLeaf100 : CovBy 9 PR (Pg cN 9 BS TS) cell223 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf100]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload100) normal212 46 numeric100
theorem normalizedLeaf101 : AdaptiveCoverage.normalize SL cell225 = normal214 := by
  calc
    AdaptiveCoverage.normalize SL cell225 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell225)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell225)).symm
    _ = normal214 := by rfl

theorem numeric101 : ForcedCoverage2.dispatch (fun _ => payload101) normal214 46 = true := by
  decide +kernel

theorem coveredLeaf101 : CovBy 9 PR (Pg cN 9 BS TS) cell225 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf101]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload101) normal214 46 numeric101
theorem normalizedLeaf102 : AdaptiveCoverage.normalize SL cell226 = normal215 := by
  calc
    AdaptiveCoverage.normalize SL cell226 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell226)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell226)).symm
    _ = normal215 := by rfl

theorem numeric102 : ForcedCoverage2.dispatch (fun _ => payload102) normal215 46 = true := by
  decide +kernel

theorem coveredLeaf102 : CovBy 9 PR (Pg cN 9 BS TS) cell226 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf102]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload102) normal215 46 numeric102
theorem normalizedLeaf103 : AdaptiveCoverage.normalize SL cell220 = normal216 := by
  calc
    AdaptiveCoverage.normalize SL cell220 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell220)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell220)).symm
    _ = normal216 := by rfl

theorem numeric103 : ForcedCoverage2.dispatch (fun _ => payload103) normal216 46 = true := by
  decide +kernel

theorem coveredLeaf103 : CovBy 9 PR (Pg cN 9 BS TS) cell220 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf103]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload103) normal216 46 numeric103
theorem normalizedLeaf104 : AdaptiveCoverage.normalize SL cell229 = normal219 := by
  calc
    AdaptiveCoverage.normalize SL cell229 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell229)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell229)).symm
    _ = normal219 := by rfl

theorem numeric104 : ForcedCoverage2.dispatch (fun _ => payload104) normal219 46 = true := by
  decide +kernel

theorem coveredLeaf104 : CovBy 9 PR (Pg cN 9 BS TS) cell229 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf104]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload104) normal219 46 numeric104
theorem normalizedLeaf105 : AdaptiveCoverage.normalize SL cell233 = normal222 := by
  calc
    AdaptiveCoverage.normalize SL cell233 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell233)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell233)).symm
    _ = normal222 := by rfl

theorem numeric105 : ForcedCoverage2.dispatch (fun _ => payload105) normal222 46 = true := by
  decide +kernel

theorem coveredLeaf105 : CovBy 9 PR (Pg cN 9 BS TS) cell233 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf105]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload105) normal222 46 numeric105
theorem normalizedLeaf106 : AdaptiveCoverage.normalize SL cell235 = normal224 := by
  calc
    AdaptiveCoverage.normalize SL cell235 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell235)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell235)).symm
    _ = normal224 := by rfl

theorem numeric106 : ForcedCoverage2.dispatch (fun _ => payload106) normal224 46 = true := by
  decide +kernel

theorem coveredLeaf106 : CovBy 9 PR (Pg cN 9 BS TS) cell235 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf106]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload106) normal224 46 numeric106
theorem normalizedLeaf107 : AdaptiveCoverage.normalize SL cell236 = normal225 := by
  calc
    AdaptiveCoverage.normalize SL cell236 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell236)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell236)).symm
    _ = normal225 := by rfl

theorem numeric107 : ForcedCoverage2.dispatch (fun _ => payload107) normal225 46 = true := by
  decide +kernel

theorem coveredLeaf107 : CovBy 9 PR (Pg cN 9 BS TS) cell236 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf107]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload107) normal225 46 numeric107
theorem normalizedLeaf108 : AdaptiveCoverage.normalize SL cell232 = normal226 := by
  calc
    AdaptiveCoverage.normalize SL cell232 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell232)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell232)).symm
    _ = normal226 := by rfl

theorem numeric108 : ForcedCoverage2.dispatch (fun _ => payload108) normal226 46 = true := by
  decide +kernel

theorem coveredLeaf108 : CovBy 9 PR (Pg cN 9 BS TS) cell232 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf108]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload108) normal226 46 numeric108
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
theorem normalizedLeaf110 : AdaptiveCoverage.normalize SL cell245 = normal233 := by
  calc
    AdaptiveCoverage.normalize SL cell245 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell245)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell245)).symm
    _ = normal233 := by rfl

theorem numeric110 : ForcedCoverage2.dispatch (fun _ => payload110) normal233 46 = true := by
  decide +kernel

theorem coveredLeaf110 : CovBy 9 PR (Pg cN 9 BS TS) cell245 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf110]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload110) normal233 46 numeric110
theorem normalizedLeaf111 : AdaptiveCoverage.normalize SL cell247 = normal235 := by
  calc
    AdaptiveCoverage.normalize SL cell247 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell247)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell247)).symm
    _ = normal235 := by rfl

theorem numeric111 : ForcedCoverage2.dispatch (fun _ => payload111) normal235 46 = true := by
  decide +kernel

theorem coveredLeaf111 : CovBy 9 PR (Pg cN 9 BS TS) cell247 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf111]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload111) normal235 46 numeric111
theorem normalizedLeaf112 : AdaptiveCoverage.normalize SL cell248 = normal236 := by
  calc
    AdaptiveCoverage.normalize SL cell248 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell248)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell248)).symm
    _ = normal236 := by rfl

theorem numeric112 : ForcedCoverage2.dispatch (fun _ => payload112) normal236 46 = true := by
  decide +kernel

theorem coveredLeaf112 : CovBy 9 PR (Pg cN 9 BS TS) cell248 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf112]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload112) normal236 46 numeric112
theorem normalizedLeaf113 : AdaptiveCoverage.normalize SL cell244 = normal237 := by
  calc
    AdaptiveCoverage.normalize SL cell244 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell244)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell244)).symm
    _ = normal237 := by rfl

theorem numeric113 : ForcedCoverage2.dispatch (fun _ => payload113) normal237 46 = true := by
  decide +kernel

theorem coveredLeaf113 : CovBy 9 PR (Pg cN 9 BS TS) cell244 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf113]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload113) normal237 46 numeric113
theorem normalizedLeaf114 : AdaptiveCoverage.normalize SL cell251 = normal240 := by
  calc
    AdaptiveCoverage.normalize SL cell251 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell251)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell251)).symm
    _ = normal240 := by rfl

theorem numeric114 : ForcedCoverage2.dispatch (fun _ => payload114) normal240 46 = true := by
  decide +kernel

theorem coveredLeaf114 : CovBy 9 PR (Pg cN 9 BS TS) cell251 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf114]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload114) normal240 46 numeric114
theorem normalizedLeaf115 : AdaptiveCoverage.normalize SL cell253 = normal242 := by
  calc
    AdaptiveCoverage.normalize SL cell253 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell253)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell253)).symm
    _ = normal242 := by rfl

theorem numeric115 : ForcedCoverage2.dispatch (fun _ => payload115) normal242 46 = true := by
  decide +kernel

theorem coveredLeaf115 : CovBy 9 PR (Pg cN 9 BS TS) cell253 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf115]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload115) normal242 46 numeric115
theorem normalizedLeaf116 : AdaptiveCoverage.normalize SL cell254 = normal243 := by
  calc
    AdaptiveCoverage.normalize SL cell254 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell254)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell254)).symm
    _ = normal243 := by rfl

theorem numeric116 : ForcedCoverage2.dispatch (fun _ => payload116) normal243 46 = true := by
  decide +kernel

theorem coveredLeaf116 : CovBy 9 PR (Pg cN 9 BS TS) cell254 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf116]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload116) normal243 46 numeric116
theorem normalizedLeaf117 : AdaptiveCoverage.normalize SL cell250 = normal244 := by
  calc
    AdaptiveCoverage.normalize SL cell250 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell250)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell250)).symm
    _ = normal244 := by rfl

theorem numeric117 : ForcedCoverage2.dispatch (fun _ => payload117) normal244 46 = true := by
  decide +kernel

theorem coveredLeaf117 : CovBy 9 PR (Pg cN 9 BS TS) cell250 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf117]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload117) normal244 46 numeric117
theorem normalizedLeaf118 : AdaptiveCoverage.normalize SL cell257 = normal247 := by
  calc
    AdaptiveCoverage.normalize SL cell257 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell257)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell257)).symm
    _ = normal247 := by rfl

theorem numeric118 : ForcedCoverage2.dispatch (fun _ => payload118) normal247 46 = true := by
  decide +kernel

theorem coveredLeaf118 : CovBy 9 PR (Pg cN 9 BS TS) cell257 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf118]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload118) normal247 46 numeric118
theorem normalizedLeaf119 : AdaptiveCoverage.normalize SL cell259 = normal249 := by
  calc
    AdaptiveCoverage.normalize SL cell259 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell259)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell259)).symm
    _ = normal249 := by rfl

theorem numeric119 : ForcedCoverage2.dispatch (fun _ => payload119) normal249 46 = true := by
  decide +kernel

theorem coveredLeaf119 : CovBy 9 PR (Pg cN 9 BS TS) cell259 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf119]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload119) normal249 46 numeric119
theorem normalizedLeaf120 : AdaptiveCoverage.normalize SL cell260 = normal250 := by
  calc
    AdaptiveCoverage.normalize SL cell260 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell260)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell260)).symm
    _ = normal250 := by rfl

theorem numeric120 : ForcedCoverage2.dispatch (fun _ => payload120) normal250 46 = true := by
  decide +kernel

theorem coveredLeaf120 : CovBy 9 PR (Pg cN 9 BS TS) cell260 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf120]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload120) normal250 46 numeric120
theorem normalizedLeaf121 : AdaptiveCoverage.normalize SL cell256 = normal251 := by
  calc
    AdaptiveCoverage.normalize SL cell256 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell256)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell256)).symm
    _ = normal251 := by rfl

theorem numeric121 : ForcedCoverage2.dispatch (fun _ => payload121) normal251 46 = true := by
  decide +kernel

theorem coveredLeaf121 : CovBy 9 PR (Pg cN 9 BS TS) cell256 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf121]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload121) normal251 46 numeric121
theorem normalizedLeaf122 : AdaptiveCoverage.normalize SL cell263 = normal254 := by
  calc
    AdaptiveCoverage.normalize SL cell263 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell263)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell263)).symm
    _ = normal254 := by rfl

theorem numeric122 : ForcedCoverage2.dispatch (fun _ => payload122) normal254 46 = true := by
  decide +kernel

theorem coveredLeaf122 : CovBy 9 PR (Pg cN 9 BS TS) cell263 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf122]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload122) normal254 46 numeric122
theorem normalizedLeaf123 : AdaptiveCoverage.normalize SL cell273 = normal260 := by
  calc
    AdaptiveCoverage.normalize SL cell273 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell273)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell273)).symm
    _ = normal260 := by rfl

theorem numeric123 : ForcedCoverage2.dispatch (fun _ => payload123) normal260 46 = true := by
  decide +kernel

theorem coveredLeaf123 : CovBy 9 PR (Pg cN 9 BS TS) cell273 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf123]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload123) normal260 46 numeric123
theorem normalizedLeaf124 : AdaptiveCoverage.normalize SL cell275 = normal262 := by
  calc
    AdaptiveCoverage.normalize SL cell275 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell275)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell275)).symm
    _ = normal262 := by rfl

theorem numeric124 : ForcedCoverage2.dispatch (fun _ => payload124) normal262 46 = true := by
  decide +kernel

theorem coveredLeaf124 : CovBy 9 PR (Pg cN 9 BS TS) cell275 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf124]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload124) normal262 46 numeric124
theorem normalizedLeaf125 : AdaptiveCoverage.normalize SL cell277 = normal264 := by
  calc
    AdaptiveCoverage.normalize SL cell277 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell277)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell277)).symm
    _ = normal264 := by rfl

theorem numeric125 : ForcedCoverage2.dispatch (fun _ => payload125) normal264 46 = true := by
  decide +kernel

theorem coveredLeaf125 : CovBy 9 PR (Pg cN 9 BS TS) cell277 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf125]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload125) normal264 46 numeric125
theorem normalizedLeaf126 : AdaptiveCoverage.normalize SL cell279 = normal266 := by
  calc
    AdaptiveCoverage.normalize SL cell279 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell279)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell279)).symm
    _ = normal266 := by rfl

theorem numeric126 : ForcedCoverage2.dispatch (fun _ => payload126) normal266 46 = true := by
  decide +kernel

theorem coveredLeaf126 : CovBy 9 PR (Pg cN 9 BS TS) cell279 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf126]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload126) normal266 46 numeric126
theorem normalizedLeaf127 : AdaptiveCoverage.normalize SL cell283 = normal269 := by
  calc
    AdaptiveCoverage.normalize SL cell283 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell283)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell283)).symm
    _ = normal269 := by rfl

theorem numeric127 : ForcedCoverage2.dispatch (fun _ => payload127) normal269 46 = true := by
  decide +kernel

theorem coveredLeaf127 : CovBy 9 PR (Pg cN 9 BS TS) cell283 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf127]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload127) normal269 46 numeric127

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
#print axioms normalizedLeaf127
#print axioms numeric127
#print axioms coveredLeaf127
end StructuralGoal20261016.W10Aux478
end
