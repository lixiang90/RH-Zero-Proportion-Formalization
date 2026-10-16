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
theorem normalizedLeaf128 : AdaptiveCoverage.normalize SL cell285 = normal271 := by
  calc
    AdaptiveCoverage.normalize SL cell285 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell285)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell285)).symm
    _ = normal271 := by rfl

theorem numeric128 : ForcedCoverage2.dispatch (fun _ => payload128) normal271 46 = true := by
  decide +kernel

theorem coveredLeaf128 : CovBy 9 PR (Pg cN 9 BS TS) cell285 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf128]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload128) normal271 46 numeric128
theorem normalizedLeaf129 : AdaptiveCoverage.normalize SL cell286 = normal272 := by
  calc
    AdaptiveCoverage.normalize SL cell286 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell286)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell286)).symm
    _ = normal272 := by rfl

theorem numeric129 : ForcedCoverage2.dispatch (fun _ => payload129) normal272 46 = true := by
  decide +kernel

theorem coveredLeaf129 : CovBy 9 PR (Pg cN 9 BS TS) cell286 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf129]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload129) normal272 46 numeric129
theorem normalizedLeaf130 : AdaptiveCoverage.normalize SL cell282 = normal273 := by
  calc
    AdaptiveCoverage.normalize SL cell282 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell282)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell282)).symm
    _ = normal273 := by rfl

theorem numeric130 : ForcedCoverage2.dispatch (fun _ => payload130) normal273 46 = true := by
  decide +kernel

theorem coveredLeaf130 : CovBy 9 PR (Pg cN 9 BS TS) cell282 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf130]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload130) normal273 46 numeric130
theorem normalizedLeaf131 : AdaptiveCoverage.normalize SL cell272 = normal274 := by
  calc
    AdaptiveCoverage.normalize SL cell272 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell272)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell272)).symm
    _ = normal274 := by rfl

theorem numeric131 : ForcedCoverage2.dispatch (fun _ => payload131) normal274 46 = true := by
  decide +kernel

theorem coveredLeaf131 : CovBy 9 PR (Pg cN 9 BS TS) cell272 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf131]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload131) normal274 46 numeric131
theorem normalizedLeaf132 : AdaptiveCoverage.normalize SL cell289 = normal277 := by
  calc
    AdaptiveCoverage.normalize SL cell289 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell289)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell289)).symm
    _ = normal277 := by rfl

theorem numeric132 : ForcedCoverage2.dispatch (fun _ => payload132) normal277 46 = true := by
  decide +kernel

theorem coveredLeaf132 : CovBy 9 PR (Pg cN 9 BS TS) cell289 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf132]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload132) normal277 46 numeric132
theorem normalizedLeaf133 : AdaptiveCoverage.normalize SL cell291 = normal279 := by
  calc
    AdaptiveCoverage.normalize SL cell291 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell291)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell291)).symm
    _ = normal279 := by rfl

theorem numeric133 : ForcedCoverage2.dispatch (fun _ => payload133) normal279 46 = true := by
  decide +kernel

theorem coveredLeaf133 : CovBy 9 PR (Pg cN 9 BS TS) cell291 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf133]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload133) normal279 46 numeric133
theorem normalizedLeaf134 : AdaptiveCoverage.normalize SL cell293 = normal281 := by
  calc
    AdaptiveCoverage.normalize SL cell293 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell293)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell293)).symm
    _ = normal281 := by rfl

theorem numeric134 : ForcedCoverage2.dispatch (fun _ => payload134) normal281 46 = true := by
  decide +kernel

theorem coveredLeaf134 : CovBy 9 PR (Pg cN 9 BS TS) cell293 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf134]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload134) normal281 46 numeric134
theorem normalizedLeaf135 : AdaptiveCoverage.normalize SL cell297 = normal284 := by
  calc
    AdaptiveCoverage.normalize SL cell297 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell297)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell297)).symm
    _ = normal284 := by rfl

theorem numeric135 : ForcedCoverage2.dispatch (fun _ => payload135) normal284 46 = true := by
  decide +kernel

theorem coveredLeaf135 : CovBy 9 PR (Pg cN 9 BS TS) cell297 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf135]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload135) normal284 46 numeric135
theorem normalizedLeaf136 : AdaptiveCoverage.normalize SL cell299 = normal286 := by
  calc
    AdaptiveCoverage.normalize SL cell299 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell299)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell299)).symm
    _ = normal286 := by rfl

theorem numeric136 : ForcedCoverage2.dispatch (fun _ => payload136) normal286 46 = true := by
  decide +kernel

theorem coveredLeaf136 : CovBy 9 PR (Pg cN 9 BS TS) cell299 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf136]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload136) normal286 46 numeric136
theorem normalizedLeaf137 : AdaptiveCoverage.normalize SL cell300 = normal287 := by
  calc
    AdaptiveCoverage.normalize SL cell300 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell300)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell300)).symm
    _ = normal287 := by rfl

theorem numeric137 : ForcedCoverage2.dispatch (fun _ => payload137) normal287 46 = true := by
  decide +kernel

theorem coveredLeaf137 : CovBy 9 PR (Pg cN 9 BS TS) cell300 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf137]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload137) normal287 46 numeric137
theorem normalizedLeaf138 : AdaptiveCoverage.normalize SL cell296 = normal288 := by
  calc
    AdaptiveCoverage.normalize SL cell296 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell296)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell296)).symm
    _ = normal288 := by rfl

theorem numeric138 : ForcedCoverage2.dispatch (fun _ => payload138) normal288 46 = true := by
  decide +kernel

theorem coveredLeaf138 : CovBy 9 PR (Pg cN 9 BS TS) cell296 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf138]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload138) normal288 46 numeric138
theorem normalizedLeaf139 : AdaptiveCoverage.normalize SL cell301 = normal290 := by
  calc
    AdaptiveCoverage.normalize SL cell301 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell301)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell301)).symm
    _ = normal290 := by rfl

theorem numeric139 : ForcedCoverage2.dispatch (fun _ => payload139) normal290 46 = true := by
  decide +kernel

theorem coveredLeaf139 : CovBy 9 PR (Pg cN 9 BS TS) cell301 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf139]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload139) normal290 46 numeric139
theorem normalizedLeaf140 : AdaptiveCoverage.normalize SL cell303 = normal292 := by
  calc
    AdaptiveCoverage.normalize SL cell303 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell303)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell303)).symm
    _ = normal292 := by rfl

theorem numeric140 : ForcedCoverage2.dispatch (fun _ => payload140) normal292 46 = true := by
  decide +kernel

theorem coveredLeaf140 : CovBy 9 PR (Pg cN 9 BS TS) cell303 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf140]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload140) normal292 46 numeric140
theorem normalizedLeaf141 : AdaptiveCoverage.normalize SL cell304 = normal293 := by
  calc
    AdaptiveCoverage.normalize SL cell304 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell304)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell304)).symm
    _ = normal293 := by rfl

theorem numeric141 : ForcedCoverage2.dispatch (fun _ => payload141) normal293 46 = true := by
  decide +kernel

theorem coveredLeaf141 : CovBy 9 PR (Pg cN 9 BS TS) cell304 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf141]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload141) normal293 46 numeric141
theorem normalizedLeaf142 : AdaptiveCoverage.normalize SL cell268 = normal294 := by
  calc
    AdaptiveCoverage.normalize SL cell268 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell268)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell268)).symm
    _ = normal294 := by rfl

theorem numeric142 : ForcedCoverage2.dispatch (fun _ => payload142) normal294 46 = true := by
  decide +kernel

theorem coveredLeaf142 : CovBy 9 PR (Pg cN 9 BS TS) cell268 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf142]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload142) normal294 46 numeric142
theorem normalizedLeaf143 : AdaptiveCoverage.normalize SL cell266 = normal295 := by
  calc
    AdaptiveCoverage.normalize SL cell266 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell266)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell266)).symm
    _ = normal295 := by rfl

theorem numeric143 : ForcedCoverage2.dispatch (fun _ => payload143) normal295 46 = true := by
  decide +kernel

theorem coveredLeaf143 : CovBy 9 PR (Pg cN 9 BS TS) cell266 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf143]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload143) normal295 46 numeric143
theorem normalizedLeaf144 : AdaptiveCoverage.normalize SL cell305 = normal297 := by
  calc
    AdaptiveCoverage.normalize SL cell305 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell305)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell305)).symm
    _ = normal297 := by rfl

theorem numeric144 : ForcedCoverage2.dispatch (fun _ => payload144) normal297 46 = true := by
  decide +kernel

theorem coveredLeaf144 : CovBy 9 PR (Pg cN 9 BS TS) cell305 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf144]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload144) normal297 46 numeric144
theorem normalizedLeaf145 : AdaptiveCoverage.normalize SL cell315 = normal303 := by
  calc
    AdaptiveCoverage.normalize SL cell315 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell315)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell315)).symm
    _ = normal303 := by rfl

theorem numeric145 : ForcedCoverage2.dispatch (fun _ => payload145) normal303 46 = true := by
  decide +kernel

theorem coveredLeaf145 : CovBy 9 PR (Pg cN 9 BS TS) cell315 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf145]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload145) normal303 46 numeric145
theorem normalizedLeaf146 : AdaptiveCoverage.normalize SL cell319 = normal306 := by
  calc
    AdaptiveCoverage.normalize SL cell319 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell319)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell319)).symm
    _ = normal306 := by rfl

theorem numeric146 : ForcedCoverage2.dispatch (fun _ => payload146) normal306 46 = true := by
  decide +kernel

theorem coveredLeaf146 : CovBy 9 PR (Pg cN 9 BS TS) cell319 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf146]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload146) normal306 46 numeric146
theorem normalizedLeaf147 : AdaptiveCoverage.normalize SL cell321 = normal308 := by
  calc
    AdaptiveCoverage.normalize SL cell321 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell321)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell321)).symm
    _ = normal308 := by rfl

theorem numeric147 : ForcedCoverage2.dispatch (fun _ => payload147) normal308 46 = true := by
  decide +kernel

theorem coveredLeaf147 : CovBy 9 PR (Pg cN 9 BS TS) cell321 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf147]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload147) normal308 46 numeric147
theorem normalizedLeaf148 : AdaptiveCoverage.normalize SL cell322 = normal309 := by
  calc
    AdaptiveCoverage.normalize SL cell322 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell322)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell322)).symm
    _ = normal309 := by rfl

theorem numeric148 : ForcedCoverage2.dispatch (fun _ => payload148) normal309 46 = true := by
  decide +kernel

theorem coveredLeaf148 : CovBy 9 PR (Pg cN 9 BS TS) cell322 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf148]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload148) normal309 46 numeric148
theorem normalizedLeaf149 : AdaptiveCoverage.normalize SL cell318 = normal310 := by
  calc
    AdaptiveCoverage.normalize SL cell318 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell318)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell318)).symm
    _ = normal310 := by rfl

theorem numeric149 : ForcedCoverage2.dispatch (fun _ => payload149) normal310 46 = true := by
  decide +kernel

theorem coveredLeaf149 : CovBy 9 PR (Pg cN 9 BS TS) cell318 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf149]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload149) normal310 46 numeric149
theorem normalizedLeaf150 : AdaptiveCoverage.normalize SL cell314 = normal311 := by
  calc
    AdaptiveCoverage.normalize SL cell314 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell314)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell314)).symm
    _ = normal311 := by rfl

theorem numeric150 : ForcedCoverage2.dispatch (fun _ => payload150) normal311 46 = true := by
  decide +kernel

theorem coveredLeaf150 : CovBy 9 PR (Pg cN 9 BS TS) cell314 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf150]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload150) normal311 46 numeric150
theorem normalizedLeaf151 : AdaptiveCoverage.normalize SL cell312 = normal312 := by
  calc
    AdaptiveCoverage.normalize SL cell312 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell312)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell312)).symm
    _ = normal312 := by rfl

theorem numeric151 : ForcedCoverage2.dispatch (fun _ => payload151) normal312 46 = true := by
  decide +kernel

theorem coveredLeaf151 : CovBy 9 PR (Pg cN 9 BS TS) cell312 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf151]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload151) normal312 46 numeric151
theorem normalizedLeaf152 : AdaptiveCoverage.normalize SL cell310 = normal313 := by
  calc
    AdaptiveCoverage.normalize SL cell310 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell310)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell310)).symm
    _ = normal313 := by rfl

theorem numeric152 : ForcedCoverage2.dispatch (fun _ => payload152) normal313 46 = true := by
  decide +kernel

theorem coveredLeaf152 : CovBy 9 PR (Pg cN 9 BS TS) cell310 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf152]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload152) normal313 46 numeric152
theorem normalizedLeaf153 : AdaptiveCoverage.normalize SL cell329 = normal318 := by
  calc
    AdaptiveCoverage.normalize SL cell329 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell329)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell329)).symm
    _ = normal318 := by rfl

theorem numeric153 : ForcedCoverage2.dispatch (fun _ => payload153) normal318 46 = true := by
  decide +kernel

theorem coveredLeaf153 : CovBy 9 PR (Pg cN 9 BS TS) cell329 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf153]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload153) normal318 46 numeric153
theorem normalizedLeaf154 : AdaptiveCoverage.normalize SL cell331 = normal320 := by
  calc
    AdaptiveCoverage.normalize SL cell331 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell331)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell331)).symm
    _ = normal320 := by rfl

theorem numeric154 : ForcedCoverage2.dispatch (fun _ => payload154) normal320 46 = true := by
  decide +kernel

theorem coveredLeaf154 : CovBy 9 PR (Pg cN 9 BS TS) cell331 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf154]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload154) normal320 46 numeric154
theorem normalizedLeaf155 : AdaptiveCoverage.normalize SL cell333 = normal322 := by
  calc
    AdaptiveCoverage.normalize SL cell333 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell333)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell333)).symm
    _ = normal322 := by rfl

theorem numeric155 : ForcedCoverage2.dispatch (fun _ => payload155) normal322 46 = true := by
  decide +kernel

theorem coveredLeaf155 : CovBy 9 PR (Pg cN 9 BS TS) cell333 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf155]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload155) normal322 46 numeric155
theorem normalizedLeaf156 : AdaptiveCoverage.normalize SL cell335 = normal324 := by
  calc
    AdaptiveCoverage.normalize SL cell335 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell335)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell335)).symm
    _ = normal324 := by rfl

theorem numeric156 : ForcedCoverage2.dispatch (fun _ => payload156) normal324 46 = true := by
  decide +kernel

theorem coveredLeaf156 : CovBy 9 PR (Pg cN 9 BS TS) cell335 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf156]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload156) normal324 46 numeric156
theorem normalizedLeaf157 : AdaptiveCoverage.normalize SL cell339 = normal327 := by
  calc
    AdaptiveCoverage.normalize SL cell339 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell339)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell339)).symm
    _ = normal327 := by rfl

theorem numeric157 : ForcedCoverage2.dispatch (fun _ => payload157) normal327 46 = true := by
  decide +kernel

theorem coveredLeaf157 : CovBy 9 PR (Pg cN 9 BS TS) cell339 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf157]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload157) normal327 46 numeric157
theorem normalizedLeaf158 : AdaptiveCoverage.normalize SL cell341 = normal329 := by
  calc
    AdaptiveCoverage.normalize SL cell341 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell341)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell341)).symm
    _ = normal329 := by rfl

theorem numeric158 : ForcedCoverage2.dispatch (fun _ => payload158) normal329 46 = true := by
  decide +kernel

theorem coveredLeaf158 : CovBy 9 PR (Pg cN 9 BS TS) cell341 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf158]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload158) normal329 46 numeric158
theorem normalizedLeaf159 : AdaptiveCoverage.normalize SL cell342 = normal330 := by
  calc
    AdaptiveCoverage.normalize SL cell342 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell342)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell342)).symm
    _ = normal330 := by rfl

theorem numeric159 : ForcedCoverage2.dispatch (fun _ => payload159) normal330 46 = true := by
  decide +kernel

theorem coveredLeaf159 : CovBy 9 PR (Pg cN 9 BS TS) cell342 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf159]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload159) normal330 46 numeric159

set_option pp.fullNames true
#print axioms normalizedLeaf128
#print axioms numeric128
#print axioms coveredLeaf128
#print axioms normalizedLeaf129
#print axioms numeric129
#print axioms coveredLeaf129
#print axioms normalizedLeaf130
#print axioms numeric130
#print axioms coveredLeaf130
#print axioms normalizedLeaf131
#print axioms numeric131
#print axioms coveredLeaf131
#print axioms normalizedLeaf132
#print axioms numeric132
#print axioms coveredLeaf132
#print axioms normalizedLeaf133
#print axioms numeric133
#print axioms coveredLeaf133
#print axioms normalizedLeaf134
#print axioms numeric134
#print axioms coveredLeaf134
#print axioms normalizedLeaf135
#print axioms numeric135
#print axioms coveredLeaf135
#print axioms normalizedLeaf136
#print axioms numeric136
#print axioms coveredLeaf136
#print axioms normalizedLeaf137
#print axioms numeric137
#print axioms coveredLeaf137
#print axioms normalizedLeaf138
#print axioms numeric138
#print axioms coveredLeaf138
#print axioms normalizedLeaf139
#print axioms numeric139
#print axioms coveredLeaf139
#print axioms normalizedLeaf140
#print axioms numeric140
#print axioms coveredLeaf140
#print axioms normalizedLeaf141
#print axioms numeric141
#print axioms coveredLeaf141
#print axioms normalizedLeaf142
#print axioms numeric142
#print axioms coveredLeaf142
#print axioms normalizedLeaf143
#print axioms numeric143
#print axioms coveredLeaf143
#print axioms normalizedLeaf144
#print axioms numeric144
#print axioms coveredLeaf144
#print axioms normalizedLeaf145
#print axioms numeric145
#print axioms coveredLeaf145
#print axioms normalizedLeaf146
#print axioms numeric146
#print axioms coveredLeaf146
#print axioms normalizedLeaf147
#print axioms numeric147
#print axioms coveredLeaf147
#print axioms normalizedLeaf148
#print axioms numeric148
#print axioms coveredLeaf148
#print axioms normalizedLeaf149
#print axioms numeric149
#print axioms coveredLeaf149
#print axioms normalizedLeaf150
#print axioms numeric150
#print axioms coveredLeaf150
#print axioms normalizedLeaf151
#print axioms numeric151
#print axioms coveredLeaf151
#print axioms normalizedLeaf152
#print axioms numeric152
#print axioms coveredLeaf152
#print axioms normalizedLeaf153
#print axioms numeric153
#print axioms coveredLeaf153
#print axioms normalizedLeaf154
#print axioms numeric154
#print axioms coveredLeaf154
#print axioms normalizedLeaf155
#print axioms numeric155
#print axioms coveredLeaf155
#print axioms normalizedLeaf156
#print axioms numeric156
#print axioms coveredLeaf156
#print axioms normalizedLeaf157
#print axioms numeric157
#print axioms coveredLeaf157
#print axioms normalizedLeaf158
#print axioms numeric158
#print axioms coveredLeaf158
#print axioms normalizedLeaf159
#print axioms numeric159
#print axioms coveredLeaf159
end StructuralGoal20261016.W10Aux478
end
