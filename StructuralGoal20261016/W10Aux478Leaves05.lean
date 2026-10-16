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
theorem normalizedLeaf160 : AdaptiveCoverage.normalize SL cell338 = normal331 := by
  calc
    AdaptiveCoverage.normalize SL cell338 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell338)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell338)).symm
    _ = normal331 := by rfl

theorem numeric160 : ForcedCoverage2.dispatch (fun _ => payload160) normal331 46 = true := by
  decide +kernel

theorem coveredLeaf160 : CovBy 9 PR (Pg cN 9 BS TS) cell338 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf160]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload160) normal331 46 numeric160
theorem normalizedLeaf161 : AdaptiveCoverage.normalize SL cell343 = normal333 := by
  calc
    AdaptiveCoverage.normalize SL cell343 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell343)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell343)).symm
    _ = normal333 := by rfl

theorem numeric161 : ForcedCoverage2.dispatch (fun _ => payload161) normal333 46 = true := by
  decide +kernel

theorem coveredLeaf161 : CovBy 9 PR (Pg cN 9 BS TS) cell343 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf161]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload161) normal333 46 numeric161
theorem normalizedLeaf162 : AdaptiveCoverage.normalize SL cell345 = normal335 := by
  calc
    AdaptiveCoverage.normalize SL cell345 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell345)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell345)).symm
    _ = normal335 := by rfl

theorem numeric162 : ForcedCoverage2.dispatch (fun _ => payload162) normal335 46 = true := by
  decide +kernel

theorem coveredLeaf162 : CovBy 9 PR (Pg cN 9 BS TS) cell345 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf162]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload162) normal335 46 numeric162
theorem normalizedLeaf163 : AdaptiveCoverage.normalize SL cell347 = normal337 := by
  calc
    AdaptiveCoverage.normalize SL cell347 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell347)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell347)).symm
    _ = normal337 := by rfl

theorem numeric163 : ForcedCoverage2.dispatch (fun _ => payload163) normal337 46 = true := by
  decide +kernel

theorem coveredLeaf163 : CovBy 9 PR (Pg cN 9 BS TS) cell347 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf163]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload163) normal337 46 numeric163
theorem normalizedLeaf164 : AdaptiveCoverage.normalize SL cell349 = normal339 := by
  calc
    AdaptiveCoverage.normalize SL cell349 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell349)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell349)).symm
    _ = normal339 := by rfl

theorem numeric164 : ForcedCoverage2.dispatch (fun _ => payload164) normal339 46 = true := by
  decide +kernel

theorem coveredLeaf164 : CovBy 9 PR (Pg cN 9 BS TS) cell349 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf164]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload164) normal339 46 numeric164
theorem normalizedLeaf165 : AdaptiveCoverage.normalize SL cell351 = normal341 := by
  calc
    AdaptiveCoverage.normalize SL cell351 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell351)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell351)).symm
    _ = normal341 := by rfl

theorem numeric165 : ForcedCoverage2.dispatch (fun _ => payload165) normal341 46 = true := by
  decide +kernel

theorem coveredLeaf165 : CovBy 9 PR (Pg cN 9 BS TS) cell351 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf165]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload165) normal341 46 numeric165
theorem normalizedLeaf166 : AdaptiveCoverage.normalize SL cell353 = normal343 := by
  calc
    AdaptiveCoverage.normalize SL cell353 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell353)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell353)).symm
    _ = normal343 := by rfl

theorem numeric166 : ForcedCoverage2.dispatch (fun _ => payload166) normal343 46 = true := by
  decide +kernel

theorem coveredLeaf166 : CovBy 9 PR (Pg cN 9 BS TS) cell353 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf166]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload166) normal343 46 numeric166
theorem normalizedLeaf167 : AdaptiveCoverage.normalize SL cell359 = normal347 := by
  calc
    AdaptiveCoverage.normalize SL cell359 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell359)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell359)).symm
    _ = normal347 := by rfl

theorem numeric167 : ForcedCoverage2.dispatch (fun _ => payload167) normal347 46 = true := by
  decide +kernel

theorem coveredLeaf167 : CovBy 9 PR (Pg cN 9 BS TS) cell359 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf167]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload167) normal347 46 numeric167
theorem normalizedLeaf168 : AdaptiveCoverage.normalize SL cell360 = normal348 := by
  calc
    AdaptiveCoverage.normalize SL cell360 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell360)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell360)).symm
    _ = normal348 := by rfl

theorem numeric168 : ForcedCoverage2.dispatch (fun _ => payload168) normal348 46 = true := by
  decide +kernel

theorem coveredLeaf168 : CovBy 9 PR (Pg cN 9 BS TS) cell360 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf168]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload168) normal348 46 numeric168
theorem normalizedLeaf169 : AdaptiveCoverage.normalize SL cell358 = normal349 := by
  calc
    AdaptiveCoverage.normalize SL cell358 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell358)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell358)).symm
    _ = normal349 := by rfl

theorem numeric169 : ForcedCoverage2.dispatch (fun _ => payload169) normal349 46 = true := by
  decide +kernel

theorem coveredLeaf169 : CovBy 9 PR (Pg cN 9 BS TS) cell358 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf169]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload169) normal349 46 numeric169
theorem normalizedLeaf170 : AdaptiveCoverage.normalize SL cell356 = normal350 := by
  calc
    AdaptiveCoverage.normalize SL cell356 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell356)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell356)).symm
    _ = normal350 := by rfl

theorem numeric170 : ForcedCoverage2.dispatch (fun _ => payload170) normal350 46 = true := by
  decide +kernel

theorem coveredLeaf170 : CovBy 9 PR (Pg cN 9 BS TS) cell356 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf170]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload170) normal350 46 numeric170
theorem normalizedLeaf171 : AdaptiveCoverage.normalize SL cell326 = normal351 := by
  calc
    AdaptiveCoverage.normalize SL cell326 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell326)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell326)).symm
    _ = normal351 := by rfl

theorem numeric171 : ForcedCoverage2.dispatch (fun _ => payload171) normal351 46 = true := by
  decide +kernel

theorem coveredLeaf171 : CovBy 9 PR (Pg cN 9 BS TS) cell326 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf171]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload171) normal351 46 numeric171
theorem normalizedLeaf172 : AdaptiveCoverage.normalize SL cell324 = normal352 := by
  calc
    AdaptiveCoverage.normalize SL cell324 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell324)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell324)).symm
    _ = normal352 := by rfl

theorem numeric172 : ForcedCoverage2.dispatch (fun _ => payload172) normal352 46 = true := by
  decide +kernel

theorem coveredLeaf172 : CovBy 9 PR (Pg cN 9 BS TS) cell324 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf172]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload172) normal352 46 numeric172
theorem normalizedLeaf173 : AdaptiveCoverage.normalize SL cell363 = normal355 := by
  calc
    AdaptiveCoverage.normalize SL cell363 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell363)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell363)).symm
    _ = normal355 := by rfl

theorem numeric173 : ForcedCoverage2.dispatch (fun _ => payload173) normal355 46 = true := by
  decide +kernel

theorem coveredLeaf173 : CovBy 9 PR (Pg cN 9 BS TS) cell363 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf173]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload173) normal355 46 numeric173
theorem normalizedLeaf174 : AdaptiveCoverage.normalize SL cell369 = normal359 := by
  calc
    AdaptiveCoverage.normalize SL cell369 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell369)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell369)).symm
    _ = normal359 := by rfl

theorem numeric174 : ForcedCoverage2.dispatch (fun _ => payload174) normal359 46 = true := by
  decide +kernel

theorem coveredLeaf174 : CovBy 9 PR (Pg cN 9 BS TS) cell369 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf174]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload174) normal359 46 numeric174
theorem normalizedLeaf175 : AdaptiveCoverage.normalize SL cell381 = normal366 := by
  calc
    AdaptiveCoverage.normalize SL cell381 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell381)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell381)).symm
    _ = normal366 := by rfl

theorem numeric175 : ForcedCoverage2.dispatch (fun _ => payload175) normal366 46 = true := by
  decide +kernel

theorem coveredLeaf175 : CovBy 9 PR (Pg cN 9 BS TS) cell381 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf175]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload175) normal366 46 numeric175
theorem normalizedLeaf176 : AdaptiveCoverage.normalize SL cell385 = normal369 := by
  calc
    AdaptiveCoverage.normalize SL cell385 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell385)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell385)).symm
    _ = normal369 := by rfl

theorem numeric176 : ForcedCoverage2.dispatch (fun _ => payload176) normal369 46 = true := by
  decide +kernel

theorem coveredLeaf176 : CovBy 9 PR (Pg cN 9 BS TS) cell385 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf176]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload176) normal369 46 numeric176
theorem normalizedLeaf177 : AdaptiveCoverage.normalize SL cell387 = normal371 := by
  calc
    AdaptiveCoverage.normalize SL cell387 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell387)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell387)).symm
    _ = normal371 := by rfl

theorem numeric177 : ForcedCoverage2.dispatch (fun _ => payload177) normal371 46 = true := by
  decide +kernel

theorem coveredLeaf177 : CovBy 9 PR (Pg cN 9 BS TS) cell387 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf177]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload177) normal371 46 numeric177
theorem normalizedLeaf178 : AdaptiveCoverage.normalize SL cell389 = normal373 := by
  calc
    AdaptiveCoverage.normalize SL cell389 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell389)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell389)).symm
    _ = normal373 := by rfl

theorem numeric178 : ForcedCoverage2.dispatch (fun _ => payload178) normal373 46 = true := by
  decide +kernel

theorem coveredLeaf178 : CovBy 9 PR (Pg cN 9 BS TS) cell389 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf178]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload178) normal373 46 numeric178
theorem normalizedLeaf179 : AdaptiveCoverage.normalize SL cell390 = normal374 := by
  calc
    AdaptiveCoverage.normalize SL cell390 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell390)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell390)).symm
    _ = normal374 := by rfl

theorem numeric179 : ForcedCoverage2.dispatch (fun _ => payload179) normal374 46 = true := by
  decide +kernel

theorem coveredLeaf179 : CovBy 9 PR (Pg cN 9 BS TS) cell390 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf179]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload179) normal374 46 numeric179
theorem normalizedLeaf180 : AdaptiveCoverage.normalize SL cell384 = normal375 := by
  calc
    AdaptiveCoverage.normalize SL cell384 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell384)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell384)).symm
    _ = normal375 := by rfl

theorem numeric180 : ForcedCoverage2.dispatch (fun _ => payload180) normal375 46 = true := by
  decide +kernel

theorem coveredLeaf180 : CovBy 9 PR (Pg cN 9 BS TS) cell384 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf180]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload180) normal375 46 numeric180
theorem normalizedLeaf181 : AdaptiveCoverage.normalize SL cell380 = normal376 := by
  calc
    AdaptiveCoverage.normalize SL cell380 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell380)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell380)).symm
    _ = normal376 := by rfl

theorem numeric181 : ForcedCoverage2.dispatch (fun _ => payload181) normal376 46 = true := by
  decide +kernel

theorem coveredLeaf181 : CovBy 9 PR (Pg cN 9 BS TS) cell380 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf181]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload181) normal376 46 numeric181
theorem normalizedLeaf182 : AdaptiveCoverage.normalize SL cell378 = normal377 := by
  calc
    AdaptiveCoverage.normalize SL cell378 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell378)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell378)).symm
    _ = normal377 := by rfl

theorem numeric182 : ForcedCoverage2.dispatch (fun _ => payload182) normal377 46 = true := by
  decide +kernel

theorem coveredLeaf182 : CovBy 9 PR (Pg cN 9 BS TS) cell378 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf182]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload182) normal377 46 numeric182
theorem normalizedLeaf183 : AdaptiveCoverage.normalize SL cell376 = normal378 := by
  calc
    AdaptiveCoverage.normalize SL cell376 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell376)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell376)).symm
    _ = normal378 := by rfl

theorem numeric183 : ForcedCoverage2.dispatch (fun _ => payload183) normal378 46 = true := by
  decide +kernel

theorem coveredLeaf183 : CovBy 9 PR (Pg cN 9 BS TS) cell376 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf183]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload183) normal378 46 numeric183
theorem normalizedLeaf184 : AdaptiveCoverage.normalize SL cell374 = normal379 := by
  calc
    AdaptiveCoverage.normalize SL cell374 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell374)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell374)).symm
    _ = normal379 := by rfl

theorem numeric184 : ForcedCoverage2.dispatch (fun _ => payload184) normal379 46 = true := by
  decide +kernel

theorem coveredLeaf184 : CovBy 9 PR (Pg cN 9 BS TS) cell374 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf184]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload184) normal379 46 numeric184
theorem normalizedLeaf185 : AdaptiveCoverage.normalize SL cell397 = normal384 := by
  calc
    AdaptiveCoverage.normalize SL cell397 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell397)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell397)).symm
    _ = normal384 := by rfl

theorem numeric185 : ForcedCoverage2.dispatch (fun _ => payload185) normal384 46 = true := by
  decide +kernel

theorem coveredLeaf185 : CovBy 9 PR (Pg cN 9 BS TS) cell397 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf185]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload185) normal384 46 numeric185
theorem normalizedLeaf186 : AdaptiveCoverage.normalize SL cell401 = normal387 := by
  calc
    AdaptiveCoverage.normalize SL cell401 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell401)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell401)).symm
    _ = normal387 := by rfl

theorem numeric186 : ForcedCoverage2.dispatch (fun _ => payload186) normal387 46 = true := by
  decide +kernel

theorem coveredLeaf186 : CovBy 9 PR (Pg cN 9 BS TS) cell401 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf186]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload186) normal387 46 numeric186
theorem normalizedLeaf187 : AdaptiveCoverage.normalize SL cell402 = normal388 := by
  calc
    AdaptiveCoverage.normalize SL cell402 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell402)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell402)).symm
    _ = normal388 := by rfl

theorem numeric187 : ForcedCoverage2.dispatch (fun _ => payload187) normal388 46 = true := by
  decide +kernel

theorem coveredLeaf187 : CovBy 9 PR (Pg cN 9 BS TS) cell402 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf187]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload187) normal388 46 numeric187
theorem normalizedLeaf188 : AdaptiveCoverage.normalize SL cell400 = normal389 := by
  calc
    AdaptiveCoverage.normalize SL cell400 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell400)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell400)).symm
    _ = normal389 := by rfl

theorem numeric188 : ForcedCoverage2.dispatch (fun _ => payload188) normal389 46 = true := by
  decide +kernel

theorem coveredLeaf188 : CovBy 9 PR (Pg cN 9 BS TS) cell400 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf188]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload188) normal389 46 numeric188
theorem normalizedLeaf189 : AdaptiveCoverage.normalize SL cell396 = normal390 := by
  calc
    AdaptiveCoverage.normalize SL cell396 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell396)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell396)).symm
    _ = normal390 := by rfl

theorem numeric189 : ForcedCoverage2.dispatch (fun _ => payload189) normal390 46 = true := by
  decide +kernel

theorem coveredLeaf189 : CovBy 9 PR (Pg cN 9 BS TS) cell396 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf189]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload189) normal390 46 numeric189
theorem normalizedLeaf190 : AdaptiveCoverage.normalize SL cell394 = normal391 := by
  calc
    AdaptiveCoverage.normalize SL cell394 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell394)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell394)).symm
    _ = normal391 := by rfl

theorem numeric190 : ForcedCoverage2.dispatch (fun _ => payload190) normal391 46 = true := by
  decide +kernel

theorem coveredLeaf190 : CovBy 9 PR (Pg cN 9 BS TS) cell394 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf190]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload190) normal391 46 numeric190
theorem normalizedLeaf191 : AdaptiveCoverage.normalize SL cell392 = normal392 := by
  calc
    AdaptiveCoverage.normalize SL cell392 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell392)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell392)).symm
    _ = normal392 := by rfl

theorem numeric191 : ForcedCoverage2.dispatch (fun _ => payload191) normal392 46 = true := by
  decide +kernel

theorem coveredLeaf191 : CovBy 9 PR (Pg cN 9 BS TS) cell392 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf191]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload191) normal392 46 numeric191

set_option pp.fullNames true
#print axioms normalizedLeaf160
#print axioms numeric160
#print axioms coveredLeaf160
#print axioms normalizedLeaf161
#print axioms numeric161
#print axioms coveredLeaf161
#print axioms normalizedLeaf162
#print axioms numeric162
#print axioms coveredLeaf162
#print axioms normalizedLeaf163
#print axioms numeric163
#print axioms coveredLeaf163
#print axioms normalizedLeaf164
#print axioms numeric164
#print axioms coveredLeaf164
#print axioms normalizedLeaf165
#print axioms numeric165
#print axioms coveredLeaf165
#print axioms normalizedLeaf166
#print axioms numeric166
#print axioms coveredLeaf166
#print axioms normalizedLeaf167
#print axioms numeric167
#print axioms coveredLeaf167
#print axioms normalizedLeaf168
#print axioms numeric168
#print axioms coveredLeaf168
#print axioms normalizedLeaf169
#print axioms numeric169
#print axioms coveredLeaf169
#print axioms normalizedLeaf170
#print axioms numeric170
#print axioms coveredLeaf170
#print axioms normalizedLeaf171
#print axioms numeric171
#print axioms coveredLeaf171
#print axioms normalizedLeaf172
#print axioms numeric172
#print axioms coveredLeaf172
#print axioms normalizedLeaf173
#print axioms numeric173
#print axioms coveredLeaf173
#print axioms normalizedLeaf174
#print axioms numeric174
#print axioms coveredLeaf174
#print axioms normalizedLeaf175
#print axioms numeric175
#print axioms coveredLeaf175
#print axioms normalizedLeaf176
#print axioms numeric176
#print axioms coveredLeaf176
#print axioms normalizedLeaf177
#print axioms numeric177
#print axioms coveredLeaf177
#print axioms normalizedLeaf178
#print axioms numeric178
#print axioms coveredLeaf178
#print axioms normalizedLeaf179
#print axioms numeric179
#print axioms coveredLeaf179
#print axioms normalizedLeaf180
#print axioms numeric180
#print axioms coveredLeaf180
#print axioms normalizedLeaf181
#print axioms numeric181
#print axioms coveredLeaf181
#print axioms normalizedLeaf182
#print axioms numeric182
#print axioms coveredLeaf182
#print axioms normalizedLeaf183
#print axioms numeric183
#print axioms coveredLeaf183
#print axioms normalizedLeaf184
#print axioms numeric184
#print axioms coveredLeaf184
#print axioms normalizedLeaf185
#print axioms numeric185
#print axioms coveredLeaf185
#print axioms normalizedLeaf186
#print axioms numeric186
#print axioms coveredLeaf186
#print axioms normalizedLeaf187
#print axioms numeric187
#print axioms coveredLeaf187
#print axioms normalizedLeaf188
#print axioms numeric188
#print axioms coveredLeaf188
#print axioms normalizedLeaf189
#print axioms numeric189
#print axioms coveredLeaf189
#print axioms normalizedLeaf190
#print axioms numeric190
#print axioms coveredLeaf190
#print axioms normalizedLeaf191
#print axioms numeric191
#print axioms coveredLeaf191
end StructuralGoal20261016.W10Aux478
end
