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
theorem normalizedLeaf192 : AdaptiveCoverage.normalize SL cell403 = normal394 := by
  calc
    AdaptiveCoverage.normalize SL cell403 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell403)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell403)).symm
    _ = normal394 := by rfl

theorem numeric192 : ForcedCoverage2.dispatch (fun _ => payload192) normal394 46 = true := by
  decide +kernel

theorem coveredLeaf192 : CovBy 9 PR (Pg cN 9 BS TS) cell403 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf192]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload192) normal394 46 numeric192
theorem normalizedLeaf193 : AdaptiveCoverage.normalize SL cell405 = normal396 := by
  calc
    AdaptiveCoverage.normalize SL cell405 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell405)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell405)).symm
    _ = normal396 := by rfl

theorem numeric193 : ForcedCoverage2.dispatch (fun _ => payload193) normal396 46 = true := by
  decide +kernel

theorem coveredLeaf193 : CovBy 9 PR (Pg cN 9 BS TS) cell405 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf193]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload193) normal396 46 numeric193
theorem normalizedLeaf194 : AdaptiveCoverage.normalize SL cell407 = normal398 := by
  calc
    AdaptiveCoverage.normalize SL cell407 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell407)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell407)).symm
    _ = normal398 := by rfl

theorem numeric194 : ForcedCoverage2.dispatch (fun _ => payload194) normal398 46 = true := by
  decide +kernel

theorem coveredLeaf194 : CovBy 9 PR (Pg cN 9 BS TS) cell407 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf194]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload194) normal398 46 numeric194
theorem normalizedLeaf195 : AdaptiveCoverage.normalize SL cell409 = normal400 := by
  calc
    AdaptiveCoverage.normalize SL cell409 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell409)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell409)).symm
    _ = normal400 := by rfl

theorem numeric195 : ForcedCoverage2.dispatch (fun _ => payload195) normal400 46 = true := by
  decide +kernel

theorem coveredLeaf195 : CovBy 9 PR (Pg cN 9 BS TS) cell409 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf195]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload195) normal400 46 numeric195
theorem normalizedLeaf196 : AdaptiveCoverage.normalize SL cell410 = normal401 := by
  calc
    AdaptiveCoverage.normalize SL cell410 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell410)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell410)).symm
    _ = normal401 := by rfl

theorem numeric196 : ForcedCoverage2.dispatch (fun _ => payload196) normal401 46 = true := by
  decide +kernel

theorem coveredLeaf196 : CovBy 9 PR (Pg cN 9 BS TS) cell410 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf196]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload196) normal401 46 numeric196
theorem normalizedLeaf197 : AdaptiveCoverage.normalize SL cell413 = normal404 := by
  calc
    AdaptiveCoverage.normalize SL cell413 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell413)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell413)).symm
    _ = normal404 := by rfl

theorem numeric197 : ForcedCoverage2.dispatch (fun _ => payload197) normal404 46 = true := by
  decide +kernel

theorem coveredLeaf197 : CovBy 9 PR (Pg cN 9 BS TS) cell413 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf197]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload197) normal404 46 numeric197
theorem normalizedLeaf198 : AdaptiveCoverage.normalize SL cell425 = normal411 := by
  calc
    AdaptiveCoverage.normalize SL cell425 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell425)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell425)).symm
    _ = normal411 := by rfl

theorem numeric198 : ForcedCoverage2.dispatch (fun _ => payload198) normal411 46 = true := by
  decide +kernel

theorem coveredLeaf198 : CovBy 9 PR (Pg cN 9 BS TS) cell425 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf198]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload198) normal411 46 numeric198
theorem normalizedLeaf199 : AdaptiveCoverage.normalize SL cell427 = normal413 := by
  calc
    AdaptiveCoverage.normalize SL cell427 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell427)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell427)).symm
    _ = normal413 := by rfl

theorem numeric199 : ForcedCoverage2.dispatch (fun _ => payload199) normal413 46 = true := by
  decide +kernel

theorem coveredLeaf199 : CovBy 9 PR (Pg cN 9 BS TS) cell427 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf199]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload199) normal413 46 numeric199
theorem normalizedLeaf200 : AdaptiveCoverage.normalize SL cell428 = normal414 := by
  calc
    AdaptiveCoverage.normalize SL cell428 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell428)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell428)).symm
    _ = normal414 := by rfl

theorem numeric200 : ForcedCoverage2.dispatch (fun _ => payload200) normal414 46 = true := by
  decide +kernel

theorem coveredLeaf200 : CovBy 9 PR (Pg cN 9 BS TS) cell428 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf200]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload200) normal414 46 numeric200
theorem normalizedLeaf201 : AdaptiveCoverage.normalize SL cell424 = normal415 := by
  calc
    AdaptiveCoverage.normalize SL cell424 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell424)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell424)).symm
    _ = normal415 := by rfl

theorem numeric201 : ForcedCoverage2.dispatch (fun _ => payload201) normal415 46 = true := by
  decide +kernel

theorem coveredLeaf201 : CovBy 9 PR (Pg cN 9 BS TS) cell424 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf201]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload201) normal415 46 numeric201
theorem normalizedLeaf202 : AdaptiveCoverage.normalize SL cell422 = normal416 := by
  calc
    AdaptiveCoverage.normalize SL cell422 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell422)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell422)).symm
    _ = normal416 := by rfl

theorem numeric202 : ForcedCoverage2.dispatch (fun _ => payload202) normal416 46 = true := by
  decide +kernel

theorem coveredLeaf202 : CovBy 9 PR (Pg cN 9 BS TS) cell422 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf202]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload202) normal416 46 numeric202
theorem normalizedLeaf203 : AdaptiveCoverage.normalize SL cell420 = normal417 := by
  calc
    AdaptiveCoverage.normalize SL cell420 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell420)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell420)).symm
    _ = normal417 := by rfl

theorem numeric203 : ForcedCoverage2.dispatch (fun _ => payload203) normal417 46 = true := by
  decide +kernel

theorem coveredLeaf203 : CovBy 9 PR (Pg cN 9 BS TS) cell420 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf203]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload203) normal417 46 numeric203
theorem normalizedLeaf204 : AdaptiveCoverage.normalize SL cell431 = normal420 := by
  calc
    AdaptiveCoverage.normalize SL cell431 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell431)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell431)).symm
    _ = normal420 := by rfl

theorem numeric204 : ForcedCoverage2.dispatch (fun _ => payload204) normal420 46 = true := by
  decide +kernel

theorem coveredLeaf204 : CovBy 9 PR (Pg cN 9 BS TS) cell431 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf204]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload204) normal420 46 numeric204
theorem normalizedLeaf205 : AdaptiveCoverage.normalize SL cell432 = normal421 := by
  calc
    AdaptiveCoverage.normalize SL cell432 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell432)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell432)).symm
    _ = normal421 := by rfl

theorem numeric205 : ForcedCoverage2.dispatch (fun _ => payload205) normal421 46 = true := by
  decide +kernel

theorem coveredLeaf205 : CovBy 9 PR (Pg cN 9 BS TS) cell432 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf205]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload205) normal421 46 numeric205
theorem normalizedLeaf206 : AdaptiveCoverage.normalize SL cell430 = normal422 := by
  calc
    AdaptiveCoverage.normalize SL cell430 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell430)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell430)).symm
    _ = normal422 := by rfl

theorem numeric206 : ForcedCoverage2.dispatch (fun _ => payload206) normal422 46 = true := by
  decide +kernel

theorem coveredLeaf206 : CovBy 9 PR (Pg cN 9 BS TS) cell430 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf206]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload206) normal422 46 numeric206
theorem normalizedLeaf207 : AdaptiveCoverage.normalize SL cell443 = normal429 := by
  calc
    AdaptiveCoverage.normalize SL cell443 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell443)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell443)).symm
    _ = normal429 := by rfl

theorem numeric207 : ForcedCoverage2.dispatch (fun _ => payload207) normal429 46 = true := by
  decide +kernel

theorem coveredLeaf207 : CovBy 9 PR (Pg cN 9 BS TS) cell443 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf207]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload207) normal429 46 numeric207
theorem normalizedLeaf208 : AdaptiveCoverage.normalize SL cell445 = normal431 := by
  calc
    AdaptiveCoverage.normalize SL cell445 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell445)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell445)).symm
    _ = normal431 := by rfl

theorem numeric208 : ForcedCoverage2.dispatch (fun _ => payload208) normal431 46 = true := by
  decide +kernel

theorem coveredLeaf208 : CovBy 9 PR (Pg cN 9 BS TS) cell445 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf208]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload208) normal431 46 numeric208
theorem normalizedLeaf209 : AdaptiveCoverage.normalize SL cell447 = normal433 := by
  calc
    AdaptiveCoverage.normalize SL cell447 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell447)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell447)).symm
    _ = normal433 := by rfl

theorem numeric209 : ForcedCoverage2.dispatch (fun _ => payload209) normal433 46 = true := by
  decide +kernel

theorem coveredLeaf209 : CovBy 9 PR (Pg cN 9 BS TS) cell447 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf209]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload209) normal433 46 numeric209
theorem normalizedLeaf210 : AdaptiveCoverage.normalize SL cell448 = normal434 := by
  calc
    AdaptiveCoverage.normalize SL cell448 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell448)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell448)).symm
    _ = normal434 := by rfl

theorem numeric210 : ForcedCoverage2.dispatch (fun _ => payload210) normal434 46 = true := by
  decide +kernel

theorem coveredLeaf210 : CovBy 9 PR (Pg cN 9 BS TS) cell448 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf210]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload210) normal434 46 numeric210
theorem normalizedLeaf211 : AdaptiveCoverage.normalize SL cell442 = normal435 := by
  calc
    AdaptiveCoverage.normalize SL cell442 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell442)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell442)).symm
    _ = normal435 := by rfl

theorem numeric211 : ForcedCoverage2.dispatch (fun _ => payload211) normal435 46 = true := by
  decide +kernel

theorem coveredLeaf211 : CovBy 9 PR (Pg cN 9 BS TS) cell442 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf211]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload211) normal435 46 numeric211
theorem normalizedLeaf212 : AdaptiveCoverage.normalize SL cell451 = normal438 := by
  calc
    AdaptiveCoverage.normalize SL cell451 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell451)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell451)).symm
    _ = normal438 := by rfl

theorem numeric212 : ForcedCoverage2.dispatch (fun _ => payload212) normal438 46 = true := by
  decide +kernel

theorem coveredLeaf212 : CovBy 9 PR (Pg cN 9 BS TS) cell451 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf212]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload212) normal438 46 numeric212
theorem normalizedLeaf213 : AdaptiveCoverage.normalize SL cell453 = normal440 := by
  calc
    AdaptiveCoverage.normalize SL cell453 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell453)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell453)).symm
    _ = normal440 := by rfl

theorem numeric213 : ForcedCoverage2.dispatch (fun _ => payload213) normal440 46 = true := by
  decide +kernel

theorem coveredLeaf213 : CovBy 9 PR (Pg cN 9 BS TS) cell453 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf213]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload213) normal440 46 numeric213
theorem normalizedLeaf214 : AdaptiveCoverage.normalize SL cell455 = normal442 := by
  calc
    AdaptiveCoverage.normalize SL cell455 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell455)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell455)).symm
    _ = normal442 := by rfl

theorem numeric214 : ForcedCoverage2.dispatch (fun _ => payload214) normal442 46 = true := by
  decide +kernel

theorem coveredLeaf214 : CovBy 9 PR (Pg cN 9 BS TS) cell455 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf214]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload214) normal442 46 numeric214
theorem normalizedLeaf215 : AdaptiveCoverage.normalize SL cell457 = normal444 := by
  calc
    AdaptiveCoverage.normalize SL cell457 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell457)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell457)).symm
    _ = normal444 := by rfl

theorem numeric215 : ForcedCoverage2.dispatch (fun _ => payload215) normal444 46 = true := by
  decide +kernel

theorem coveredLeaf215 : CovBy 9 PR (Pg cN 9 BS TS) cell457 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf215]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload215) normal444 46 numeric215
theorem normalizedLeaf216 : AdaptiveCoverage.normalize SL cell458 = normal445 := by
  calc
    AdaptiveCoverage.normalize SL cell458 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell458)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell458)).symm
    _ = normal445 := by rfl

theorem numeric216 : ForcedCoverage2.dispatch (fun _ => payload216) normal445 46 = true := by
  decide +kernel

theorem coveredLeaf216 : CovBy 9 PR (Pg cN 9 BS TS) cell458 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf216]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload216) normal445 46 numeric216
theorem normalizedLeaf217 : AdaptiveCoverage.normalize SL cell450 = normal446 := by
  calc
    AdaptiveCoverage.normalize SL cell450 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell450)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell450)).symm
    _ = normal446 := by rfl

theorem numeric217 : ForcedCoverage2.dispatch (fun _ => payload217) normal446 46 = true := by
  decide +kernel

theorem coveredLeaf217 : CovBy 9 PR (Pg cN 9 BS TS) cell450 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf217]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload217) normal446 46 numeric217
theorem normalizedLeaf218 : AdaptiveCoverage.normalize SL cell438 = normal447 := by
  calc
    AdaptiveCoverage.normalize SL cell438 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell438)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell438)).symm
    _ = normal447 := by rfl

theorem numeric218 : ForcedCoverage2.dispatch (fun _ => payload218) normal447 46 = true := by
  decide +kernel

theorem coveredLeaf218 : CovBy 9 PR (Pg cN 9 BS TS) cell438 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf218]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload218) normal447 46 numeric218
theorem normalizedLeaf219 : AdaptiveCoverage.normalize SL cell436 = normal448 := by
  calc
    AdaptiveCoverage.normalize SL cell436 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell436)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell436)).symm
    _ = normal448 := by rfl

theorem numeric219 : ForcedCoverage2.dispatch (fun _ => payload219) normal448 46 = true := by
  decide +kernel

theorem coveredLeaf219 : CovBy 9 PR (Pg cN 9 BS TS) cell436 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf219]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload219) normal448 46 numeric219
theorem normalizedLeaf220 : AdaptiveCoverage.normalize SL cell465 = normal453 := by
  calc
    AdaptiveCoverage.normalize SL cell465 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell465)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell465)).symm
    _ = normal453 := by rfl

theorem numeric220 : ForcedCoverage2.dispatch (fun _ => payload220) normal453 46 = true := by
  decide +kernel

theorem coveredLeaf220 : CovBy 9 PR (Pg cN 9 BS TS) cell465 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf220]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload220) normal453 46 numeric220
theorem normalizedLeaf221 : AdaptiveCoverage.normalize SL cell467 = normal455 := by
  calc
    AdaptiveCoverage.normalize SL cell467 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell467)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell467)).symm
    _ = normal455 := by rfl

theorem numeric221 : ForcedCoverage2.dispatch (fun _ => payload221) normal455 46 = true := by
  decide +kernel

theorem coveredLeaf221 : CovBy 9 PR (Pg cN 9 BS TS) cell467 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf221]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload221) normal455 46 numeric221
theorem normalizedLeaf222 : AdaptiveCoverage.normalize SL cell468 = normal456 := by
  calc
    AdaptiveCoverage.normalize SL cell468 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell468)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell468)).symm
    _ = normal456 := by rfl

theorem numeric222 : ForcedCoverage2.dispatch (fun _ => payload222) normal456 46 = true := by
  decide +kernel

theorem coveredLeaf222 : CovBy 9 PR (Pg cN 9 BS TS) cell468 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf222]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload222) normal456 46 numeric222
theorem normalizedLeaf223 : AdaptiveCoverage.normalize SL cell464 = normal457 := by
  calc
    AdaptiveCoverage.normalize SL cell464 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell464)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell464)).symm
    _ = normal457 := by rfl

theorem numeric223 : ForcedCoverage2.dispatch (fun _ => payload223) normal457 46 = true := by
  decide +kernel

theorem coveredLeaf223 : CovBy 9 PR (Pg cN 9 BS TS) cell464 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf223]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload223) normal457 46 numeric223

set_option pp.fullNames true
#print axioms normalizedLeaf192
#print axioms numeric192
#print axioms coveredLeaf192
#print axioms normalizedLeaf193
#print axioms numeric193
#print axioms coveredLeaf193
#print axioms normalizedLeaf194
#print axioms numeric194
#print axioms coveredLeaf194
#print axioms normalizedLeaf195
#print axioms numeric195
#print axioms coveredLeaf195
#print axioms normalizedLeaf196
#print axioms numeric196
#print axioms coveredLeaf196
#print axioms normalizedLeaf197
#print axioms numeric197
#print axioms coveredLeaf197
#print axioms normalizedLeaf198
#print axioms numeric198
#print axioms coveredLeaf198
#print axioms normalizedLeaf199
#print axioms numeric199
#print axioms coveredLeaf199
#print axioms normalizedLeaf200
#print axioms numeric200
#print axioms coveredLeaf200
#print axioms normalizedLeaf201
#print axioms numeric201
#print axioms coveredLeaf201
#print axioms normalizedLeaf202
#print axioms numeric202
#print axioms coveredLeaf202
#print axioms normalizedLeaf203
#print axioms numeric203
#print axioms coveredLeaf203
#print axioms normalizedLeaf204
#print axioms numeric204
#print axioms coveredLeaf204
#print axioms normalizedLeaf205
#print axioms numeric205
#print axioms coveredLeaf205
#print axioms normalizedLeaf206
#print axioms numeric206
#print axioms coveredLeaf206
#print axioms normalizedLeaf207
#print axioms numeric207
#print axioms coveredLeaf207
#print axioms normalizedLeaf208
#print axioms numeric208
#print axioms coveredLeaf208
#print axioms normalizedLeaf209
#print axioms numeric209
#print axioms coveredLeaf209
#print axioms normalizedLeaf210
#print axioms numeric210
#print axioms coveredLeaf210
#print axioms normalizedLeaf211
#print axioms numeric211
#print axioms coveredLeaf211
#print axioms normalizedLeaf212
#print axioms numeric212
#print axioms coveredLeaf212
#print axioms normalizedLeaf213
#print axioms numeric213
#print axioms coveredLeaf213
#print axioms normalizedLeaf214
#print axioms numeric214
#print axioms coveredLeaf214
#print axioms normalizedLeaf215
#print axioms numeric215
#print axioms coveredLeaf215
#print axioms normalizedLeaf216
#print axioms numeric216
#print axioms coveredLeaf216
#print axioms normalizedLeaf217
#print axioms numeric217
#print axioms coveredLeaf217
#print axioms normalizedLeaf218
#print axioms numeric218
#print axioms coveredLeaf218
#print axioms normalizedLeaf219
#print axioms numeric219
#print axioms coveredLeaf219
#print axioms normalizedLeaf220
#print axioms numeric220
#print axioms coveredLeaf220
#print axioms normalizedLeaf221
#print axioms numeric221
#print axioms coveredLeaf221
#print axioms normalizedLeaf222
#print axioms numeric222
#print axioms coveredLeaf222
#print axioms normalizedLeaf223
#print axioms numeric223
#print axioms coveredLeaf223
end StructuralGoal20261016.W10Aux478
end
