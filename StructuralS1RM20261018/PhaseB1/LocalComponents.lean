import StructuralS1RM20261018.PhaseB1.LocalGeometry
import StructuralS1RM20261018.PhaseB1.LocalData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open AMW.Cert AMW.Cert.PCell AMW.Cert.Pyr AMW.Cert.PyrD
open StructuralS1RM20261018
open StructuralS1RM20261018.LocalGeometry
namespace StructuralS1RM20261018.LocalComponents
-- Actual variables, not epigraph existential witnesses. No gauge X0=0.
def actualZ (P : ℕ → ℝ) (j : Fin 78) : ℝ :=
  match j.val with
  | 0 => (20 * 32768 * P 0)
  | 1 => (20 * 32768 * P 1)
  | 2 => (20 * 32768 * P 2)
  | 3 => (20 * 32768 * P 3)
  | 4 => (20 * 32768 * P 4)
  | 5 => (20 * 32768 * P 5)
  | 6 => (20 * 32768 * P 6)
  | 7 => (20 * 32768 * P 7)
  | 8 => (20 * 32768 * P 8)
  | 9 => (20 * 32768 * P 9)
  | 10 => ((QuantizedComponent.kappa : ℝ) * wfun (P 1-P 0))
  | 11 => ((QuantizedComponent.kappa : ℝ) * wfun (P 3-P 0))
  | 12 => ((QuantizedComponent.kappa : ℝ) * wfun (P 4-P 0))
  | 13 => ((QuantizedComponent.kappa : ℝ) * wfun (P 5-P 0))
  | 14 => ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 0))
  | 15 => ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 0))
  | 16 => ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 0))
  | 17 => ((QuantizedComponent.kappa : ℝ) * wfun (P 2-P 1))
  | 18 => ((QuantizedComponent.kappa : ℝ) * wfun (P 3-P 1))
  | 19 => ((QuantizedComponent.kappa : ℝ) * wfun (P 4-P 1))
  | 20 => ((QuantizedComponent.kappa : ℝ) * wfun (P 5-P 1))
  | 21 => ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 1))
  | 22 => ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 1))
  | 23 => ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 1))
  | 24 => ((QuantizedComponent.kappa : ℝ) * wfun (P 3-P 2))
  | 25 => ((QuantizedComponent.kappa : ℝ) * wfun (P 4-P 2))
  | 26 => ((QuantizedComponent.kappa : ℝ) * wfun (P 5-P 2))
  | 27 => ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 2))
  | 28 => ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 2))
  | 29 => ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 2))
  | 30 => ((QuantizedComponent.kappa : ℝ) * wfun (P 4-P 3))
  | 31 => ((QuantizedComponent.kappa : ℝ) * wfun (P 5-P 3))
  | 32 => ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 3))
  | 33 => ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 3))
  | 34 => ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 3))
  | 35 => ((QuantizedComponent.kappa : ℝ) * wfun (P 5-P 4))
  | 36 => ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 4))
  | 37 => ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 4))
  | 38 => ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 4))
  | 39 => ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 5))
  | 40 => ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 5))
  | 41 => ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 5))
  | 42 => ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 6))
  | 43 => ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 7))
  | 44 => ((QuantizedComponent.kappa : ℝ) * wfun (P 9-P 8))
  | 45 => ((QuantizedComponent.kappa : ℝ) * wfun (P 9-P 6))
  | 46 => ((QuantizedComponent.kappa : ℝ) * wfun (P 9-P 5))
  | 47 => ((QuantizedComponent.kappa : ℝ) * wfun (P 9-P 4))
  | 48 => ((QuantizedComponent.kappa : ℝ) * wfun (P 9-P 3))
  | 49 => ((QuantizedComponent.kappa : ℝ) * wfun (P 9-P 2))
  | 50 => ((QuantizedComponent.kappa : ℝ) * wfun (P 9-P 1))
  | 51 => ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 7))
  | 52 => ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 6))
  | 53 => ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 5))
  | 54 => ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 4))
  | 55 => ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 3))
  | 56 => ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 2))
  | 57 => ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 1))
  | 58 => ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 6))
  | 59 => ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 5))
  | 60 => ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 4))
  | 61 => ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 3))
  | 62 => ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 2))
  | 63 => ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 1))
  | 64 => ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 5))
  | 65 => ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 4))
  | 66 => ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 3))
  | 67 => ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 2))
  | 68 => ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 1))
  | 69 => ((QuantizedComponent.kappa : ℝ) * wfun (P 5-P 4))
  | 70 => ((QuantizedComponent.kappa : ℝ) * wfun (P 5-P 3))
  | 71 => ((QuantizedComponent.kappa : ℝ) * wfun (P 5-P 2))
  | 72 => ((QuantizedComponent.kappa : ℝ) * wfun (P 5-P 1))
  | 73 => ((QuantizedComponent.kappa : ℝ) * wfun (P 4-P 3))
  | 74 => ((QuantizedComponent.kappa : ℝ) * wfun (P 4-P 2))
  | 75 => ((QuantizedComponent.kappa : ℝ) * wfun (P 4-P 1))
  | 76 => ((QuantizedComponent.kappa : ℝ) * wfun (P 3-P 2))
  | _ => ((QuantizedComponent.kappa : ℝ) * wfun (P 2-P 1))

theorem pointWord33248 : AMW.Cert.PC9QB6MData.PT 33248 = 339565915100054711931765125185936107842395 := by decide +kernel

theorem pointWord33536 : AMW.Cert.PC9QB6MData.PT 33536 = 361300122059133552910688810484506591837074 := by decide +kernel

theorem pointWord33696 : AMW.Cert.PC9QB6MData.PT 33696 = 358269482228743773916014259622667495349662 := by decide +kernel

theorem pointWord33728 : AMW.Cert.PC9QB6MData.PT 33728 = 359649220888368482957217612384151877577289 := by decide +kernel

theorem pointWord33792 : AMW.Cert.PC9QB6MData.PT 33792 = 372209096220540086297383097985056740758370 := by decide +kernel

theorem pointWord33888 : AMW.Cert.PC9QB6MData.PT 33888 = 366137182735794491793864297798744397050618 := by decide +kernel

theorem pointWord33984 : AMW.Cert.PC9QB6MData.PT 33984 = 370644594869501044306569003572935576908434 := by decide +kernel

theorem pointWord34048 : AMW.Cert.PC9QB6MData.PT 34048 = 379755123552610793771964976702740168479888 := by decide +kernel

theorem pointWord34784 : AMW.Cert.PC9QB6MData.PT 34784 = 403647996776843972155080242767480024584160 := by decide +kernel

theorem pointWord67264 : AMW.Cert.PC9QB6MData.PT 67264 = 126927985438670607219777208160542359814999 := by decide +kernel

theorem pointWord67552 : AMW.Cert.PC9QB6MData.PT 67552 = 123137027194691976168546243925870182019226 := by decide +kernel

theorem pointWord67584 : AMW.Cert.PC9QB6MData.PT 67584 = 123137025142365648837312612486071690897588 := by decide +kernel

theorem pointWord100320 : AMW.Cert.PC9QB6MData.PT 100320 = 159592436616892853614108495736058564663220 := by decide +kernel

theorem pointWord101024 : AMW.Cert.PC9QB6MData.PT 101024 = 157125389054236938990241405003390946780415 := by decide +kernel

theorem pointWord101120 : AMW.Cert.PC9QB6MData.PT 101120 = 157508202657371941690715231695739545258956 := by decide +kernel

theorem pointWord101152 : AMW.Cert.PC9QB6MData.PT 101152 = 156688072756500832947958550065273496275819 := by decide +kernel

theorem pointWord101632 : AMW.Cert.PC9QB6MData.PT 101632 = 155366818408488734276541672521747632412713 := by decide +kernel

theorem pointWord131424 : AMW.Cert.PC9QB6MData.PT 131424 = 207980324884319095326514273199865678860940 := by decide +kernel

theorem pointWord132096 : AMW.Cert.PC9QB6MData.PT 132096 = 205389659244344892351405529205813612551630 := by decide +kernel

theorem pointWord134240 : AMW.Cert.PC9QB6MData.PT 134240 = 194842236098680885811352896025909492265936 := by decide +kernel

theorem pointWord134336 : AMW.Cert.PC9QB6MData.PT 134336 = 196204694436803724276401587409941356360766 := by decide +kernel

theorem pointWord134368 : AMW.Cert.PC9QB6MData.PT 134368 = 196002652079579991657398348719873920153685 := by decide +kernel

theorem pointWord135168 : AMW.Cert.PC9QB6MData.PT 135168 = 193163420310010281058036928578916183242874 := by decide +kernel

theorem pointWord165824 : AMW.Cert.PC9QB6MData.PT 165824 = 245194723761013534045442504319762839487466 := by decide +kernel

theorem pointWord166112 : AMW.Cert.PC9QB6MData.PT 166112 = 243990443311634000896289444778298538016627 := by decide +kernel

theorem pointWord168064 : AMW.Cert.PC9QB6MData.PT 168064 = 236581327188541896679860458441787294399684 := by decide +kernel

theorem pointWord168288 : AMW.Cert.PC9QB6MData.PT 168288 = 236241044821620954671098894389501446452150 := by decide +kernel

theorem pointWord168512 : AMW.Cert.PC9QB6MData.PT 168512 = 233219709587201837562627937573192972590189 := by decide +kernel

theorem pointWord201984 : AMW.Cert.PC9QB6MData.PT 201984 = 271626425366216993425149245789713631137527 := by decide +kernel

theorem pointWord227520 : AMW.Cert.PC9QB6MData.PT 227520 = 337251743245525014087874280793455699570223 := by decide +kernel

theorem pointWord228960 : AMW.Cert.PC9QB6MData.PT 228960 = 340962947389451075693529383144799642599108 := by decide +kernel

theorem pointWord233472 : AMW.Cert.PC9QB6MData.PT 233472 = 319565034249480789618767603983540946487905 := by decide +kernel

theorem pointWord262016 : AMW.Cert.PC9QB6MData.PT 262016 = 380733452503987396867710295857621821821913 := by decide +kernel

theorem rowSound0 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row0 (actualZ P) ≤ (LocalData.row0.rhs : ℝ) := by
  have hv := (h.left.2 21 (by decide)).1
  norm_num [AMW.Cert.PC9QB6M.PR, pI, pJ, leftCell] at hv
  rw [canonical_span P false 3 8 (by decide) (by decide)] at hv
  norm_num [SC] at hv
  change (1 : ℝ) * (20 * 32768 * P 3) + (-1 : ℝ) * (20 * 32768 * P 8) + 0 ≤ (-4078080 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound1 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row1 (actualZ P) ≤ (LocalData.row1.rhs : ℝ) := by
  have hv := h.orderedRight
  change (1 : ℝ) * (20 * 32768 * P 1) + (-1 : ℝ) * (20 * 32768 * P 2) + (-1 : ℝ) * (20 * 32768 * P 8) + (1 : ℝ) * (20 * 32768 * P 9) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound2 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row2 (actualZ P) ≤ (LocalData.row2.rhs : ℝ) := by
  have hr := range0 P h
  have hUc : (75995 : ℝ)/SC ≤ (75995 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 26112 75995 (P 1-P 0) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 26112 75995 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 1-P 0)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound3 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row3 (actualZ P) ≤ (LocalData.row3.rhs : ℝ) := by
  have hr := range0 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 33888) 26112 75995 33888 = true := by
    rw [pointWord33888]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 26112 ≤ 26112 by decide) (P 1-P 0) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 33888 = (-26551708672 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord33888, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 26112 33888 = (18259456511967232 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord33888, trip, lo32, hi32]
  rw [hs, he] at hv
  change (26551708672 : ℝ) * (20 * 32768 * P 0) + (-26551708672 : ℝ) * (20 * 32768 * P 1) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 1-P 0)) + 0 ≤ (-18259456511967232 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound4 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row4 (actualZ P) ≤ (LocalData.row4.rhs : ℝ) := by
  have hr := range1 P h
  have hUc : (133724 : ℝ)/SC ≤ (133724 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 83841 133724 (P 3-P 0) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 83841 133724 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 3-P 0)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound5 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row5 (actualZ P) ≤ (LocalData.row5.rhs : ℝ) := by
  have hr := range2 P h
  have hUc : (163390 : ℝ)/SC ≤ (163390 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 113507 163390 (P 4-P 0) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 113507 163390 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 4-P 0)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound6 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row6 (actualZ P) ≤ (LocalData.row6.rhs : ℝ) := by
  have hr := range3 P h
  have hUc : (193056 : ℝ)/SC ≤ (193056 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 143173 193056 (P 5-P 0) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 143173 193056 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 5-P 0)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound7 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row7 (actualZ P) ≤ (LocalData.row7.rhs : ℝ) := by
  have hr := range4 P h
  have hUc : (222240 : ℝ)/SC ≤ (222240 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 172357 222240 (P 6-P 0) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 172357 222240 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 0)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound8 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row8 (actualZ P) ≤ (LocalData.row8.rhs : ℝ) := by
  have hr := range5 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 228960) 200902 250785 228960 = true := by
    rw [pointWord228960]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 200902 ≤ 200902 by decide) (P 7-P 0) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 228960 = (148639232 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord228960, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 200902 228960 = (-680109905874944 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord228960, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-148639232 : ℝ) * (20 * 32768 * P 0) + (148639232 : ℝ) * (20 * 32768 * P 7) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 0)) + 0 ≤ (680109905874944 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound9 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row9 (actualZ P) ≤ (LocalData.row9.rhs : ℝ) := by
  have hr := range6 P h
  have hUc : (347550 : ℝ)/SC ≤ (347550 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 287745 347550 (P 8-P 0) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 287745 347550 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 0)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound10 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row10 (actualZ P) ≤ (LocalData.row10.rhs : ℝ) := by
  have hr := range7 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 34048) 28545 39936 34048 = true := by
    rw [pointWord34048]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 28545 ≤ 28545 by decide) (P 2-P 1) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 34048 = (-22079180800 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord34048, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 28545 34048 = (15221032715087872 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord34048, trip, lo32, hi32]
  rw [hs, he] at hv
  change (22079180800 : ℝ) * (20 * 32768 * P 1) + (-22079180800 : ℝ) * (20 * 32768 * P 2) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 2-P 1)) + 0 ≤ (-15221032715087872 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound11 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row11 (actualZ P) ≤ (LocalData.row11.rhs : ℝ) := by
  have hr := range8 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 67552) 57729 78725 67552 = true := by
    rw [pointWord67552]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 57729 ≤ 57729 by decide) (P 3-P 1) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 67552 = (1534761472 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord67552, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 57729 67552 = (-2068708809551872 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord67552, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-1534761472 : ℝ) * (20 * 32768 * P 1) + (1534761472 : ℝ) * (20 * 32768 * P 3) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 3-P 1)) + 0 ≤ (2068708809551872 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound12 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row12 (actualZ P) ≤ (LocalData.row12.rhs : ℝ) := by
  have hr := range9 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 101152) 87395 108391 101152 = true := by
    rw [pointWord101152]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 87395 ≤ 87395 by decide) (P 4-P 1) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 101152 = (3457619968 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord101152, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 87395 101152 = (-6928834863663104 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord101152, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-3457619968 : ℝ) * (20 * 32768 * P 1) + (3457619968 : ℝ) * (20 * 32768 * P 4) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 4-P 1)) + 0 ≤ (6928834863663104 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound13 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row13 (actualZ P) ≤ (LocalData.row13.rhs : ℝ) := by
  have hr := range10 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 134368) 117061 142272 134368 = true := by
    rw [pointWord134368]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 117061 ≤ 117061 by decide) (P 5-P 1) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 134368 = (3504015360 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord134368, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 117061 134368 = (-9290722681042944 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord134368, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-3504015360 : ℝ) * (20 * 32768 * P 1) + (3504015360 : ℝ) * (20 * 32768 * P 5) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 5-P 1)) + 0 ≤ (9290722681042944 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound14 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row14 (actualZ P) ≤ (LocalData.row14.rhs : ℝ) := by
  have hr := range11 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 168288) 146245 171456 168288 = true := by
    rw [pointWord168288]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 146245 ≤ 146245 by decide) (P 6-P 1) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 168288 = (2608332288 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord168288, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 146245 168288 = (-8660379013822464 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord168288, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-2608332288 : ℝ) * (20 * 32768 * P 1) + (2608332288 : ℝ) * (20 * 32768 * P 6) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 1)) + 0 ≤ (8660379013822464 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound15 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row15 (actualZ P) ≤ (LocalData.row15.rhs : ℝ) := by
  have hr := range12 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 201984) 174790 203904 201984 = true := by
    rw [pointWord201984]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 174790 ≤ 174790 by decide) (P 7-P 1) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 201984 = (2227275264 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord201984, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 174790 201984 = (-8852765569327104 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord201984, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-2227275264 : ℝ) * (20 * 32768 * P 1) + (2227275264 : ℝ) * (20 * 32768 * P 7) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 1)) + 0 ≤ (8852765569327104 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound16 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row16 (actualZ P) ≤ (LocalData.row16.rhs : ℝ) := by
  have hr := range13 P h
  have hUc : (292551 : ℝ)/SC ≤ (292551 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 261633 292551 (P 8-P 1) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 261633 292551 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 1)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound17 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row17 (actualZ P) ≤ (LocalData.row17.rhs : ℝ) := by
  have hr := range14 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 33536) 29184 45301 33536 = true := by
    rw [pointWord33536]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 29184 ≤ 29184 by decide) (P 3-P 2) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 33536 = (-36820669952 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord33536, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 29184 33536 = (25182855327383552 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord33536, trip, lo32, hi32]
  rw [hs, he] at hv
  change (36820669952 : ℝ) * (20 * 32768 * P 2) + (-36820669952 : ℝ) * (20 * 32768 * P 3) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 3-P 2)) + 0 ≤ (-25182855327383552 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound18 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row18 (actualZ P) ≤ (LocalData.row18.rhs : ℝ) := by
  have hr := range14 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 33696) 29184 45301 33696 = true := by
    rw [pointWord33696]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 29184 ≤ 29184 by decide) (P 3-P 2) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 33696 = (-32079893504 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord33696, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 29184 33696 = (21995568985604096 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord33696, trip, lo32, hi32]
  rw [hs, he] at hv
  change (32079893504 : ℝ) * (20 * 32768 * P 2) + (-32079893504 : ℝ) * (20 * 32768 * P 3) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 3-P 2)) + 0 ≤ (-21995568985604096 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound19 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row19 (actualZ P) ≤ (LocalData.row19.rhs : ℝ) := by
  have hr := range15 P h
  have hUc : (79846 : ℝ)/SC ≤ (79846 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 58850 79846 (P 4-P 2) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 58850 79846 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 4-P 2)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound20 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row20 (actualZ P) ≤ (LocalData.row20.rhs : ℝ) := by
  have hr := range16 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 101120) 88516 113727 101120 = true := by
    rw [pointWord101120]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 88516 ≤ 88516 by decide) (P 5-P 2) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 101120 = (3404096512 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord101120, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 88516 101120 = (-6820571906138112 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord101120, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-3404096512 : ℝ) * (20 * 32768 * P 2) + (3404096512 : ℝ) * (20 * 32768 * P 5) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 5-P 2)) + 0 ≤ (6820571906138112 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound21 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row21 (actualZ P) ≤ (LocalData.row21.rhs : ℝ) := by
  have hr := range17 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 134240) 117700 142911 134240 = true := by
    rw [pointWord134240]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 117700 ≤ 117700 by decide) (P 6-P 2) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 134240 = (3397841920 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord134240, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 117700 134240 = (-9005532857655296 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord134240, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-3397841920 : ℝ) * (20 * 32768 * P 2) + (3397841920 : ℝ) * (20 * 32768 * P 6) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 2)) + 0 ≤ (9005532857655296 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound22 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row22 (actualZ P) ≤ (LocalData.row22.rhs : ℝ) := by
  have hr := range18 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 168064) 146245 175359 168064 = true := by
    rw [pointWord168064]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 146245 ≤ 146245 by decide) (P 7-P 2) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 168064 = (2509929984 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord168064, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 146245 168064 = (-8329403302834176 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord168064, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-2509929984 : ℝ) * (20 * 32768 * P 2) + (2509929984 : ℝ) * (20 * 32768 * P 7) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 2)) + 0 ≤ (8329403302834176 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound23 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row23 (actualZ P) ≤ (LocalData.row23.rhs : ℝ) := by
  have hr := range19 P h
  have hUc : (264006 : ℝ)/SC ≤ (264006 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 233088 264006 (P 8-P 2) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 233088 264006 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 2)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound24 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row24 (actualZ P) ≤ (LocalData.row24.rhs : ℝ) := by
  have hr := range20 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 33536) 29666 44151 33536 = true := by
    rw [pointWord33536]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 29666 ≤ 29666 by decide) (P 4-P 3) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 33536 = (-36820669952 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord33536, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 29666 33536 = (25182855356997632 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord33536, trip, lo32, hi32]
  rw [hs, he] at hv
  change (36820669952 : ℝ) * (20 * 32768 * P 3) + (-36820669952 : ℝ) * (20 * 32768 * P 4) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 4-P 3)) + 0 ≤ (-25182855356997632 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound25 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row25 (actualZ P) ≤ (LocalData.row25.rhs : ℝ) := by
  have hr := range20 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 33728) 29666 44151 33728 = true := by
    rw [pointWord33728]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 29666 ≤ 29666 by decide) (P 4-P 3) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 33728 = (-31146338816 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord33728, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 29666 33728 = (21366129300463616 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord33728, trip, lo32, hi32]
  rw [hs, he] at hv
  change (31146338816 : ℝ) * (20 * 32768 * P 3) + (-31146338816 : ℝ) * (20 * 32768 * P 4) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 4-P 3)) + 0 ≤ (-21366129300463616 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound26 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row26 (actualZ P) ≤ (LocalData.row26.rhs : ℝ) := by
  have hr := range21 P h
  have hUc : (84543 : ℝ)/SC ≤ (84543 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 59332 84543 (P 5-P 3) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 59332 84543 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 5-P 3)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound27 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row27 (actualZ P) ≤ (LocalData.row27.rhs : ℝ) := by
  have hr := range22 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 100320) 88516 113727 100320 = true := by
    rw [pointWord100320]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 88516 ≤ 88516 by decide) (P 6-P 3) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 100320 = (1987692544 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord100320, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 88516 100320 = (-3967561988620288 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord100320, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-1987692544 : ℝ) * (20 * 32768 * P 3) + (1987692544 : ℝ) * (20 * 32768 * P 6) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 3)) + 0 ≤ (3967561988620288 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound28 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row28 (actualZ P) ≤ (LocalData.row28.rhs : ℝ) := by
  have hr := range23 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 134336) 117061 146175 134336 = true := by
    rw [pointWord134336]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 117061 ≤ 117061 by decide) (P 7-P 3) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 134336 = (3477716992 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord134336, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 117061 134336 = (-9220057914357760 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord134336, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-3477716992 : ℝ) * (20 * 32768 * P 3) + (3477716992 : ℝ) * (20 * 32768 * P 7) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 3)) + 0 ≤ (9220057914357760 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound29 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row29 (actualZ P) ≤ (LocalData.row29.rhs : ℝ) := by
  have hr := range24 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 227520) 203904 228311 227520 = true := by
    rw [pointWord227520]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 174790 ≤ 203904 by decide) (P 8-P 3) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 227520 = (-444589568 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord227520, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 174790 227520 = (2027854590832640 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord227520, trip, lo32, hi32]
  rw [hs, he] at hv
  change (444589568 : ℝ) * (20 * 32768 * P 3) + (-444589568 : ℝ) * (20 * 32768 * P 8) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 3)) + 0 ≤ (-2027854590832640 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound30 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row30 (actualZ P) ≤ (LocalData.row30.rhs : ℝ) := by
  have hr := range25 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 33536) 29666 44151 33536 = true := by
    rw [pointWord33536]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 29666 ≤ 29666 by decide) (P 5-P 4) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 33536 = (-36820669952 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord33536, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 29666 33536 = (25182855356997632 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord33536, trip, lo32, hi32]
  rw [hs, he] at hv
  change (36820669952 : ℝ) * (20 * 32768 * P 4) + (-36820669952 : ℝ) * (20 * 32768 * P 5) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 5-P 4)) + 0 ≤ (-25182855356997632 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound31 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row31 (actualZ P) ≤ (LocalData.row31.rhs : ℝ) := by
  have hr := range26 P h
  have hUc : (84061 : ℝ)/SC ≤ (84061 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 58850 84061 (P 6-P 4) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 58850 84061 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 4)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound32 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row32 (actualZ P) ≤ (LocalData.row32.rhs : ℝ) := by
  have hr := range27 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 101024) 87395 116509 101024 = true := by
    rw [pointWord101024]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 87395 ≤ 87395 by decide) (P 7-P 4) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 101024 = (3242002944 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord101024, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 87395 101024 = (-6492909988745216 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord101024, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-3242002944 : ℝ) * (20 * 32768 * P 4) + (3242002944 : ℝ) * (20 * 32768 * P 7) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 4)) + 0 ≤ (6492909988745216 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound33 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row33 (actualZ P) ≤ (LocalData.row33.rhs : ℝ) := by
  have hr := range28 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 165824) 159753 184160 165824 = true := by
    rw [pointWord165824]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 145124 ≤ 159753 by decide) (P 8-P 4) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 165824 = (1233925120 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord165824, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 145124 165824 = (-4070814095663104 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord165824, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-1233925120 : ℝ) * (20 * 32768 * P 4) + (1233925120 : ℝ) * (20 * 32768 * P 8) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 4)) + 0 ≤ (4070814095663104 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound34 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row34 (actualZ P) ≤ (LocalData.row34.rhs : ℝ) := by
  have hr := range29 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 33696) 29184 45301 33696 = true := by
    rw [pointWord33696]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 29184 ≤ 29184 by decide) (P 6-P 5) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 33696 = (-32079893504 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord33696, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 29184 33696 = (21995568985604096 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord33696, trip, lo32, hi32]
  rw [hs, he] at hv
  change (32079893504 : ℝ) * (20 * 32768 * P 5) + (-32079893504 : ℝ) * (20 * 32768 * P 6) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 5)) + 0 ≤ (-21995568985604096 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound35 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row35 (actualZ P) ≤ (LocalData.row35.rhs : ℝ) := by
  have hr := range30 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 67584) 57729 86843 67584 = true := by
    rw [pointWord67584]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 57729 ≤ 57729 by decide) (P 7-P 5) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 67584 = (1689130496 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord67584, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 57729 67584 = (-2277316915343360 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord67584, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-1689130496 : ℝ) * (20 * 32768 * P 5) + (1689130496 : ℝ) * (20 * 32768 * P 7) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 5)) + 0 ≤ (2277316915343360 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound36 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row36 (actualZ P) ≤ (LocalData.row36.rhs : ℝ) := by
  have hr := range31 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 131424) 119361 154494 131424 = true := by
    rw [pointWord131424]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 115458 ≤ 119361 by decide) (P 8-P 5) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 131424 = (523880960 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord131424, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 115458 131424 = (-1374652449533952 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord131424, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-523880960 : ℝ) * (20 * 32768 * P 5) + (523880960 : ℝ) * (20 * 32768 * P 8) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 5)) + 0 ≤ (1374652449533952 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound37 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row37 (actualZ P) ≤ (LocalData.row37.rhs : ℝ) := by
  have hr := range32 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 33984) 28545 57659 33984 = true := by
    rw [pointWord33984]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 28545 ≤ 28545 by decide) (P 7-P 6) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 33984 = (-23853524480 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord33984, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 28545 33984 = (16428152158996480 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord33984, trip, lo32, hi32]
  rw [hs, he] at hv
  change (23853524480 : ℝ) * (20 * 32768 * P 6) + (-23853524480 : ℝ) * (20 * 32768 * P 7) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 6)) + 0 ≤ (-16428152158996480 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound38 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row38 (actualZ P) ≤ (LocalData.row38.rhs : ℝ) := by
  have hr := range32 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 33792) 28545 57659 33792 = true := by
    rw [pointWord33792]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 28545 ≤ 28545 by decide) (P 7-P 6) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 33792 = (-29293851136 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord33792, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 28545 33792 = (20115331631083520 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord33792, trip, lo32, hi32]
  rw [hs, he] at hv
  change (29293851136 : ℝ) * (20 * 32768 * P 6) + (-29293851136 : ℝ) * (20 * 32768 * P 7) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 6)) + 0 ≤ (-20115331631083520 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound39 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row39 (actualZ P) ≤ (LocalData.row39.rhs : ℝ) := by
  have hr := range33 P h
  have hUc : (96765 : ℝ)/SC ≤ (96765 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 57729 96765 (P 8-P 7) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 57729 96765 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 7)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound40 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row40 (actualZ P) ≤ (LocalData.row40.rhs : ℝ) := by
  have hr := range34 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 34784) 26112 53902 34784 = true := by
    rw [pointWord34784]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 26112 ≤ 26112 by decide) (P 9-P 8) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 34784 = (-3082366976 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord34784, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 26112 34784 = (2148325269766144 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord34784, trip, lo32, hi32]
  rw [hs, he] at hv
  change (3082366976 : ℝ) * (20 * 32768 * P 8) + (-3082366976 : ℝ) * (20 * 32768 * P 9) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 9-P 8)) + 0 ≤ (-2148325269766144 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound41 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row41 (actualZ P) ≤ (LocalData.row41.rhs : ℝ) := by
  have hr := range35 P h
  have hUc : (169290 : ℝ)/SC ≤ (169290 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 116017 169290 (P 9-P 6) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 116017 169290 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 9-P 6)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound42 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row42 (actualZ P) ≤ (LocalData.row42.rhs : ℝ) := by
  have hr := range36 P h
  have hUc : (198956 : ℝ)/SC ≤ (198956 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 145683 198956 (P 9-P 5) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 145683 198956 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 9-P 5)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound43 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row43 (actualZ P) ≤ (LocalData.row43.rhs : ℝ) := by
  have hr := range37 P h
  have hUc : (228622 : ℝ)/SC ≤ (228622 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 184715 228622 (P 9-P 4) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 184715 228622 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 9-P 4)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound44 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row44 (actualZ P) ≤ (LocalData.row44.rhs : ℝ) := by
  have hr := range38 P h
  have hUc : (257806 : ℝ)/SC ≤ (257806 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 230016 257806 (P 9-P 3) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 230016 257806 = 71900 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 9-P 3)) + 0 ≤ (-2412563660800 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound45 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row45 (actualZ P) ≤ (LocalData.row45.rhs : ℝ) := by
  have hr := range39 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 262016) 258561 286351 262016 = true := by
    rw [pointWord262016]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 233078 ≤ 258561 by decide) (P 9-P 2) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 262016 = (74247680 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord262016, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 233078 262016 = (-388911408713728 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord262016, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-74247680 : ℝ) * (20 * 32768 * P 2) + (74247680 : ℝ) * (20 * 32768 * P 9) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 9-P 2)) + 0 ≤ (388911408713728 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound46 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row46 (actualZ P) ≤ (LocalData.row46.rhs : ℝ) := by
  have hr := range40 P h
  have hUc : (384896 : ℝ)/SC ≤ (384896 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 284673 384896 (P 9-P 1) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 284673 384896 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 9-P 1)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound47 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row47 (actualZ P) ≤ (LocalData.row47.rhs : ℝ) := by
  have hr := range41 P h
  have hUc : (94169 : ℝ)/SC ≤ (94169 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 60721 94169 (P 8-P 7) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 60721 94169 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 7)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound48 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row48 (actualZ P) ≤ (LocalData.row48.rhs : ℝ) := by
  have hr := range42 P h
  have hUc : (123353 : ℝ)/SC ≤ (123353 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 89905 123353 (P 8-P 6) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 89905 123353 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 6)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound49 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row49 (actualZ P) ≤ (LocalData.row49.rhs : ℝ) := by
  have hr := range43 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 132096) 119571 153019 132096 = true := by
    rw [pointWord132096]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 119571 ≤ 119571 by decide) (P 8-P 5) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 132096 = (1284774912 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord132096, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 119571 132096 = (-3379722992289792 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord132096, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-1284774912 : ℝ) * (20 * 32768 * P 5) + (1284774912 : ℝ) * (20 * 32768 * P 8) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 5)) + 0 ≤ (3379722992289792 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound50 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row50 (actualZ P) ≤ (LocalData.row50.rhs : ℝ) := by
  have hr := range44 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 166112) 158603 182685 166112 = true := by
    rw [pointWord166112]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 149237 ≤ 158603 by decide) (P 8-P 4) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 166112 = (1424091648 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord166112, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 149237 166112 = (-4702042082490368 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord166112, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-1424091648 : ℝ) * (20 * 32768 * P 4) + (1424091648 : ℝ) * (20 * 32768 * P 8) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 4)) + 0 ≤ (4702042082490368 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound51 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row51 (actualZ P) ≤ (LocalData.row51.rhs : ℝ) := by
  have hr := range45 P h
  have hUc : (211869 : ℝ)/SC ≤ (211869 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 203904 211869 (P 8-P 3) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 203904 211869 = 6735216 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 3)) + 0 ≤ (-225996347277312 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound52 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row52 (actualZ P) ≤ (LocalData.row52.rhs : ℝ) := by
  have hr := range46 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 233472) 232449 240414 233472 = true := by
    rw [pointWord233472]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 206966 ≤ 232449 by decide) (P 8-P 2) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 233472 = (1660200448 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord233472, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 206966 233472 = (-7663606811168768 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord233472, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-1660200448 : ℝ) * (20 * 32768 * P 2) + (1660200448 : ℝ) * (20 * 32768 * P 8) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 2)) + 0 ≤ (7663606811168768 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound53 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row53 (actualZ P) ≤ (LocalData.row53.rhs : ℝ) := by
  have hr := range47 P h
  have hUc : (334912 : ℝ)/SC ≤ (334912 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 258561 334912 (P 8-P 1) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 258561 334912 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 8-P 1)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound54 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row54 (actualZ P) ≤ (LocalData.row54.rhs : ℝ) := by
  have hr := range48 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 34048) 29184 45301 34048 = true := by
    rw [pointWord34048]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 29184 ≤ 29184 by decide) (P 7-P 6) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 34048 = (-22079180800 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord34048, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 29184 34048 = (15221032754348032 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord34048, trip, lo32, hi32]
  rw [hs, he] at hv
  change (22079180800 : ℝ) * (20 * 32768 * P 6) + (-22079180800 : ℝ) * (20 * 32768 * P 7) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 6)) + 0 ≤ (-15221032754348032 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound55 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row55 (actualZ P) ≤ (LocalData.row55.rhs : ℝ) := by
  have hr := range49 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 67584) 58850 84333 67584 = true := by
    rw [pointWord67584]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 58850 ≤ 58850 by decide) (P 7-P 5) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 67584 = (1689130496 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord67584, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 58850 67584 = (-2277316892385280 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord67584, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-1689130496 : ℝ) * (20 * 32768 * P 5) + (1689130496 : ℝ) * (20 * 32768 * P 7) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 5)) + 0 ≤ (2277316892385280 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound56 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row56 (actualZ P) ≤ (LocalData.row56.rhs : ℝ) := by
  have hr := range50 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 101120) 88516 113999 101120 = true := by
    rw [pointWord101120]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 88516 ≤ 88516 by decide) (P 7-P 4) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 101120 = (3404096512 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord101120, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 88516 101120 = (-6820571906138112 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord101120, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-3404096512 : ℝ) * (20 * 32768 * P 4) + (3404096512 : ℝ) * (20 * 32768 * P 7) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 4)) + 0 ≤ (6820571906138112 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound57 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row57 (actualZ P) ≤ (LocalData.row57.rhs : ℝ) := by
  have hr := range51 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 135168) 117700 143183 135168 = true := by
    rw [pointWord135168]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 117700 ≤ 117700 by decide) (P 7-P 3) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 135168 = (4105786880 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord135168, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 117700 135168 = (-10912567847903232 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord135168, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-4105786880 : ℝ) * (20 * 32768 * P 3) + (4105786880 : ℝ) * (20 * 32768 * P 7) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 3)) + 0 ≤ (10912567847903232 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound58 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row58 (actualZ P) ≤ (LocalData.row58.rhs : ℝ) := by
  have hr := range52 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 168512) 146245 171728 168512 = true := by
    rw [pointWord168512]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 146245 ≤ 146245 by decide) (P 7-P 2) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 168512 = (2700740608 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord168512, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 146245 168512 = (-8971607951226880 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord168512, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-2700740608 : ℝ) * (20 * 32768 * P 2) + (2700740608 : ℝ) * (20 * 32768 * P 7) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 2)) + 0 ≤ (8971607951226880 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound59 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row59 (actualZ P) ≤ (LocalData.row59.rhs : ℝ) := by
  have hr := range53 P h
  have hUc : (274191 : ℝ)/SC ≤ (274191 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 172357 274191 (P 7-P 1) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 172357 274191 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 7-P 1)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound60 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row60 (actualZ P) ≤ (LocalData.row60.rhs : ℝ) := by
  have hr := range54 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 33728) 29666 44151 33728 = true := by
    rw [pointWord33728]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 29666 ≤ 29666 by decide) (P 6-P 5) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 33728 = (-31146338816 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord33728, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 29666 33728 = (21366129300463616 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord33728, trip, lo32, hi32]
  rw [hs, he] at hv
  change (31146338816 : ℝ) * (20 * 32768 * P 5) + (-31146338816 : ℝ) * (20 * 32768 * P 6) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 5)) + 0 ≤ (-21366129300463616 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound61 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row61 (actualZ P) ≤ (LocalData.row61.rhs : ℝ) := by
  have hr := range54 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 33536) 29666 44151 33536 = true := by
    rw [pointWord33536]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 29666 ≤ 29666 by decide) (P 6-P 5) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 33536 = (-36820669952 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord33536, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 29666 33536 = (25182855356997632 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord33536, trip, lo32, hi32]
  rw [hs, he] at hv
  change (36820669952 : ℝ) * (20 * 32768 * P 5) + (-36820669952 : ℝ) * (20 * 32768 * P 6) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 5)) + 0 ≤ (-25182855356997632 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound62 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row62 (actualZ P) ≤ (LocalData.row62.rhs : ℝ) := by
  have hr := range55 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 67264) 59332 84815 67264 = true := by
    rw [pointWord67264]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 59332 ≤ 59332 by decide) (P 6-P 4) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 67264 = (119734784 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord67264, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 59332 67264 = (-161048283627520 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord67264, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-119734784 : ℝ) * (20 * 32768 * P 4) + (119734784 : ℝ) * (20 * 32768 * P 6) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 4)) + 0 ≤ (161048283627520 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound63 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row63 (actualZ P) ≤ (LocalData.row63.rhs : ℝ) := by
  have hr := range56 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 101120) 88516 113999 101120 = true := by
    rw [pointWord101120]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 88516 ≤ 88516 by decide) (P 6-P 3) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 101120 = (3404096512 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord101120, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 88516 101120 = (-6820571906138112 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord101120, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-3404096512 : ℝ) * (20 * 32768 * P 3) + (3404096512 : ℝ) * (20 * 32768 * P 6) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 3)) + 0 ≤ (6820571906138112 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound64 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row64 (actualZ P) ≤ (LocalData.row64.rhs : ℝ) := by
  have hr := range57 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 135168) 117061 142544 135168 = true := by
    rw [pointWord135168]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 117061 ≤ 117061 by decide) (P 6-P 2) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 135168 = (4105786880 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord135168, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 117061 135168 = (-10912567854446592 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord135168, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-4105786880 : ℝ) * (20 * 32768 * P 2) + (4105786880 : ℝ) * (20 * 32768 * P 6) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 2)) + 0 ≤ (10912567854446592 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound65 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row65 (actualZ P) ≤ (LocalData.row65.rhs : ℝ) := by
  have hr := range58 P h
  have hUc : (245007 : ℝ)/SC ≤ (245007 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 143173 245007 (P 6-P 1) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 143173 245007 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 6-P 1)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound66 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row66 (actualZ P) ≤ (LocalData.row66.rhs : ℝ) := by
  have hr := range59 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 33536) 29666 44151 33536 = true := by
    rw [pointWord33536]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 29666 ≤ 29666 by decide) (P 5-P 4) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 33536 = (-36820669952 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord33536, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 29666 33536 = (25182855356997632 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord33536, trip, lo32, hi32]
  rw [hs, he] at hv
  change (36820669952 : ℝ) * (20 * 32768 * P 4) + (-36820669952 : ℝ) * (20 * 32768 * P 5) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 5-P 4)) + 0 ≤ (-25182855356997632 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound67 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row67 (actualZ P) ≤ (LocalData.row67.rhs : ℝ) := by
  have hr := range59 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 33728) 29666 44151 33728 = true := by
    rw [pointWord33728]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 29666 ≤ 29666 by decide) (P 5-P 4) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 33728 = (-31146338816 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord33728, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 29666 33728 = (21366129300463616 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord33728, trip, lo32, hi32]
  rw [hs, he] at hv
  change (31146338816 : ℝ) * (20 * 32768 * P 4) + (-31146338816 : ℝ) * (20 * 32768 * P 5) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 5-P 4)) + 0 ≤ (-21366129300463616 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound68 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row68 (actualZ P) ≤ (LocalData.row68.rhs : ℝ) := by
  have hr := range60 P h
  have hUc : (84333 : ℝ)/SC ≤ (84333 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 58850 84333 (P 5-P 3) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 58850 84333 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 5-P 3)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound69 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row69 (actualZ P) ≤ (LocalData.row69.rhs : ℝ) := by
  have hr := range61 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 101632) 87395 112878 101632 = true := by
    rw [pointWord101632]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 87395 ≤ 87395 by decide) (P 5-P 2) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 101632 = (4228782080 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord101632, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 87395 101632 = (-8492579881519104 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord101632, trip, lo32, hi32]
  rw [hs, he] at hv
  change (-4228782080 : ℝ) * (20 * 32768 * P 2) + (4228782080 : ℝ) * (20 * 32768 * P 5) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 5-P 2)) + 0 ≤ (8492579881519104 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound70 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row70 (actualZ P) ≤ (LocalData.row70.rhs : ℝ) := by
  have hr := range62 P h
  have hUc : (215341 : ℝ)/SC ≤ (215341 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 113507 215341 (P 5-P 1) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 113507 215341 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 5-P 1)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound71 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row71 (actualZ P) ≤ (LocalData.row71.rhs : ℝ) := by
  have hr := range63 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 33696) 29184 45301 33696 = true := by
    rw [pointWord33696]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 29184 ≤ 29184 by decide) (P 4-P 3) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 33696 = (-32079893504 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord33696, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 29184 33696 = (21995568985604096 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord33696, trip, lo32, hi32]
  rw [hs, he] at hv
  change (32079893504 : ℝ) * (20 * 32768 * P 3) + (-32079893504 : ℝ) * (20 * 32768 * P 4) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 4-P 3)) + 0 ≤ (-21995568985604096 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound72 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row72 (actualZ P) ≤ (LocalData.row72.rhs : ℝ) := by
  have hr := range64 P h
  have hUc : (81811 : ℝ)/SC ≤ (81811 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 57729 81811 (P 4-P 2) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 57729 81811 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 4-P 2)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound73 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row73 (actualZ P) ≤ (LocalData.row73.rhs : ℝ) := by
  have hr := range65 P h
  have hUc : (176309 : ℝ)/SC ≤ (176309 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 83841 176309 (P 4-P 1) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 83841 176309 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 4-P 1)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound74 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row74 (actualZ P) ≤ (LocalData.row74.rhs : ℝ) := by
  have hr := range66 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 33792) 28545 36510 33792 = true := by
    rw [pointWord33792]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 28545 ≤ 28545 by decide) (P 3-P 2) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 33792 = (-29293851136 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord33792, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 28545 33792 = (20115331631083520 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord33792, trip, lo32, hi32]
  rw [hs, he] at hv
  change (29293851136 : ℝ) * (20 * 32768 * P 2) + (-29293851136 : ℝ) * (20 * 32768 * P 3) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 3-P 2)) + 0 ≤ (-20115331631083520 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound75 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row75 (actualZ P) ≤ (LocalData.row75.rhs : ℝ) := by
  have hr := range67 P h
  have hUc : (102463 : ℝ)/SC ≤ (102463 : ℝ)/SC := by norm_num [SC]
  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS 26112 102463 (P 2-P 1) hr.1 (hr.2.trans hUc)
  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK 26112 102463 = 0 := by decide +kernel
  rw [hlb] at hv
  change (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 2-P 1)) + 0 ≤ (0 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowSound76 (P : ℕ → ℝ) (h : Domain P) :
    Sparse78.eval LocalData.row76 (actualZ P) ≤ (LocalData.row76.rhs : ℝ) := by
  have hr := range67 P h
  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT 33248) 26112 102463 33248 = true := by
    rw [pointWord33248]
    decide +kernel
  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv
  have hv := QuantizedComponent.scaled_anchor ht (show 26112 ≤ 26112 by decide) (P 2-P 1) hr.1 hr.2
  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) 33248 = (-45659680768 : ℤ) := by
    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord33248, trip, lo32, hi32]
  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) 26112 33248 = (31085711956770816 : ℤ) := by
    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord33248, trip, lo32, hi32]
  rw [hs, he] at hv
  change (45659680768 : ℝ) * (20 * 32768 * P 1) + (-45659680768 : ℝ) * (20 * 32768 * P 2) + (-1 : ℝ) * ((QuantizedComponent.kappa : ℝ) * wfun (P 2-P 1)) + 0 ≤ (-31085711956770816 : ℝ)
  norm_num at hv ⊢
  nlinarith [hv]

theorem rowsSound (P : ℕ → ℝ) (h : Domain P) (i : Fin 77) :
    Sparse78.eval (LocalData.rows i) (actualZ P) ≤ ((LocalData.rows i).rhs : ℝ) := by
  fin_cases i
  · exact rowSound0 P h
  · exact rowSound1 P h
  · exact rowSound2 P h
  · exact rowSound3 P h
  · exact rowSound4 P h
  · exact rowSound5 P h
  · exact rowSound6 P h
  · exact rowSound7 P h
  · exact rowSound8 P h
  · exact rowSound9 P h
  · exact rowSound10 P h
  · exact rowSound11 P h
  · exact rowSound12 P h
  · exact rowSound13 P h
  · exact rowSound14 P h
  · exact rowSound15 P h
  · exact rowSound16 P h
  · exact rowSound17 P h
  · exact rowSound18 P h
  · exact rowSound19 P h
  · exact rowSound20 P h
  · exact rowSound21 P h
  · exact rowSound22 P h
  · exact rowSound23 P h
  · exact rowSound24 P h
  · exact rowSound25 P h
  · exact rowSound26 P h
  · exact rowSound27 P h
  · exact rowSound28 P h
  · exact rowSound29 P h
  · exact rowSound30 P h
  · exact rowSound31 P h
  · exact rowSound32 P h
  · exact rowSound33 P h
  · exact rowSound34 P h
  · exact rowSound35 P h
  · exact rowSound36 P h
  · exact rowSound37 P h
  · exact rowSound38 P h
  · exact rowSound39 P h
  · exact rowSound40 P h
  · exact rowSound41 P h
  · exact rowSound42 P h
  · exact rowSound43 P h
  · exact rowSound44 P h
  · exact rowSound45 P h
  · exact rowSound46 P h
  · exact rowSound47 P h
  · exact rowSound48 P h
  · exact rowSound49 P h
  · exact rowSound50 P h
  · exact rowSound51 P h
  · exact rowSound52 P h
  · exact rowSound53 P h
  · exact rowSound54 P h
  · exact rowSound55 P h
  · exact rowSound56 P h
  · exact rowSound57 P h
  · exact rowSound58 P h
  · exact rowSound59 P h
  · exact rowSound60 P h
  · exact rowSound61 P h
  · exact rowSound62 P h
  · exact rowSound63 P h
  · exact rowSound64 P h
  · exact rowSound65 P h
  · exact rowSound66 P h
  · exact rowSound67 P h
  · exact rowSound68 P h
  · exact rowSound69 P h
  · exact rowSound70 P h
  · exact rowSound71 P h
  · exact rowSound72 P h
  · exact rowSound73 P h
  · exact rowSound74 P h
  · exact rowSound75 P h
  · exact rowSound76 P h

set_option pp.fullNames true
#print axioms rowsSound
end StructuralS1RM20261018.LocalComponents
end
