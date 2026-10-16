/- SPDX-License-Identifier: Apache-2.0
Generated concrete scalar data; check the matching kernel receipts.
No global coverage is asserted.
-/
import StructuralW10Followup20261016.scalar_Data
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralW10Followup20261016.Scalar
def q7_0 : Quad := ⟨(17729401 : ℚ)/1000000000, (-51429201123203 : ℚ)/524288000000000, (10786852369244352949168637 : ℚ)/85899345920000000000000000⟩
theorem scalar7_0 {x : ℝ}
    (hl : (low2 : ℝ)≤x) (hu : x≤(top2 : ℝ)) : evalR q7_0 x≤AMW.Cert.wfun x := by
  apply check_sound q7_0 base2 top2 low2 hull2
  · norm_num [q7_0]
  · decide +kernel
  · exact (by norm_num [base2,low2] : (base2 : ℝ)≤(low2 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_0
def q7_1 : Quad := ⟨(339397 : ℚ)/1000000000, (-404559627553 : ℚ)/131072000000000, (26631566261157815002249 : ℚ)/5368709120000000000000000⟩
theorem scalar7_1 {x : ℝ}
    (hl : (low7 : ℝ)≤x) (hu : x≤(top7 : ℝ)) : evalR q7_1 x≤AMW.Cert.wfun x := by
  apply check_sound q7_1 base7 top7 low7 hull7
  · norm_num [q7_1]
  · decide +kernel
  · exact (by norm_num [base7,low7] : (base7 : ℝ)≤(low7 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_1
def q7_2 : Quad := ⟨(126603 : ℚ)/500000000, (-1049012494237 : ℚ)/262144000000000, (666195236589684365906719 : ℚ)/42949672960000000000000000⟩
theorem scalar7_2 {x : ℝ}
    (hl : (low9 : ℝ)≤x) (hu : x≤(top9 : ℝ)) : evalR q7_2 x≤AMW.Cert.wfun x := by
  apply check_sound q7_2 base9 top9 low9 hull9
  · norm_num [q7_2]
  · decide +kernel
  · exact (by norm_num [base9,low9] : (base9 : ℝ)≤(low9 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_2
def q7_3 : Quad := ⟨(459727 : ℚ)/1000000000, (-4366239106663 : ℚ)/524288000000000, (640702145375027241833399 : ℚ)/17179869184000000000000000⟩
theorem scalar7_3 {x : ℝ}
    (hl : (low10 : ℝ)≤x) (hu : x≤(top10 : ℝ)) : evalR q7_3 x≤AMW.Cert.wfun x := by
  apply check_sound q7_3 base10 top10 low10 hull10
  · norm_num [q7_3]
  · decide +kernel
  · exact (by norm_num [base10,low10] : (base10 : ℝ)≤(low10 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_3
def q7_4 : Quad := ⟨(69949 : ℚ)/125000000, (-175176125293 : ℚ)/13107200000000, (34272352457460786594457 : ℚ)/429496729600000000000000⟩
theorem scalar7_4 {x : ℝ}
    (hl : (low12 : ℝ)≤x) (hu : x≤(top12 : ℝ)) : evalR q7_4 x≤AMW.Cert.wfun x := by
  apply check_sound q7_4 base12 top12 low12 hull12
  · norm_num [q7_4]
  · decide +kernel
  · exact (by norm_num [base12,low12] : (base12 : ℝ)≤(low12 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_4
def q7_5 : Quad := ⟨(116941 : ℚ)/250000000, (-77359270637 : ℚ)/6553600000000, (99845318577609191043873 : ℚ)/1342177280000000000000000⟩
theorem scalar7_5 {x : ℝ}
    (hl : (low13 : ℝ)≤x) (hu : x≤(top13 : ℝ)) : evalR q7_5 x≤AMW.Cert.wfun x := by
  apply check_sound q7_5 base13 top13 low13 hull13
  · norm_num [q7_5]
  · decide +kernel
  · exact (by norm_num [base13,low13] : (base13 : ℝ)≤(low13 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_5
def q7_6 : Quad := ⟨(46328189 : ℚ)/1000000000, (-70759785355129 : ℚ)/524288000000000, (7794411080300665133597089 : ℚ)/85899345920000000000000000⟩
theorem scalar7_6 {x : ℝ}
    (hl : (low1 : ℝ)≤x) (hu : x≤(top1 : ℝ)) : evalR q7_6 x≤AMW.Cert.wfun x := by
  apply check_sound q7_6 base1 top1 low1 hull1
  · norm_num [q7_6]
  · decide +kernel
  · exact (by norm_num [base1,low1] : (base1 : ℝ)≤(low1 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_6
def q7_7 : Quad := ⟨(3075329 : ℚ)/500000000, (-10639590033489 : ℚ)/262144000000000, (2854619209859180119644493 : ℚ)/42949672960000000000000000⟩
theorem scalar7_7 {x : ℝ}
    (hl : (low3 : ℝ)≤x) (hu : x≤(top3 : ℝ)) : evalR q7_7 x≤AMW.Cert.wfun x := by
  apply check_sound q7_7 base3 top3 low3 hull3
  · norm_num [q7_7]
  · decide +kernel
  · exact (by norm_num [base3,low3] : (base3 : ℝ)≤(low3 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_7
def q7_8 : Quad := ⟨(2170993 : ℚ)/1000000000, (-1931597343111 : ℚ)/131072000000000, (25949638891821553030089 : ℚ)/1073741824000000000000000⟩
theorem scalar7_8 {x : ℝ}
    (hl : (low4 : ℝ)≤x) (hu : x≤(top4 : ℝ)) : evalR q7_8 x≤AMW.Cert.wfun x := by
  apply check_sound q7_8 base4 top4 low4 hull4
  · norm_num [q7_8]
  · decide +kernel
  · exact (by norm_num [base4,low4] : (base4 : ℝ)≤(low4 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_8
def q7_9 : Quad := ⟨(1761741 : ℚ)/1000000000, (-7892021518533 : ℚ)/524288000000000, (534607866624042692919781 : ℚ)/17179869184000000000000000⟩
theorem scalar7_9 {x : ℝ}
    (hl : (low5 : ℝ)≤x) (hu : x≤(top5 : ℝ)) : evalR q7_9 x≤AMW.Cert.wfun x := by
  apply check_sound q7_9 base5 top5 low5 hull5
  · norm_num [q7_9]
  · decide +kernel
  · exact (by norm_num [base5,low5] : (base5 : ℝ)≤(low5 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_9
def q7_10 : Quad := ⟨(339397 : ℚ)/1000000000, (-86272802343 : ℚ)/26214400000000, (34359254270460897702673 : ℚ)/5368709120000000000000000⟩
theorem scalar7_10 {x : ℝ}
    (hl : (low7 : ℝ)≤x) (hu : x≤(top7 : ℝ)) : evalR q7_10 x≤AMW.Cert.wfun x := by
  apply check_sound q7_10 base7 top7 low7 hull7
  · norm_num [q7_10]
  · decide +kernel
  · exact (by norm_num [base7,low7] : (base7 : ℝ)≤(low7 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_10
def q7_11 : Quad := ⟨(86121 : ℚ)/200000000, (-1371785125211 : ℚ)/262144000000000, (306130622799902307430649 : ℚ)/21474836480000000000000000⟩
theorem scalar7_11 {x : ℝ}
    (hl : (low8 : ℝ)≤x) (hu : x≤(top8 : ℝ)) : evalR q7_11 x≤AMW.Cert.wfun x := by
  apply check_sound q7_11 base8 top8 low8 hull8
  · norm_num [q7_11]
  · decide +kernel
  · exact (by norm_num [base8,low8] : (base8 : ℝ)≤(low8 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_11
def q7_12 : Quad := ⟨(459727 : ℚ)/1000000000, (-2196321709731 : ℚ)/262144000000000, (811741420869437126411163 : ℚ)/21474836480000000000000000⟩
theorem scalar7_12 {x : ℝ}
    (hl : (low10 : ℝ)≤x) (hu : x≤(top10 : ℝ)) : evalR q7_12 x≤AMW.Cert.wfun x := by
  apply check_sound q7_12 base10 top10 low10 hull10
  · norm_num [q7_12]
  · decide +kernel
  · exact (by norm_num [base10,low10] : (base10 : ℝ)≤(low10 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_12
def q7_13 : Quad := ⟨(152881 : ℚ)/250000000, (-1655638218857 : ℚ)/131072000000000, (1394134018546047154259853 : ℚ)/21474836480000000000000000⟩
theorem scalar7_13 {x : ℝ}
    (hl : (low11 : ℝ)≤x) (hu : x≤(top11 : ℝ)) : evalR q7_13 x≤AMW.Cert.wfun x := by
  apply check_sound q7_13 base11 top11 low11 hull11
  · norm_num [q7_13]
  · decide +kernel
  · exact (by norm_num [base11,low11] : (base11 : ℝ)≤(low11 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_13
def q7_14 : Quad := ⟨(17729401 : ℚ)/1000000000, (-2658873983149 : ℚ)/26214400000000, (709388430804095465543701 : ℚ)/5368709120000000000000000⟩
theorem scalar7_14 {x : ℝ}
    (hl : (low2 : ℝ)≤x) (hu : x≤(top2 : ℝ)) : evalR q7_14 x≤AMW.Cert.wfun x := by
  apply check_sound q7_14 base2 top2 low2 hull2
  · norm_num [q7_14]
  · decide +kernel
  · exact (by norm_num [base2,low2] : (base2 : ℝ)≤(low2 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_14
def q7_15 : Quad := ⟨(3075329 : ℚ)/500000000, (-10864765989423 : ℚ)/262144000000000, (2965280172540627804731469 : ℚ)/42949672960000000000000000⟩
theorem scalar7_15 {x : ℝ}
    (hl : (low3 : ℝ)≤x) (hu : x≤(top3 : ℝ)) : evalR q7_15 x≤AMW.Cert.wfun x := by
  apply check_sound q7_15 base3 top3 low3 hull3
  · norm_num [q7_15]
  · decide +kernel
  · exact (by norm_num [base3,low3] : (base3 : ℝ)≤(low3 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_15
def q7_16 : Quad := ⟨(2170993 : ℚ)/1000000000, (-1982563357659 : ℚ)/131072000000000, (138167734340496615202421 : ℚ)/5368709120000000000000000⟩
theorem scalar7_16 {x : ℝ}
    (hl : (low4 : ℝ)≤x) (hu : x≤(top4 : ℝ)) : evalR q7_16 x≤AMW.Cert.wfun x := by
  apply check_sound q7_16 base4 top4 low4 hull4
  · norm_num [q7_16]
  · decide +kernel
  · exact (by norm_num [base4,low4] : (base4 : ℝ)≤(low4 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_16
def q7_17 : Quad := ⟨(618613 : ℚ)/1000000000, (-3786818138427 : ℚ)/524288000000000, (361954333470117903176637 : ℚ)/17179869184000000000000000⟩
theorem scalar7_17 {x : ℝ}
    (hl : (low6 : ℝ)≤x) (hu : x≤(top6 : ℝ)) : evalR q7_17 x≤AMW.Cert.wfun x := by
  apply check_sound q7_17 base6 top6 low6 hull6
  · norm_num [q7_17]
  · decide +kernel
  · exact (by norm_num [base6,low6] : (base6 : ℝ)≤(low6 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_17
def q7_18 : Quad := ⟨(339397 : ℚ)/1000000000, (-68535261293 : ℚ)/20971520000000, (107166291002551711668397 : ℚ)/17179869184000000000000000⟩
theorem scalar7_18 {x : ℝ}
    (hl : (low7 : ℝ)≤x) (hu : x≤(top7 : ℝ)) : evalR q7_18 x≤AMW.Cert.wfun x := by
  apply check_sound q7_18 base7 top7 low7 hull7
  · norm_num [q7_18]
  · decide +kernel
  · exact (by norm_num [base7,low7] : (base7 : ℝ)≤(low7 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_18
def q7_19 : Quad := ⟨(126603 : ℚ)/500000000, (-1061741061999 : ℚ)/262144000000000, (136994688570146638939803 : ℚ)/8589934592000000000000000⟩
theorem scalar7_19 {x : ℝ}
    (hl : (low9 : ℝ)≤x) (hu : x≤(top9 : ℝ)) : evalR q7_19 x≤AMW.Cert.wfun x := by
  apply check_sound q7_19 base9 top9 low9 hull9
  · norm_num [q7_19]
  · decide +kernel
  · exact (by norm_num [base9,low9] : (base9 : ℝ)≤(low9 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_19
def q7_20 : Quad := ⟨(459727 : ℚ)/1000000000, (-1103053146861 : ℚ)/131072000000000, (40989511589072340993151 : ℚ)/1073741824000000000000000⟩
theorem scalar7_20 {x : ℝ}
    (hl : (low10 : ℝ)≤x) (hu : x≤(top10 : ℝ)) : evalR q7_20 x≤AMW.Cert.wfun x := by
  apply check_sound q7_20 base10 top10 low10 hull10
  · norm_num [q7_20]
  · decide +kernel
  · exact (by norm_num [base10,low10] : (base10 : ℝ)≤(low10 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_20
def q7_21 : Quad := ⟨(46328189 : ℚ)/1000000000, (-76794920839391 : ℚ)/524288000000000, (8820379514331205205369777 : ℚ)/85899345920000000000000000⟩
theorem scalar7_21 {x : ℝ}
    (hl : (low1 : ℝ)≤x) (hu : x≤(top1 : ℝ)) : evalR q7_21 x≤AMW.Cert.wfun x := by
  apply check_sound q7_21 base1 top1 low1 hull1
  · norm_num [q7_21]
  · decide +kernel
  · exact (by norm_num [base1,low1] : (base1 : ℝ)≤(low1 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_21
def q7_22 : Quad := ⟨(17729401 : ℚ)/1000000000, (-4451943750377 : ℚ)/65536000000000, (3473836953388843299181 : ℚ)/53687091200000000000000⟩
theorem scalar7_22 {x : ℝ}
    (hl : (low2 : ℝ)≤x) (hu : x≤(top2 : ℝ)) : evalR q7_22 x≤AMW.Cert.wfun x := by
  apply check_sound q7_22 base2 top2 low2 hull2
  · norm_num [q7_22]
  · decide +kernel
  · exact (by norm_num [base2,low2] : (base2 : ℝ)≤(low2 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_22
def q7_23 : Quad := ⟨(2170993 : ℚ)/1000000000, (-1579191068319 : ℚ)/104857600000000, (87521332891206677075517 : ℚ)/3435973836800000000000000⟩
theorem scalar7_23 {x : ℝ}
    (hl : (low4 : ℝ)≤x) (hu : x≤(top4 : ℝ)) : evalR q7_23 x≤AMW.Cert.wfun x := by
  apply check_sound q7_23 base4 top4 low4 hull4
  · norm_num [q7_23]
  · decide +kernel
  · exact (by norm_num [base4,low4] : (base4 : ℝ)≤(low4 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_23
def q7_24 : Quad := ⟨(1761741 : ℚ)/1000000000, (-1570717897029 : ℚ)/104857600000000, (2641100607665407042546129 : ℚ)/85899345920000000000000000⟩
theorem scalar7_24 {x : ℝ}
    (hl : (low5 : ℝ)≤x) (hu : x≤(top5 : ℝ)) : evalR q7_24 x≤AMW.Cert.wfun x := by
  apply check_sound q7_24 base5 top5 low5 hull5
  · norm_num [q7_24]
  · decide +kernel
  · exact (by norm_num [base5,low5] : (base5 : ℝ)≤(low5 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_24
def q7_25 : Quad := ⟨(339397 : ℚ)/1000000000, (-1641762995309 : ℚ)/524288000000000, (90649341239820637333501 : ℚ)/17179869184000000000000000⟩
theorem scalar7_25 {x : ℝ}
    (hl : (low7 : ℝ)≤x) (hu : x≤(top7 : ℝ)) : evalR q7_25 x≤AMW.Cert.wfun x := by
  apply check_sound q7_25 base7 top7 low7 hull7
  · norm_num [q7_25]
  · decide +kernel
  · exact (by norm_num [base7,low7] : (base7 : ℝ)≤(low7 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_25
def q7_26 : Quad := ⟨(86121 : ℚ)/200000000, (-341982162377 : ℚ)/65536000000000, (18973689004589949554033 : ℚ)/1342177280000000000000000⟩
theorem scalar7_26 {x : ℝ}
    (hl : (low8 : ℝ)≤x) (hu : x≤(top8 : ℝ)) : evalR q7_26 x≤AMW.Cert.wfun x := by
  apply check_sound q7_26 base8 top8 low8 hull8
  · norm_num [q7_26]
  · decide +kernel
  · exact (by norm_num [base8,low8] : (base8 : ℝ)≤(low8 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_26
def q7_27 : Quad := ⟨(46328189 : ℚ)/1000000000, (-15364784457141 : ℚ)/104857600000000, (8825293958724593893038529 : ℚ)/85899345920000000000000000⟩
theorem scalar7_27 {x : ℝ}
    (hl : (low1 : ℝ)≤x) (hu : x≤(top1 : ℝ)) : evalR q7_27 x≤AMW.Cert.wfun x := by
  apply check_sound q7_27 base1 top1 low1 hull1
  · norm_num [q7_27]
  · decide +kernel
  · exact (by norm_num [base1,low1] : (base1 : ℝ)≤(low1 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_27
def q7_28 : Quad := ⟨(3075329 : ℚ)/500000000, (-33857819179 : ℚ)/819200000000, (720317828281289466237 : ℚ)/10485760000000000000000⟩
theorem scalar7_28 {x : ℝ}
    (hl : (low3 : ℝ)≤x) (hu : x≤(top3 : ℝ)) : evalR q7_28 x≤AMW.Cert.wfun x := by
  apply check_sound q7_28 base3 top3 low3 hull3
  · norm_num [q7_28]
  · decide +kernel
  · exact (by norm_num [base3,low3] : (base3 : ℝ)≤(low3 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_28
def q7_29 : Quad := ⟨(2170993 : ℚ)/1000000000, (-762435908149 : ℚ)/52428800000000, (502119110485746136731533 : ℚ)/21474836480000000000000000⟩
theorem scalar7_29 {x : ℝ}
    (hl : (low4 : ℝ)≤x) (hu : x≤(top4 : ℝ)) : evalR q7_29 x≤AMW.Cert.wfun x := by
  apply check_sound q7_29 base4 top4 low4 hull4
  · norm_num [q7_29]
  · decide +kernel
  · exact (by norm_num [base4,low4] : (base4 : ℝ)≤(low4 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_29
def q7_30 : Quad := ⟨(618613 : ℚ)/1000000000, (-1777775998347 : ℚ)/262144000000000, (395607195163862205484433 : ℚ)/21474836480000000000000000⟩
theorem scalar7_30 {x : ℝ}
    (hl : (low6 : ℝ)≤x) (hu : x≤(top6 : ℝ)) : evalR q7_30 x≤AMW.Cert.wfun x := by
  apply check_sound q7_30 base6 top6 low6 hull6
  · norm_num [q7_30]
  · decide +kernel
  · exact (by norm_num [base6,low6] : (base6 : ℝ)≤(low6 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_30
def q7_31 : Quad := ⟨(339397 : ℚ)/1000000000, (-1606542916881 : ℚ)/524288000000000, (412608330260929271468137 : ℚ)/85899345920000000000000000⟩
theorem scalar7_31 {x : ℝ}
    (hl : (low7 : ℝ)≤x) (hu : x≤(top7 : ℝ)) : evalR q7_31 x≤AMW.Cert.wfun x := by
  apply check_sound q7_31 base7 top7 low7 hull7
  · norm_num [q7_31]
  · decide +kernel
  · exact (by norm_num [base7,low7] : (base7 : ℝ)≤(low7 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_31
def q7_32 : Quad := ⟨(17729401 : ℚ)/1000000000, (-53003342666027 : ℚ)/524288000000000, (451769073844154437120757 : ℚ)/3435973836800000000000000⟩
theorem scalar7_32 {x : ℝ}
    (hl : (low2 : ℝ)≤x) (hu : x≤(top2 : ℝ)) : evalR q7_32 x≤AMW.Cert.wfun x := by
  apply check_sound q7_32 base2 top2 low2 hull2
  · norm_num [q7_32]
  · decide +kernel
  · exact (by norm_num [base2,low2] : (base2 : ℝ)≤(low2 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_32
def q7_33 : Quad := ⟨(3075329 : ℚ)/500000000, (-10575473681461 : ℚ)/262144000000000, (2823063505727282092309957 : ℚ)/42949672960000000000000000⟩
theorem scalar7_33 {x : ℝ}
    (hl : (low3 : ℝ)≤x) (hu : x≤(top3 : ℝ)) : evalR q7_33 x≤AMW.Cert.wfun x := by
  apply check_sound q7_33 base3 top3 low3 hull3
  · norm_num [q7_33]
  · decide +kernel
  · exact (by norm_num [base3,low3] : (base3 : ℝ)≤(low3 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_33
def q7_34 : Quad := ⟨(1761741 : ℚ)/1000000000, (-10146894275789 : ℚ)/524288000000000, (905544837747995896446773 : ℚ)/17179869184000000000000000⟩
theorem scalar7_34 {x : ℝ}
    (hl : (low5 : ℝ)≤x) (hu : x≤(top5 : ℝ)) : evalR q7_34 x≤AMW.Cert.wfun x := by
  apply check_sound q7_34 base5 top5 low5 hull5
  · norm_num [q7_34]
  · decide +kernel
  · exact (by norm_num [base5,low5] : (base5 : ℝ)≤(low5 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_34
def q7_35 : Quad := ⟨(46328189 : ℚ)/1000000000, (-34957373504981 : ℚ)/262144000000000, (382510542936394401096149 : ℚ)/4294967296000000000000000⟩
theorem scalar7_35 {x : ℝ}
    (hl : (low1 : ℝ)≤x) (hu : x≤(top1 : ℝ)) : evalR q7_35 x≤AMW.Cert.wfun x := by
  apply check_sound q7_35 base1 top1 low1 hull1
  · norm_num [q7_35]
  · decide +kernel
  · exact (by norm_num [base1,low1] : (base1 : ℝ)≤(low1 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_35
def q7_36 : Quad := ⟨(3075329 : ℚ)/500000000, (-5207696983583 : ℚ)/131072000000000, (686047062470740408800493 : ℚ)/10737418240000000000000000⟩
theorem scalar7_36 {x : ℝ}
    (hl : (low3 : ℝ)≤x) (hu : x≤(top3 : ℝ)) : evalR q7_36 x≤AMW.Cert.wfun x := by
  apply check_sound q7_36 base3 top3 low3 hull3
  · norm_num [q7_36]
  · decide +kernel
  · exact (by norm_num [base3,low3] : (base3 : ℝ)≤(low3 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_36
def q7_37 : Quad := ⟨(17729401 : ℚ)/1000000000, (-13031528498651 : ℚ)/131072000000000, (688235030750239414734989 : ℚ)/5368709120000000000000000⟩
theorem scalar7_37 {x : ℝ}
    (hl : (low2 : ℝ)≤x) (hu : x≤(top2 : ℝ)) : evalR q7_37 x≤AMW.Cert.wfun x := by
  apply check_sound q7_37 base2 top2 low2 hull2
  · norm_num [q7_37]
  · decide +kernel
  · exact (by norm_num [base2,low2] : (base2 : ℝ)≤(low2 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_37
def q7_38 : Quad := ⟨(46328189 : ℚ)/1000000000, (-74181541667299 : ℚ)/524288000000000, (8376936086431403580349497 : ℚ)/85899345920000000000000000⟩
theorem scalar7_38 {x : ℝ}
    (hl : (low1 : ℝ)≤x) (hu : x≤(top1 : ℝ)) : evalR q7_38 x≤AMW.Cert.wfun x := by
  apply check_sound q7_38 base1 top1 low1 hull1
  · norm_num [q7_38]
  · decide +kernel
  · exact (by norm_num [base1,low1] : (base1 : ℝ)≤(low1 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_38
end StructuralW10Followup20261016.Scalar
end
