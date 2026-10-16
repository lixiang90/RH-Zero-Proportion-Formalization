/- SPDX-License-Identifier: Apache-2.0
Generated concrete scalar data; check the matching kernel receipts.
No global coverage is asserted.
-/
import StructuralW10Followup20261016.scalar_Basin7
import StructuralW10Unconditional20261016.BasinPolynomials
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralW10Followup20261016.Scalar
open scoped BigOperators
open Zeta23Ext.BridgeW Zeta23Ext.Bridge
open StructuralW10Unconditional20261016
open StructuralResearch20261016.W10RefinedCandidate
def spans7 (g : Fin 9 → ℝ) : Fin 39 → ℝ := ![(g 0), (g 0+g 1+g 2+g 3+g 4), (g 0+g 1+g 2+g 3+g 4+g 5), (g 0+g 1+g 2+g 3+g 4+g 5+g 6), (g 0+g 1+g 2+g 3+g 4+g 5+g 6+g 7), (g 0+g 1+g 2+g 3+g 4+g 5+g 6+g 7+g 8), (g 1), (g 1+g 2), (g 1+g 2+g 3), (g 1+g 2+g 3+g 4), (g 1+g 2+g 3+g 4+g 5), (g 1+g 2+g 3+g 4+g 5+g 6), (g 1+g 2+g 3+g 4+g 5+g 6+g 7), (g 1+g 2+g 3+g 4+g 5+g 6+g 7+g 8), (g 2), (g 2+g 3), (g 2+g 3+g 4), (g 2+g 3+g 4+g 5), (g 2+g 3+g 4+g 5+g 6), (g 2+g 3+g 4+g 5+g 6+g 7), (g 2+g 3+g 4+g 5+g 6+g 7+g 8), (g 3), (g 3+g 4), (g 3+g 4+g 5), (g 3+g 4+g 5+g 6), (g 3+g 4+g 5+g 6+g 7), (g 3+g 4+g 5+g 6+g 7+g 8), (g 4), (g 4+g 5), (g 4+g 5+g 6), (g 4+g 5+g 6+g 7), (g 4+g 5+g 6+g 7+g 8), (g 5), (g 5+g 6), (g 5+g 6+g 7), (g 6), (g 6+g 7), (g 7), (g 8)]
def lows7 : Fin 39 → ℚ := ![low2, low7, low9, low10, low12, low13, low1, low3, low4, low5, low7, low8, low10, low11, low2, low3, low4, low6, low7, low9, low10, low1, low2, low4, low5, low7, low8, low1, low3, low4, low6, low7, low2, low3, low5, low1, low3, low2, low1]
def tops7 : Fin 39 → ℚ := ![top2, top7, top9, top10, top12, top13, top1, top3, top4, top5, top7, top8, top10, top11, top2, top3, top4, top6, top7, top9, top10, top1, top2, top4, top5, top7, top8, top1, top3, top4, top6, top7, top2, top3, top5, top1, top3, top2, top1]
def Basin7 (g : Fin 9 → ℝ) : Prop := ∀ z, (lows7 z : ℝ) ≤ spans7 g z ∧ spans7 g z ≤ (tops7 z : ℝ)
def qsum7 (g : Fin 9 → ℝ) : ℝ := ((1960353 : ℝ)/10000000000)*g 0+((3889123 : ℝ)/10000000000)*g 1+((2714469 : ℝ)/5000000000)*g 2+((3482077 : ℝ)/5000000000)*g 3+((1878397 : ℝ)/2500000000)*g 4+((3482077 : ℝ)/5000000000)*g 5+((2714469 : ℝ)/5000000000)*g 6+((3889123 : ℝ)/10000000000)*g 7+((1960353 : ℝ)/10000000000)*g 8+((34240949 : ℝ)/400000000)*evalR q7_0 (g 0)+((607788911 : ℝ)/2500000000)*evalR q7_1 (g 0+g 1+g 2+g 3+g 4)+((3135794589 : ℝ)/5000000000)*evalR q7_2 (g 0+g 1+g 2+g 3+g 4+g 5)+((6414869991 : ℝ)/10000000000)*evalR q7_3 (g 0+g 1+g 2+g 3+g 4+g 5+g 6)+((1 : ℝ)/1)*evalR q7_4 (g 0+g 1+g 2+g 3+g 4+g 5+g 6+g 7)+((2 : ℝ)/1)*evalR q7_5 (g 0+g 1+g 2+g 3+g 4+g 5+g 6+g 7+g 8)+((884985069 : ℝ)/5000000000)*evalR q7_6 (g 1)+((1139482463 : ℝ)/10000000000)*evalR q7_7 (g 1+g 2)+((751405669 : ℝ)/2500000000)*evalR q7_8 (g 1+g 2+g 3)+((1593572039 : ℝ)/5000000000)*evalR q7_9 (g 1+g 2+g 3+g 4)+((2739538067 : ℝ)/5000000000)*evalR q7_10 (g 1+g 2+g 3+g 4+g 5)+((3728410821 : ℝ)/10000000000)*evalR q7_11 (g 1+g 2+g 3+g 4+g 5+g 6)+((7170260017 : ℝ)/10000000000)*evalR q7_12 (g 1+g 2+g 3+g 4+g 5+g 6+g 7)+((1 : ℝ)/1)*evalR q7_13 (g 1+g 2+g 3+g 4+g 5+g 6+g 7+g 8)+((1246308147 : ℝ)/5000000000)*evalR q7_14 (g 2)+((1870568449 : ℝ)/5000000000)*evalR q7_15 (g 2+g 3)+((4658843169 : ℝ)/10000000000)*evalR q7_16 (g 2+g 3+g 4)+((6812855921 : ℝ)/10000000000)*evalR q7_17 (g 2+g 3+g 4+g 5)+((4179536443 : ℝ)/10000000000)*evalR q7_18 (g 2+g 3+g 4+g 5+g 6)+((3728410821 : ℝ)/10000000000)*evalR q7_19 (g 2+g 3+g 4+g 5+g 6+g 7)+((6414869991 : ℝ)/10000000000)*evalR q7_20 (g 2+g 3+g 4+g 5+g 6+g 7+g 8)+((318472471 : ℝ)/1000000000)*evalR q7_21 (g 3)+((2559690319 : ℝ)/5000000000)*evalR q7_22 (g 3+g 4)+((2335534153 : ℝ)/5000000000)*evalR q7_23 (g 3+g 4+g 5)+((6812855921 : ℝ)/10000000000)*evalR q7_24 (g 3+g 4+g 5+g 6)+((2739538067 : ℝ)/5000000000)*evalR q7_25 (g 3+g 4+g 5+g 6+g 7)+((3135794589 : ℝ)/5000000000)*evalR q7_26 (g 3+g 4+g 5+g 6+g 7+g 8)+((3393330261 : ℝ)/10000000000)*evalR q7_27 (g 4)+((2559690319 : ℝ)/5000000000)*evalR q7_28 (g 4+g 5)+((4658843169 : ℝ)/10000000000)*evalR q7_29 (g 4+g 5+g 6)+((1593572039 : ℝ)/5000000000)*evalR q7_30 (g 4+g 5+g 6+g 7)+((607788911 : ℝ)/2500000000)*evalR q7_31 (g 4+g 5+g 6+g 7+g 8)+((318472471 : ℝ)/1000000000)*evalR q7_32 (g 5)+((1870568449 : ℝ)/5000000000)*evalR q7_33 (g 5+g 6)+((751405669 : ℝ)/2500000000)*evalR q7_34 (g 5+g 6+g 7)+((1246308147 : ℝ)/5000000000)*evalR q7_35 (g 6)+((1139482463 : ℝ)/10000000000)*evalR q7_36 (g 6+g 7)+((884985069 : ℝ)/5000000000)*evalR q7_37 (g 7)+((34240949 : ℝ)/400000000)*evalR q7_38 (g 8)
def rest7 (g : Fin 9 → ℝ) : ℝ := ((206281733026667 : ℝ)/2500000000000000000)*((g 0+g 1+g 2+g 3+g 4)-((1846189 : ℝ)/262144))^2+((397001002351167 : ℝ)/2500000000000000000)*((g 0+g 1+g 2+g 3+g 4+g 5)-((9443191 : ℝ)/1048576))^2+((2949088936352457 : ℝ)/10000000000000000000)*((g 0+g 1+g 2+g 3+g 4+g 5+g 6)-((10535401 : ℝ)/1048576))^2+((69949 : ℝ)/125000000)*((g 0+g 1+g 2+g 3+g 4+g 5+g 6+g 7)-((12598709 : ℝ)/1048576))^2+((116941 : ℝ)/125000000)*((g 0+g 1+g 2+g 3+g 4+g 5+g 6+g 7+g 8)-((3421477 : ℝ)/262144))^2+((3504283463455327 : ℝ)/5000000000000000000)*((g 1+g 2)-((3148625 : ℝ)/1048576))^2+((1631296447559317 : ℝ)/2500000000000000000)*((g 1+g 2+g 3)-((1058167 : ℝ)/262144))^2+((2807461197559899 : ℝ)/5000000000000000000)*((g 1+g 2+g 3+g 4)-((5317337 : ℝ)/1048576))^2+((929791001325599 : ℝ)/5000000000000000000)*((g 1+g 2+g 3+g 4+g 5)-((1843943 : ℝ)/262144))^2+((321094468315341 : ℝ)/2000000000000000000)*((g 1+g 2+g 3+g 4+g 5+g 6)-((4233991 : ℝ)/524288))^2+((3296362126835359 : ℝ)/10000000000000000000)*((g 1+g 2+g 3+g 4+g 5+g 6+g 7)-((5265645 : ℝ)/524288))^2+((152881 : ℝ)/250000000)*((g 1+g 2+g 3+g 4+g 5+g 6+g 7+g 8)-((11618489 : ℝ)/1048576))^2+((5752613397694721 : ℝ)/2500000000000000000)*((g 2+g 3)-((3141423 : ℝ)/1048576))^2+((10114315907996817 : ℝ)/10000000000000000000)*((g 2+g 3+g 4)-((1056523 : ℝ)/262144))^2+((4214521239857573 : ℝ)/10000000000000000000)*((g 2+g 3+g 4+g 5)-((6284527 : ℝ)/1048576))^2+((1418522130144871 : ℝ)/10000000000000000000)*((g 2+g 3+g 4+g 5+g 6)-((7376737 : ℝ)/1048576))^2+((472027995171063 : ℝ)/5000000000000000000)*((g 2+g 3+g 4+g 5+g 6+g 7)-((9440045 : ℝ)/1048576))^2+((2949088936352457 : ℝ)/10000000000000000000)*((g 2+g 3+g 4+g 5+g 6+g 7+g 8)-((2631811 : ℝ)/262144))^2+((45381776101368919 : ℝ)/5000000000000000000)*((g 3+g 4)-((271089 : ℝ)/131072))^2+((5070428297423929 : ℝ)/5000000000000000000)*((g 3+g 4+g 5)-((4227147 : ℝ)/1048576))^2+((12002487603118461 : ℝ)/10000000000000000000)*((g 3+g 4+g 5+g 6)-((5319357 : ℝ)/1048576))^2+((929791001325599 : ℝ)/5000000000000000000)*((g 3+g 4+g 5+g 6+g 7)-((7382665 : ℝ)/1048576))^2+((270057765799269 : ℝ)/1000000000000000000)*((g 3+g 4+g 5+g 6+g 7+g 8)-((1058733 : ℝ)/131072))^2+((7871889869039951 : ℝ)/2500000000000000000)*((g 4+g 5)-((49111 : ℝ)/16384))^2+((10114315907996817 : ℝ)/10000000000000000000)*((g 4+g 5+g 6)-((2117657 : ℝ)/524288))^2+((985804379761907 : ℝ)/5000000000000000000)*((g 4+g 5+g 6+g 7)-((3149311 : ℝ)/524288))^2+((206281733026667 : ℝ)/2500000000000000000)*((g 4+g 5+g 6+g 7+g 8)-((7385821 : ℝ)/1048576))^2+((5752613397694721 : ℝ)/2500000000000000000)*((g 5+g 6)-((3150645 : ℝ)/1048576))^2+((1323782174709729 : ℝ)/2500000000000000000)*((g 5+g 6+g 7)-((5213953 : ℝ)/1048576))^2+((3504283463455327 : ℝ)/5000000000000000000)*((g 6+g 7)-((1577759 : ℝ)/524288))^2
def anchor7 : Fin 9 → ℝ := ![(2067419 : ℝ)/1048576, (1091245 : ℝ)/1048576, (514345 : ℝ)/262144, (1084043 : ℝ)/1048576, (1084669 : ℝ)/1048576, (2058435 : ℝ)/1048576, (546105 : ℝ)/524288, (515827 : ℝ)/262144, (1087199 : ℝ)/1048576]
theorem sum9 (f : Fin 9 → ℝ) : (∑ i, f i)=f 0+(f 1+(f 2+(f 3+(f 4+(f 5+(f 6+(f 7+(f 8+(0))))))))) := by
  simp only [Fin.sum_univ_succ]
  rfl
theorem fw_expanded7 (g : Fin 9 → ℝ) : Fw W g = ((1960353 : ℝ)/10000000000)*g 0+((3889123 : ℝ)/10000000000)*g 1+((2714469 : ℝ)/5000000000)*g 2+((3482077 : ℝ)/5000000000)*g 3+((1878397 : ℝ)/2500000000)*g 4+((3482077 : ℝ)/5000000000)*g 5+((2714469 : ℝ)/5000000000)*g 6+((3889123 : ℝ)/10000000000)*g 7+((1960353 : ℝ)/10000000000)*g 8+((34240949 : ℝ)/400000000)*AMW.Cert.wfun (g 0)+((607788911 : ℝ)/2500000000)*AMW.Cert.wfun (g 0+g 1+g 2+g 3+g 4)+((3135794589 : ℝ)/5000000000)*AMW.Cert.wfun (g 0+g 1+g 2+g 3+g 4+g 5)+((6414869991 : ℝ)/10000000000)*AMW.Cert.wfun (g 0+g 1+g 2+g 3+g 4+g 5+g 6)+((1 : ℝ)/1)*AMW.Cert.wfun (g 0+g 1+g 2+g 3+g 4+g 5+g 6+g 7)+((2 : ℝ)/1)*AMW.Cert.wfun (g 0+g 1+g 2+g 3+g 4+g 5+g 6+g 7+g 8)+((884985069 : ℝ)/5000000000)*AMW.Cert.wfun (g 1)+((1139482463 : ℝ)/10000000000)*AMW.Cert.wfun (g 1+g 2)+((751405669 : ℝ)/2500000000)*AMW.Cert.wfun (g 1+g 2+g 3)+((1593572039 : ℝ)/5000000000)*AMW.Cert.wfun (g 1+g 2+g 3+g 4)+((2739538067 : ℝ)/5000000000)*AMW.Cert.wfun (g 1+g 2+g 3+g 4+g 5)+((3728410821 : ℝ)/10000000000)*AMW.Cert.wfun (g 1+g 2+g 3+g 4+g 5+g 6)+((7170260017 : ℝ)/10000000000)*AMW.Cert.wfun (g 1+g 2+g 3+g 4+g 5+g 6+g 7)+((1 : ℝ)/1)*AMW.Cert.wfun (g 1+g 2+g 3+g 4+g 5+g 6+g 7+g 8)+((1246308147 : ℝ)/5000000000)*AMW.Cert.wfun (g 2)+((1870568449 : ℝ)/5000000000)*AMW.Cert.wfun (g 2+g 3)+((4658843169 : ℝ)/10000000000)*AMW.Cert.wfun (g 2+g 3+g 4)+((6812855921 : ℝ)/10000000000)*AMW.Cert.wfun (g 2+g 3+g 4+g 5)+((4179536443 : ℝ)/10000000000)*AMW.Cert.wfun (g 2+g 3+g 4+g 5+g 6)+((3728410821 : ℝ)/10000000000)*AMW.Cert.wfun (g 2+g 3+g 4+g 5+g 6+g 7)+((6414869991 : ℝ)/10000000000)*AMW.Cert.wfun (g 2+g 3+g 4+g 5+g 6+g 7+g 8)+((318472471 : ℝ)/1000000000)*AMW.Cert.wfun (g 3)+((2559690319 : ℝ)/5000000000)*AMW.Cert.wfun (g 3+g 4)+((2335534153 : ℝ)/5000000000)*AMW.Cert.wfun (g 3+g 4+g 5)+((6812855921 : ℝ)/10000000000)*AMW.Cert.wfun (g 3+g 4+g 5+g 6)+((2739538067 : ℝ)/5000000000)*AMW.Cert.wfun (g 3+g 4+g 5+g 6+g 7)+((3135794589 : ℝ)/5000000000)*AMW.Cert.wfun (g 3+g 4+g 5+g 6+g 7+g 8)+((3393330261 : ℝ)/10000000000)*AMW.Cert.wfun (g 4)+((2559690319 : ℝ)/5000000000)*AMW.Cert.wfun (g 4+g 5)+((4658843169 : ℝ)/10000000000)*AMW.Cert.wfun (g 4+g 5+g 6)+((1593572039 : ℝ)/5000000000)*AMW.Cert.wfun (g 4+g 5+g 6+g 7)+((607788911 : ℝ)/2500000000)*AMW.Cert.wfun (g 4+g 5+g 6+g 7+g 8)+((318472471 : ℝ)/1000000000)*AMW.Cert.wfun (g 5)+((1870568449 : ℝ)/5000000000)*AMW.Cert.wfun (g 5+g 6)+((751405669 : ℝ)/2500000000)*AMW.Cert.wfun (g 5+g 6+g 7)+((1246308147 : ℝ)/5000000000)*AMW.Cert.wfun (g 6)+((1139482463 : ℝ)/10000000000)*AMW.Cert.wfun (g 6+g 7)+((884985069 : ℝ)/5000000000)*AMW.Cert.wfun (g 7)+((34240949 : ℝ)/400000000)*AMW.Cert.wfun (g 8) := by
  simp [RiemannFail.cert_wfun_eq, Fw, W, a, b, aN, bN,
    ptsN, Fin.sum_univ_succ, Finset.sum_range_succ, Finset.sum_Ico_succ_top]
  ring
theorem qsum_identity7 (g : Fin 9 → ℝ) : qsum7 g =
    BasinPolynomials.C7+(∑ i, (BasinPolynomials.b7 i*(g i-anchor7 i)+
      BasinPolynomials.d7 i*(g i-anchor7 i)^2))+rest7 g := by
  rw [sum9]
  change qsum7 g = BasinPolynomials.C7+((((6178037464551 : ℝ) / 250000000000000000)*(g 0-((2067419 : ℝ)/1048576))+((607071515441549 : ℝ) / 400000000000000000)*(g 0-((2067419 : ℝ)/1048576))^2)+((((294736392840573 : ℝ) / 2500000000000000000)*(g 1-((1091245 : ℝ)/1048576))+((40999755538810041 : ℝ) / 5000000000000000000)*(g 1-((1091245 : ℝ)/1048576))^2)+((((141112488586843 : ℝ) / 10000000000000000000)*(g 2-((514345 : ℝ)/262144))+((22096296907729947 : ℝ) / 5000000000000000000)*(g 2-((514345 : ℝ)/262144))^2)+((((512791939477393 : ℝ) / 2000000000000000000)*(g 3-((1084043 : ℝ)/1048576))+((14754252827785019 : ℝ) / 1000000000000000000)*(g 3-((1084043 : ℝ)/1048576))^2)+((((-1280774998901463 : ℝ) / 10000000000000000000)*(g 4-((1084669 : ℝ)/1048576))+((157206845671027329 : ℝ) / 10000000000000000000)*(g 4-((1084669 : ℝ)/1048576))^2)+((((-103719595347149 : ℝ) / 10000000000000000000)*(g 5-((2058435 : ℝ)/1048576))+((5646326145819871 : ℝ) / 1000000000000000000)*(g 5-((2058435 : ℝ)/1048576))^2)+((((2180112447794061 : ℝ) / 10000000000000000000)*(g 6-((546105 : ℝ)/524288))+((57739199386455783 : ℝ) / 5000000000000000000)*(g 6-((546105 : ℝ)/524288))^2)+((((625485599729 : ℝ) / 15625000000000000)*(g 7-((515827 : ℝ)/262144))+((15690255167313669 : ℝ) / 5000000000000000000)*(g 7-((515827 : ℝ)/262144))^2)+((((142529561947157 : ℝ) / 2000000000000000000)*(g 8-((1087199 : ℝ)/1048576))+((1586321156811361 : ℝ) / 400000000000000000)*(g 8-((1087199 : ℝ)/1048576))^2)+(0))))))))))+rest7 g
  norm_num [qsum7, rest7, evalR,q7_0,q7_1,q7_2,q7_3,q7_4,q7_5,q7_6,q7_7,q7_8,q7_9,q7_10,q7_11,q7_12,q7_13,q7_14,q7_15,q7_16,q7_17,q7_18,q7_19,q7_20,q7_21,q7_22,q7_23,q7_24,q7_25,q7_26,q7_27,q7_28,q7_29,q7_30,q7_31,q7_32,q7_33,q7_34,q7_35,q7_36,q7_37,q7_38,BasinPolynomials.C7]
  ring

theorem actual_Fw_basin7 (g : Fin 9 → ℝ) (h : Basin7 g) :
    (433 : ℝ)/50000≤Fw W g := by
  have hh0 : (low2 : ℝ)≤(g 0) ∧ (g 0)≤(top2 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨0,by decide⟩
  have hs0 := mul_le_mul_of_nonneg_left (scalar7_0 hh0.1 hh0.2) (by norm_num : (0 : ℝ)≤((34240949 : ℝ)/400000000))
  have hh1 : (low7 : ℝ)≤(g 0+g 1+g 2+g 3+g 4) ∧ (g 0+g 1+g 2+g 3+g 4)≤(top7 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨1,by decide⟩
  have hs1 := mul_le_mul_of_nonneg_left (scalar7_1 hh1.1 hh1.2) (by norm_num : (0 : ℝ)≤((607788911 : ℝ)/2500000000))
  have hh2 : (low9 : ℝ)≤(g 0+g 1+g 2+g 3+g 4+g 5) ∧ (g 0+g 1+g 2+g 3+g 4+g 5)≤(top9 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨2,by decide⟩
  have hs2 := mul_le_mul_of_nonneg_left (scalar7_2 hh2.1 hh2.2) (by norm_num : (0 : ℝ)≤((3135794589 : ℝ)/5000000000))
  have hh3 : (low10 : ℝ)≤(g 0+g 1+g 2+g 3+g 4+g 5+g 6) ∧ (g 0+g 1+g 2+g 3+g 4+g 5+g 6)≤(top10 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨3,by decide⟩
  have hs3 := mul_le_mul_of_nonneg_left (scalar7_3 hh3.1 hh3.2) (by norm_num : (0 : ℝ)≤((6414869991 : ℝ)/10000000000))
  have hh4 : (low12 : ℝ)≤(g 0+g 1+g 2+g 3+g 4+g 5+g 6+g 7) ∧ (g 0+g 1+g 2+g 3+g 4+g 5+g 6+g 7)≤(top12 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨4,by decide⟩
  have hs4 := mul_le_mul_of_nonneg_left (scalar7_4 hh4.1 hh4.2) (by norm_num : (0 : ℝ)≤((1 : ℝ)/1))
  have hh5 : (low13 : ℝ)≤(g 0+g 1+g 2+g 3+g 4+g 5+g 6+g 7+g 8) ∧ (g 0+g 1+g 2+g 3+g 4+g 5+g 6+g 7+g 8)≤(top13 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨5,by decide⟩
  have hs5 := mul_le_mul_of_nonneg_left (scalar7_5 hh5.1 hh5.2) (by norm_num : (0 : ℝ)≤((2 : ℝ)/1))
  have hh6 : (low1 : ℝ)≤(g 1) ∧ (g 1)≤(top1 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨6,by decide⟩
  have hs6 := mul_le_mul_of_nonneg_left (scalar7_6 hh6.1 hh6.2) (by norm_num : (0 : ℝ)≤((884985069 : ℝ)/5000000000))
  have hh7 : (low3 : ℝ)≤(g 1+g 2) ∧ (g 1+g 2)≤(top3 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨7,by decide⟩
  have hs7 := mul_le_mul_of_nonneg_left (scalar7_7 hh7.1 hh7.2) (by norm_num : (0 : ℝ)≤((1139482463 : ℝ)/10000000000))
  have hh8 : (low4 : ℝ)≤(g 1+g 2+g 3) ∧ (g 1+g 2+g 3)≤(top4 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨8,by decide⟩
  have hs8 := mul_le_mul_of_nonneg_left (scalar7_8 hh8.1 hh8.2) (by norm_num : (0 : ℝ)≤((751405669 : ℝ)/2500000000))
  have hh9 : (low5 : ℝ)≤(g 1+g 2+g 3+g 4) ∧ (g 1+g 2+g 3+g 4)≤(top5 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨9,by decide⟩
  have hs9 := mul_le_mul_of_nonneg_left (scalar7_9 hh9.1 hh9.2) (by norm_num : (0 : ℝ)≤((1593572039 : ℝ)/5000000000))
  have hh10 : (low7 : ℝ)≤(g 1+g 2+g 3+g 4+g 5) ∧ (g 1+g 2+g 3+g 4+g 5)≤(top7 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨10,by decide⟩
  have hs10 := mul_le_mul_of_nonneg_left (scalar7_10 hh10.1 hh10.2) (by norm_num : (0 : ℝ)≤((2739538067 : ℝ)/5000000000))
  have hh11 : (low8 : ℝ)≤(g 1+g 2+g 3+g 4+g 5+g 6) ∧ (g 1+g 2+g 3+g 4+g 5+g 6)≤(top8 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨11,by decide⟩
  have hs11 := mul_le_mul_of_nonneg_left (scalar7_11 hh11.1 hh11.2) (by norm_num : (0 : ℝ)≤((3728410821 : ℝ)/10000000000))
  have hh12 : (low10 : ℝ)≤(g 1+g 2+g 3+g 4+g 5+g 6+g 7) ∧ (g 1+g 2+g 3+g 4+g 5+g 6+g 7)≤(top10 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨12,by decide⟩
  have hs12 := mul_le_mul_of_nonneg_left (scalar7_12 hh12.1 hh12.2) (by norm_num : (0 : ℝ)≤((7170260017 : ℝ)/10000000000))
  have hh13 : (low11 : ℝ)≤(g 1+g 2+g 3+g 4+g 5+g 6+g 7+g 8) ∧ (g 1+g 2+g 3+g 4+g 5+g 6+g 7+g 8)≤(top11 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨13,by decide⟩
  have hs13 := mul_le_mul_of_nonneg_left (scalar7_13 hh13.1 hh13.2) (by norm_num : (0 : ℝ)≤((1 : ℝ)/1))
  have hh14 : (low2 : ℝ)≤(g 2) ∧ (g 2)≤(top2 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨14,by decide⟩
  have hs14 := mul_le_mul_of_nonneg_left (scalar7_14 hh14.1 hh14.2) (by norm_num : (0 : ℝ)≤((1246308147 : ℝ)/5000000000))
  have hh15 : (low3 : ℝ)≤(g 2+g 3) ∧ (g 2+g 3)≤(top3 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨15,by decide⟩
  have hs15 := mul_le_mul_of_nonneg_left (scalar7_15 hh15.1 hh15.2) (by norm_num : (0 : ℝ)≤((1870568449 : ℝ)/5000000000))
  have hh16 : (low4 : ℝ)≤(g 2+g 3+g 4) ∧ (g 2+g 3+g 4)≤(top4 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨16,by decide⟩
  have hs16 := mul_le_mul_of_nonneg_left (scalar7_16 hh16.1 hh16.2) (by norm_num : (0 : ℝ)≤((4658843169 : ℝ)/10000000000))
  have hh17 : (low6 : ℝ)≤(g 2+g 3+g 4+g 5) ∧ (g 2+g 3+g 4+g 5)≤(top6 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨17,by decide⟩
  have hs17 := mul_le_mul_of_nonneg_left (scalar7_17 hh17.1 hh17.2) (by norm_num : (0 : ℝ)≤((6812855921 : ℝ)/10000000000))
  have hh18 : (low7 : ℝ)≤(g 2+g 3+g 4+g 5+g 6) ∧ (g 2+g 3+g 4+g 5+g 6)≤(top7 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨18,by decide⟩
  have hs18 := mul_le_mul_of_nonneg_left (scalar7_18 hh18.1 hh18.2) (by norm_num : (0 : ℝ)≤((4179536443 : ℝ)/10000000000))
  have hh19 : (low9 : ℝ)≤(g 2+g 3+g 4+g 5+g 6+g 7) ∧ (g 2+g 3+g 4+g 5+g 6+g 7)≤(top9 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨19,by decide⟩
  have hs19 := mul_le_mul_of_nonneg_left (scalar7_19 hh19.1 hh19.2) (by norm_num : (0 : ℝ)≤((3728410821 : ℝ)/10000000000))
  have hh20 : (low10 : ℝ)≤(g 2+g 3+g 4+g 5+g 6+g 7+g 8) ∧ (g 2+g 3+g 4+g 5+g 6+g 7+g 8)≤(top10 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨20,by decide⟩
  have hs20 := mul_le_mul_of_nonneg_left (scalar7_20 hh20.1 hh20.2) (by norm_num : (0 : ℝ)≤((6414869991 : ℝ)/10000000000))
  have hh21 : (low1 : ℝ)≤(g 3) ∧ (g 3)≤(top1 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨21,by decide⟩
  have hs21 := mul_le_mul_of_nonneg_left (scalar7_21 hh21.1 hh21.2) (by norm_num : (0 : ℝ)≤((318472471 : ℝ)/1000000000))
  have hh22 : (low2 : ℝ)≤(g 3+g 4) ∧ (g 3+g 4)≤(top2 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨22,by decide⟩
  have hs22 := mul_le_mul_of_nonneg_left (scalar7_22 hh22.1 hh22.2) (by norm_num : (0 : ℝ)≤((2559690319 : ℝ)/5000000000))
  have hh23 : (low4 : ℝ)≤(g 3+g 4+g 5) ∧ (g 3+g 4+g 5)≤(top4 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨23,by decide⟩
  have hs23 := mul_le_mul_of_nonneg_left (scalar7_23 hh23.1 hh23.2) (by norm_num : (0 : ℝ)≤((2335534153 : ℝ)/5000000000))
  have hh24 : (low5 : ℝ)≤(g 3+g 4+g 5+g 6) ∧ (g 3+g 4+g 5+g 6)≤(top5 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨24,by decide⟩
  have hs24 := mul_le_mul_of_nonneg_left (scalar7_24 hh24.1 hh24.2) (by norm_num : (0 : ℝ)≤((6812855921 : ℝ)/10000000000))
  have hh25 : (low7 : ℝ)≤(g 3+g 4+g 5+g 6+g 7) ∧ (g 3+g 4+g 5+g 6+g 7)≤(top7 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨25,by decide⟩
  have hs25 := mul_le_mul_of_nonneg_left (scalar7_25 hh25.1 hh25.2) (by norm_num : (0 : ℝ)≤((2739538067 : ℝ)/5000000000))
  have hh26 : (low8 : ℝ)≤(g 3+g 4+g 5+g 6+g 7+g 8) ∧ (g 3+g 4+g 5+g 6+g 7+g 8)≤(top8 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨26,by decide⟩
  have hs26 := mul_le_mul_of_nonneg_left (scalar7_26 hh26.1 hh26.2) (by norm_num : (0 : ℝ)≤((3135794589 : ℝ)/5000000000))
  have hh27 : (low1 : ℝ)≤(g 4) ∧ (g 4)≤(top1 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨27,by decide⟩
  have hs27 := mul_le_mul_of_nonneg_left (scalar7_27 hh27.1 hh27.2) (by norm_num : (0 : ℝ)≤((3393330261 : ℝ)/10000000000))
  have hh28 : (low3 : ℝ)≤(g 4+g 5) ∧ (g 4+g 5)≤(top3 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨28,by decide⟩
  have hs28 := mul_le_mul_of_nonneg_left (scalar7_28 hh28.1 hh28.2) (by norm_num : (0 : ℝ)≤((2559690319 : ℝ)/5000000000))
  have hh29 : (low4 : ℝ)≤(g 4+g 5+g 6) ∧ (g 4+g 5+g 6)≤(top4 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨29,by decide⟩
  have hs29 := mul_le_mul_of_nonneg_left (scalar7_29 hh29.1 hh29.2) (by norm_num : (0 : ℝ)≤((4658843169 : ℝ)/10000000000))
  have hh30 : (low6 : ℝ)≤(g 4+g 5+g 6+g 7) ∧ (g 4+g 5+g 6+g 7)≤(top6 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨30,by decide⟩
  have hs30 := mul_le_mul_of_nonneg_left (scalar7_30 hh30.1 hh30.2) (by norm_num : (0 : ℝ)≤((1593572039 : ℝ)/5000000000))
  have hh31 : (low7 : ℝ)≤(g 4+g 5+g 6+g 7+g 8) ∧ (g 4+g 5+g 6+g 7+g 8)≤(top7 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨31,by decide⟩
  have hs31 := mul_le_mul_of_nonneg_left (scalar7_31 hh31.1 hh31.2) (by norm_num : (0 : ℝ)≤((607788911 : ℝ)/2500000000))
  have hh32 : (low2 : ℝ)≤(g 5) ∧ (g 5)≤(top2 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨32,by decide⟩
  have hs32 := mul_le_mul_of_nonneg_left (scalar7_32 hh32.1 hh32.2) (by norm_num : (0 : ℝ)≤((318472471 : ℝ)/1000000000))
  have hh33 : (low3 : ℝ)≤(g 5+g 6) ∧ (g 5+g 6)≤(top3 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨33,by decide⟩
  have hs33 := mul_le_mul_of_nonneg_left (scalar7_33 hh33.1 hh33.2) (by norm_num : (0 : ℝ)≤((1870568449 : ℝ)/5000000000))
  have hh34 : (low5 : ℝ)≤(g 5+g 6+g 7) ∧ (g 5+g 6+g 7)≤(top5 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨34,by decide⟩
  have hs34 := mul_le_mul_of_nonneg_left (scalar7_34 hh34.1 hh34.2) (by norm_num : (0 : ℝ)≤((751405669 : ℝ)/2500000000))
  have hh35 : (low1 : ℝ)≤(g 6) ∧ (g 6)≤(top1 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨35,by decide⟩
  have hs35 := mul_le_mul_of_nonneg_left (scalar7_35 hh35.1 hh35.2) (by norm_num : (0 : ℝ)≤((1246308147 : ℝ)/5000000000))
  have hh36 : (low3 : ℝ)≤(g 6+g 7) ∧ (g 6+g 7)≤(top3 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨36,by decide⟩
  have hs36 := mul_le_mul_of_nonneg_left (scalar7_36 hh36.1 hh36.2) (by norm_num : (0 : ℝ)≤((1139482463 : ℝ)/10000000000))
  have hh37 : (low2 : ℝ)≤(g 7) ∧ (g 7)≤(top2 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨37,by decide⟩
  have hs37 := mul_le_mul_of_nonneg_left (scalar7_37 hh37.1 hh37.2) (by norm_num : (0 : ℝ)≤((884985069 : ℝ)/5000000000))
  have hh38 : (low1 : ℝ)≤(g 8) ∧ (g 8)≤(top1 : ℝ) := by simpa [lows7,tops7,spans7] using h ⟨38,by decide⟩
  have hs38 := mul_le_mul_of_nonneg_left (scalar7_38 hh38.1 hh38.2) (by norm_num : (0 : ℝ)≤((34240949 : ℝ)/400000000))
  have hf : qsum7 g≤Fw W g := by
    rw [fw_expanded7]
    unfold qsum7
    linarith only [hs0,hs1,hs2,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32,hs33,hs34,hs35,hs36,hs37,hs38]
  have hr : 0≤rest7 g := by unfold rest7; positivity
  have hp := BasinPolynomials.lower7 (fun i => g i-anchor7 i)
  rw [qsum_identity7] at hf
  linarith only [hf,hp,hr]
#print axioms actual_Fw_basin7
end StructuralW10Followup20261016.Scalar
end
