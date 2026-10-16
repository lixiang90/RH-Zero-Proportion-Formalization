"""Emit actual new-window trace-to-zero counting base.

The attributed stable-rank and endgame proof is parameter independent except
for its old atAM name; this adapts the proof to the new actual at24, then
discharges analytic inputs using the new proved realization and limits.
"""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
core=(ROOT/'GramDefect20261015/Core.lean').read_text(encoding='utf-8')
start=core.index('theorem endgame_defect (Z : ZeroConfig)')
stop=core.index('\nend Zeta23Ext.Bridge',start)
endgame=core[start:stop].replace('AMW.atAM','WindowRealization.at24')
start=core.index('theorem eventually_h7 (Z : ZeroConfig)')
stop=core.index('\nend Zeta23Ext.Bridge',start)
h7=core[start:stop]
h7=h7.replace('AMW.aAM_range_of','WindowRealization.a_range_of')
h7=h7.replace('AMW.WAM_even','WindowRealization.W_even')
h7=h7.replace('AMW.admWindow_WAM','WindowRealization.admWindow')

head='''/- SPDX-License-Identifier: Apache-2.0
Actual new-window stable-rank trace-to-zero counting base.
Adapted from Zeta23Ext.Bridge.endgame_defect and eventually_h7 in the
attributed Core. The analytic inputs are discharged for the new v24 window.
The local separated/matching defect bound is deliberately not asserted here.
-/
import StructuralGoal20261016.WindowAsymptotic
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Matrix RHLinalg Filter Asymptotics Topology Real
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23.Assembly
open Zeta23Ext.Bridge
namespace StructuralGoal20261016.WindowCountingBase

def P₀ : Params := paramsOf stdProfile 1
theorem P₀_valid : P₀.Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
def mtParams (T : ℝ) : Params := WindowRealization.at24 P₀ T

'''
tail='''
theorem actual_tail_passage (Z : ZeroConfig) (H : PaperInputs Z) :
 ∀ ε > 0, ∀ᶠ T in atTop,
   (WindowEnergy.H 24 WindowKernel.d24 - ε) * (Z.N T (2*T) : ℝ) +
     Dcirc Z (mtParams T) T ≤ (Z.N0s T (2*T) : ℝ) := by
 let P : Params := P₀
 have hP : P.Valid := P₀_valid
 have hFacts := WindowAsymptotic.actual_concreteFacts Z H hP
 have hTr := tracesBoundsD_of_factsD _ hFacts
 have hc : Tendsto
   (fun T => cRatio (P.lam1 T)
     ((AMW.concreteDataW P (WindowRealization.W P) Z).aT T)
     ((AMW.concreteDataW P (WindowRealization.W P) Z).bT T)
     ((AMW.concreteDataW P (WindowRealization.W P) Z).JT T))
   atTop (𝓝 (cRatio P.lam WindowAsymptotic.aInf WindowAsymptotic.bInf WindowAsymptotic.JInf)) :=
   WindowAsymptotic.tendsto_cRatio_W hP
 have hc0 := WindowAsymptotic.cRatio_W_pos hP.lam_pos
 have ha : ∀ᶠ T in atTop,
   1/2 ≤ (AMW.concreteDataW P (WindowRealization.W P) Z).aT T ∧
   (AMW.concreteDataW P (WindowRealization.W P) Z).aT T ≤ 1 :=
   hFacts.ab_range.mono fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
 obtain ⟨θ₀, hTail, hθ₀⟩ := WindowRealization.eventually_tailPackage Z H hP
 obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
 have hNII := Tail.eventually_NII_le Z hA₀ hloc
 have hGzGp := WindowRealization.eventually_GzGp Z H hP
 have hId : ∀ᶠ T in atTop,
   (WindowRealization.at24 P T).trGtilde T =
     (AMW.concreteDataW P (WindowRealization.W P) Z).trG T ∧
   (WindowRealization.at24 P T).trGtildeSq T =
     (AMW.concreteDataW P (WindowRealization.W P) Z).trG2 T ∧
   (WindowRealization.at24 P T).a T =
     (AMW.concreteDataW P (WindowRealization.W P) Z).aT T :=
   Eventually.of_forall fun T => AMW.atW_ident Z hP (WindowRealization.W_even P) T
 have hcalE := Assembly.calE_tendsto_zero P hP.lam_pos hP.lam_le_one
   (zero_le_one.trans hP.one_le_w)
 have h := endgame_defect Z H P hP _ _ _ _ _ hTr hc0 hc ha θ₀
   hTail hθ₀ hNII hGzGp hId hcalE (fun T => Dcirc Z (mtParams T) T) (eventually_h7 Z)
 intro ε hε
 rw [WindowAsymptotic.H24_eq_cRatio]
 exact h ε hε

#print axioms endgame_defect
#print axioms eventually_h7
#print axioms actual_tail_passage
end StructuralGoal20261016.WindowCountingBase
end
'''
out=ROOT/'StructuralGoal20261016/WindowCountingBase.lean'
out.write_text(head+endgame+'\n'+h7+tail,encoding='utf-8',newline='\n')
print(out.relative_to(ROOT),out.stat().st_size)
