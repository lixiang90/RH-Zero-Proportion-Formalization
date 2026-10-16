"""Emit the four actual-new-window counting consumers with explicit inputs."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
old=(ROOT/'GramDefect20261015/RefinedCounting.lean').read_text(encoding='utf8')
a=old.index('theorem defect_to_dyadic');body=old[a:old.index('theorem simple_dyadic',a)]
body=body.replace('AMW.HW','WindowEnergy.H 24 WindowKernel.d24')
body=body.replace('OpethN.Counting.ActualDefectEstimate','WindowCountingDefect.ActualDefectEstimate')
body=body.replace('deleted_strips Z H','WindowCountingGeometry.deleted_strips Z H')
body=body.replace('span_retained_le Z H','WindowCountingGeometry.span_retained_le Z H')
body=body.replace('tail_passage Z H (eventually_h7 Z)','WindowCountingBase.actual_tail_passage Z H')
body=body.replace('mtParams','WindowCountingBase.mtParams')
head='''/- SPDX-License-Identifier: Apache-2.0
The actual new-window dyadic and cumulative zero-counting bridge.
The proof adapts the attributed generic RefinedCounting arithmetic. The
actual Fourier energy, finite-height traces, tail, strips and spectrum are
proved upstream; only the named scalar pair and gap certificates remain.
-/
import StructuralGoal20261016.WindowCountingDefect
import StructuralGoal20261016.WindowCountingGeometry
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Filter Topology Zeta23
open Zeta23Ext.Bridge Zeta23Ext.BridgeW
open scoped BigOperators
namespace StructuralGoal20261016.WindowCounting
open Classical
'''
signature='''{n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
 {c C B hw sep : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hCc : C ≤ c)
 (hc64 : c ≤ 1/64) (hsep : 17/20 ≤ sep)
 (hPair : ∀ t : ℝ, |t| ≤ sep → c ≤ WindowDiscreteEnergy.wfun t)
 (hB : W.B = B) (hfloor : hw ≤ WindowEnergy.H 24 WindowKernel.d24)
 (hCert : WindowDiscreteEnergy.SeparatedSummedCertificate W c C sep)'''
call='hn W hW hc hC hCc hc64 hsep hPair hB hfloor hCert'
body+='theorem simple_dyadic '+signature+''' :
 ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
 ((hw-B)/(1-c)-ε)*(Zeta23.Ncount T (2*T):ℝ) ≤ Zeta23.N0simple T (2*T) := by
 have hB0 : 0 ≤ B := hB ▸ WCert.B_nonneg hW
 have hdef := WindowCountingDefect.actual_defect_estimate zetaZeroConfig hn W hW
   hc.le hC hCc hc64 hsep hB hPair hCert
 intro ε hε
 obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp
   (defect_to_dyadic zetaZeroConfig paperInputs_zeta (by omega : 2 ≤ n+1)
     hc (by linarith) hB0 hfloor hdef ε hε)
 exact ⟨T₀,fun T hT => by simpa only [zetaZeroConfig_N,zetaZeroConfig_N0s] using hT₀ T hT⟩

'''
body+='theorem simple_cumulative '+signature+''' :
 ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
 ((hw-B)/(1-c)-ε)*(Zeta23.Ncount 0 T:ℝ) ≤ Zeta23.N0simple 0 T :=
 Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
   (fun _ _ _ => Zeta23.N0simple_add' Zeta23.zetaSeam)
   (simple_dyadic '''+call+''')

'''
body+='theorem distinct_dyadic '+signature+''' :
 ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
 ((hw-B)/(1-c)-ε)*(Zeta23.Ncount T (2*T):ℝ) ≤ Zeta23.N0star T (2*T) := by
 intro ε hε
 obtain ⟨T₀,hT₀⟩ := simple_dyadic '''+call+''' ε hε
 refine ⟨T₀,fun T hT => (hT₀ T hT).trans ?_⟩
 exact_mod_cast AMW.N0simple_le_N0star' T (2*T)

'''
body+='theorem distinct_cumulative '+signature+''' :
 ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
 ((hw-B)/(1-c)-ε)*(Zeta23.Ncount 0 T:ℝ) ≤ Zeta23.N0star 0 T :=
 Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
   (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam)
   (distinct_dyadic '''+call+''')
'''
tail='''
set_option pp.fullNames true
#print axioms defect_to_dyadic
#print axioms simple_dyadic
#print axioms simple_cumulative
#print axioms distinct_dyadic
#print axioms distinct_cumulative
end StructuralGoal20261016.WindowCounting
end
'''
(ROOT/'StructuralGoal20261016/WindowCounting.lean').write_text(head+body+tail,encoding='utf8',newline='\n')
