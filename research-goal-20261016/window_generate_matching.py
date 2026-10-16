"""Adapt maximal matching to arbitrary new separation and actual kernel.

The pair payment is an explicit scalar short-pair obligation. It is not the
old hard-coded 17/20,1/64 kernel lemma. All remaining energy certificates use
the shared actual new-window Fw consumer from WindowDiscreteEnergy.
"""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[1]
core=(ROOT/'GramDefect20261015/Core.lean').read_text(encoding='utf-8')
cbc=(ROOT/'StructuralResearch20261016/CoboundaryCounting.lean').read_text(encoding='utf-8')
start=core.index('theorem close_pair_block_bound')
pair=core[start:core.index('\nend Opeth.AMMatching',start)]
pair=pair.replace('{c δ : ℝ}', '{c δ sep : ℝ}')
pair=pair.replace('(hc : c ≤ 1 / 64) (hδ : 0 ≤ δ)',
 '(hc : c ≤ 1 / 64) (hPair : ∀ t : ℝ, |t| ≤ sep → c ≤ wfun t) (hδ : 0 ≤ δ)')
pair=pair.replace('17 / 20','sep')
pair=pair.replace('have hkij : (1 / 64 : ℝ) ≤ wfun (x i - x j) :=\n    AMClosePair.kernel_square_ge hnear',
 'have hkij : c ≤ wfun (x i - x j) := hPair _ hnear')
pair=pair.replace('have hkji : (1 / 64 : ℝ) ≤ wfun (x j - x i) :=\n    AMClosePair.kernel_square_ge (by simpa only [abs_sub_comm] using hnear)',
 'have hkji : c ≤ wfun (x j - x i) := hPair _ (by simpa only [abs_sub_comm] using hnear)')
start=cbc.index('theorem matching_defect_bound_summed')
body=cbc[start:cbc.index('\nend Matching',start)]
body=body.replace('{c C : ℝ}', '{c C sep : ℝ}')
body=body.replace('17 / 20','sep')
body=body.replace('(hcPair : c ≤ 1 / 64)',
 '(hcPair : c ≤ 1 / 64)\n    (hPair : ∀ t : ℝ, |t| ≤ sep → c ≤ wfun t)')
body=body.replace('Opeth.AMMatching.close_pair_block_bound hG hcPair hδ',
 'close_pair_block_bound hG hcPair hPair hδ')
body=body.replace('matching_defect_bound_summed hn hx hG hc hC hcPair W',
 'matching_defect_bound_summed hn hx hG hc hC hcPair hPair W')
head='''/- SPDX-License-Identifier: Apache-2.0
Actual new-window maximal-matching defect payment at arbitrary separation.
Adapted from the attributed Opeth/CoboundaryCounting proofs. The short-pair
scalar input is explicit and refers to the actual new kernel, and the
separated energy input uses shared WindowGapEnergy.Fw. No record is asserted.
-/
import StructuralGoal20261016.WindowDiscreteEnergy
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23Ext.StableRankTrace Zeta23Ext.Bridge Zeta23Ext.BridgeW
open Meshuggah.Gram
namespace StructuralGoal20261016.WindowMatching
open WindowDiscreteEnergy
variable {ι : Type} [Fintype ι] [DecidableEq ι]

'''
tail='''
#print axioms close_pair_block_bound
#print axioms matching_defect_bound_effective
end StructuralGoal20261016.WindowMatching
end
'''
out=ROOT/'StructuralGoal20261016/WindowMatching.lean'
text=head+pair+'\n'+body+tail
text=re.sub(r'\b(wfun_sub_le_norm_sq|wfun|kfun)\b',r'WindowDiscreteEnergy.\1',text)
out.write_text(text,encoding='utf-8',newline='\n')
print(out.relative_to(ROOT),out.stat().st_size)
