"""Adapt generic retained-zero strip/span bounds to the actual new window."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
core=(ROOT/'GramDefect20261015/Core.lean').read_text(encoding='utf8')
def theorem(start,end):
    a=core.index(start);return core[a:core.index(end,a)]
deleted=theorem('theorem deleted_strips','end Zeta23Ext.Bridge')
span=theorem('theorem span_retained_le','end Analytic')
body=(deleted+'\n'+span).replace('mtParams','WindowCountingBase.mtParams')
head='''/- SPDX-License-Identifier: Apache-2.0
Actual new-window retained-zero strip and span estimates. These arguments
adapt the generic RvM proofs in the attributed Core; they assume no gap floor.
-/
import StructuralGoal20261016.WindowCountingBase
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Matrix RHLinalg Filter Finset
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23Ext.Bridge
namespace StructuralGoal20261016.WindowCountingGeometry
open Classical
'''
tail='''
set_option pp.fullNames true
#print axioms deleted_strips
#print axioms span_retained_le
end StructuralGoal20261016.WindowCountingGeometry
end
'''
(ROOT/'StructuralGoal20261016/WindowCountingGeometry.lean').write_text(head+body+tail,encoding='utf8',newline='\n')
