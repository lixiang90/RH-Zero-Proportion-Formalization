"""Small grouped checkpoints for the 23 OBBT checks after the passed pilot.

No passed pilot or data module is rewritten. All grouping is structural;
the same actual scalar, capacity, objective, rounding and forest checks run.
"""
from pathlib import Path
import json
HERE=Path(__file__).parent;ROOT=HERE.parent
base='StructuralGoal20261016.'
dispatch='''/- SPDX-License-Identifier: Apache-2.0
Finite dispatch of the 24 local OBBT payloads; no decoder is trusted.
-/
import StructuralGoal20261016.WindowCurvatureSubtreeData
import StructuralGoal20261016.WindowMixedCover
set_option Elab.async false
set_option maxHeartbeats 0
namespace StructuralGoal20261016.WindowCurvatureOBBTDispatch
open WindowCurvatureSubtreeData
def bound (i : ℕ) : WindowMixedContractions.OBBTBound :=
 match i with
'''+''.join(f' | {k} => bound{k:02}\n'for k in range(24))+''' | _ => bound00
def input (i : ℕ) : DifferenceCell.Cell 10 := if i < 14 then parent else leftParent
end StructuralGoal20261016.WindowCurvatureOBBTDispatch
'''
(ROOT/'StructuralGoal20261016/WindowCurvatureOBBTDispatch.lean').write_text(dispatch,encoding='utf8',newline='\n')
modules=[]
for g in range(3):
    name=f'WindowCurvatureOBBTGroup{g:02}'
    source=f'''/- SPDX-License-Identifier: Apache-2.0
Actual local OBBT checks {1+g*8}..{min(23,8+g*8)}.
-/
import StructuralGoal20261016.WindowCurvatureOBBTDispatch
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowCurvatureOBBTGroups
open WindowCurvatureOBBTDispatch
theorem checks{g:02} : ∀ j : Fin 8, 1+{g}*8+(j:ℕ) < 24 →
 WindowMixedContractions.obbtCheck WindowMixedCover.target880
   (input (1+{g}*8+(j:ℕ))) (bound (1+{g}*8+(j:ℕ))) = true := by decide +kernel
set_option pp.fullNames true
#print axioms checks{g:02}
end StructuralGoal20261016.WindowCurvatureOBBTGroups
'''
    (ROOT/f'StructuralGoal20261016/{name}.lean').write_text(source,encoding='utf8',newline='\n');modules.append(base+name)
source='''/- SPDX-License-Identifier: Apache-2.0
All 24 actual OBBT facts for the two parents of the local three-leaf tree.
-/
import StructuralGoal20261016.WindowCurvatureOBBT00
'''+''.join(f'import {m}\n'for m in modules)+'''set_option Elab.async false
set_option maxHeartbeats 0
namespace StructuralGoal20261016.WindowCurvatureOBBTAll
open WindowCurvatureOBBTDispatch WindowCurvatureOBBTGroups
theorem checked (i : Fin 24) : WindowMixedContractions.obbtCheck WindowMixedCover.target880
 (input i) (bound i) = true := by
 fin_cases i
 · exact WindowCurvatureOBBT.checked00
'''
for k in range(1,24):
    g,j=divmod(k-1,8)
    source+=f' · exact checks{g:02} ⟨{j},by decide⟩ (by decide)\n'
source+='set_option pp.fullNames true\n#print axioms checked\nend StructuralGoal20261016.WindowCurvatureOBBTAll\n'
(ROOT/'StructuralGoal20261016/WindowCurvatureOBBTAll.lean').write_text(source,encoding='utf8',newline='\n')
modules=[base+'WindowCurvatureOBBTDispatch']+modules+[base+'WindowCurvatureOBBTAll',base+'WindowCurvatureSubtreeGeometry']
(HERE/'window_curvature_obbt_group_modules.json').write_text(json.dumps(modules,indent=2)+'\n',encoding='utf8')
print(json.dumps({'actual_bounds':24,'passed_pilot_preserved':True,'new_groups':3,'ordinary_Lean_proven':False}))
