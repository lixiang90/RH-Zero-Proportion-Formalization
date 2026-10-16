"""Emit actual tight-box checks and aggregate the already proved old atoms."""
from window_moment_frozen_write import write_lean
from pathlib import Path
from fractions import Fraction as F
import hashlib
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sha=lambda raw:hashlib.sha256(raw).hexdigest()
raw=(HERE/'cover-cross-moment-factor-friendly-cases.json').read_bytes()
assert sha(raw)=='bf45540baf5919358a8a4182fe41c323be2157c89f3897f2620602a8581629a7'
cases=json.loads(raw)['cases']
def rat(q):
 q=F(q);return f'(({q.numerator}:ℚ)/{q.denominator})'
def vec(v,conv=str):return '!['+','.join(conv(x)for x in v)+']'
opts='set_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
source='''/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentBox
import StructuralGoal20261016.WindowMomentEnergyData
'''+opts+'''namespace StructuralGoal20261016.WindowMomentBoxData
'''
for k,c in enumerate(cases):
 ep=c['energy_packet'];ub=c['tight_derivative_bounds']
 source+=f'def box{k} : WindowMomentBox.Packet where\n'
 for field,vals,conv in [('center',c['physical_gap_center'],rat),('radius',c['physical_gap_radius'],rat),
                        ('uLower',[u[0]for u in ub],rat),('uUpper',[u[1]for u in ub],rat),
                        ('firstCell',[g[0]for g in ep['grid_ranges']],str),('lastCell',[g[1]for g in ep['grid_ranges']],str)]:
  source+=f' {field} := '+vec(vals,conv)+'\n'
source+='end StructuralGoal20261016.WindowMomentBoxData\n'
write_lean(ROOT/'StructuralGoal20261016/WindowMomentBoxData.lean',source)
modules=['StructuralGoal20261016.WindowMomentBoxData']
for k in range(2):
 name=f'WindowMomentBoxCase{k:02}'
 source='''/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentBoxData
'''+opts+f'''noncomputable section
namespace StructuralGoal20261016.{name}
open WindowMomentBox WindowMomentBoxData WindowMomentEnergyData
theorem checked : check cell{k} box{k} = true := by decide +kernel
theorem bounds {{g : Fin 9 → ℝ}} (hg : WindowDifferenceCell.Contains cell{k} g) :
 ∀ i, (lower box{k} i:ℝ) ≤ actual box{k} g i ∧ actual box{k} g i ≤ (upper box{k} i:ℝ) :=
 sound checked hg
set_option pp.fullNames true
#print axioms checked
#print axioms bounds
end StructuralGoal20261016.{name}
end
'''
 write_lean(ROOT/f'StructuralGoal20261016/{name}.lean',source)
 modules.append('StructuralGoal20261016.'+name)
source='/- SPDX-License-Identifier: Apache-2.0 -/\n'
for c in range(2):
 for g in range(7):source+=f'import StructuralGoal20261016.WindowMomentAtoms{c}Checks{g:02}\n'
source+=opts+'''namespace StructuralGoal20261016.WindowMomentAtomsAll
open WindowMomentAtomData WindowMomentEnergyData WindowMomentAtomChecks
'''
for c,n in [(0,103),(1,106)]:
 source+=f'''theorem checks{c} : ∀ g : Fin 7, ∀ j : Fin 16, (g:ℕ)*16+(j:ℕ) < {n} →
 WindowLiftedKKT.checkAtom (123/128) cell{c} (atom{c} ((g:ℕ)*16+(j:ℕ))) = true := by
 intro g
 fin_cases g
'''+''.join(f' · exact checks{c}_{g:02}\n'for g in range(7))+f'''
theorem checked{c} (i : Fin {n}) :
 WindowLiftedKKT.checkAtom (123/128) cell{c} (atoms{c} i) = true := by
 have hi := i.isLt
 have h := checks{c} ⟨(i:ℕ)/16,by omega⟩ ⟨(i:ℕ)%16,Nat.mod_lt _ (by decide)⟩
   (by change (i:ℕ)/16*16+(i:ℕ)%16 < {n}; omega)
 have he : (i:ℕ)/16*16+(i:ℕ)%16 = (i:ℕ) := by omega
 change WindowLiftedKKT.checkAtom (123/128) cell{c} (atom{c} ((i:ℕ)/16*16+(i:ℕ)%16)) = true at h
 rw [he] at h
 simpa only [atom{c},Nat.mod_eq_of_lt hi] using h

theorem factor{c} : ∀ i : Fin {n}, 0 ≤ factorA{c} i ∧
 (∑ r : Fin 9, |factorB{c} i r|) ≤ factorA{c} i := by decide +kernel

theorem valid{c} {{g : Fin 9 → ℝ}}
 (hg : WindowMinimizerCover.Relevant (123/128:ℚ) g)
 (hc : WindowDifferenceCell.Contains cell{c} g) (i : Fin {n}) :
 WindowLiftedFarkas.eval (WindowLiftedKKT.form cell{c} (atoms{c} i)) g ≤
   ((WindowLiftedKKT.form cell{c} (atoms{c} i)).bound:ℝ) :=
 WindowLiftedKKT.atom_sound (atoms{c} i) (checked{c} i) hg hc
'''
source+='set_option pp.fullNames true\n'
for c in range(2):
 for name in ['checked','factor','valid']:source+=f'#print axioms {name}{c}\n'
source+='end StructuralGoal20261016.WindowMomentAtomsAll\n'
# Sums and the relevant threshold use explicit scopes/types.
source=source.replace('namespace StructuralGoal20261016.WindowMomentAtomsAll\n','open scoped BigOperators\nnoncomputable section\nnamespace StructuralGoal20261016.WindowMomentAtomsAll\n').replace('(123/128:ℚ) g','((123/128:ℚ):ℝ) g')
source+='end\n'
write_lean(ROOT/'StructuralGoal20261016/WindowMomentAtomsAll.lean',source)
modules.append('StructuralGoal20261016.WindowMomentAtomsAll')
out={'grouped_cases_sha256':sha(raw),'modules':[{'module':m,'source_sha256':sha((ROOT/(m.replace('.','/')+'.lean')).read_bytes())}for m in modules],
     'ordinary_Lean_verified':False,'actual_Lean_exclusions':False,'complete_global_cover':False}
(HERE/'window_moment_actual_box_modules.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
print(json.dumps({'generated_modules':modules,'actual_Lean_exclusions':False}))
