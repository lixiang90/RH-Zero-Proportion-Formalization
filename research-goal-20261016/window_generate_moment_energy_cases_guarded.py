"""Emit two actual midpoint energy lower bounds from the frozen friendly packet."""
from window_moment_frozen_write import write_lean
from pathlib import Path
from fractions import Fraction as F
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sha = lambda raw: hashlib.sha256(raw).hexdigest()
friendly_raw = (HERE/'window-moment-friendly-packets.json').read_bytes()
assert sha(friendly_raw) == '83fa5971057aab9afd1f6f7bac1e3c860c6c3676967514fb331497fd17917057'
friendly = json.loads(friendly_raw)
cases_raw = (HERE/'cover-cross-moment-factor-friendly-cases.json').read_bytes()
assert sha(cases_raw) == 'bf45540baf5919358a8a4182fe41c323be2157c89f3897f2620602a8581629a7'
cases = json.loads(cases_raw)['cases']
pairs = [(i,i+1) for i in range(9)]+[(i,j) for i in range(9) for j in range(i+2,10)]
lookup = {p:k for k,p in enumerate(pairs)}

def rat(q):
    q = F(q)
    return f'(({q.numerator}:ℚ)/{q.denominator})'

def vector(values, convert=str):
    return '!['+','.join(convert(v) for v in values)+']'

options = 'set_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
body = '''/- SPDX-License-Identifier: Apache-2.0
Untrusted exact cells and midpoint packets for two local energy bounds.
-/
import StructuralGoal20261016.WindowMomentEnergyCertificate
'''+options+'''namespace StructuralGoal20261016.WindowMomentEnergyData
open WindowMomentEnergyCertificate
'''
for k,(case,frow) in enumerate(zip(cases,friendly['rows'])):
    assert case['path'] == frow['path']
    energy = frow['energy0']
    assert case['energy_packet'] == energy
    state = case['cell']; p = list(map(F,energy['centre']))
    radii = [max(p[r]-F(state[0][r],32768),F(state[1][r],32768)-p[r]) for r in range(9)]
    matrix = [[0 if i==j else state[1][lookup[i,j]] if i<j else -state[0][lookup[j,i]] for j in range(10)] for i in range(10)]
    body += f'-- frozen cell {case["path"]}\ndef cell{k} : DifferenceCell.Cell 10 := '+vector(matrix,lambda r:vector(r))+'\n'
    body += f'def packet{k} : Packet where\n'
    for field,values,convert in [
        ('center',p,rat),('radius',radii,rat),('point',energy['point_indices'],str),
        ('firstCell',[v[0] for v in energy['grid_ranges']],str),
        ('lastCell',[v[1] for v in energy['grid_ranges']],str),
        ('secondLower',energy['whole_span_second_lower'],rat),
        ('secondUpper',[1000000]*41,rat)]:
        body += f' {field} := '+vector(values,convert)+'\n'
body += 'end StructuralGoal20261016.WindowMomentEnergyData\n'
path = ROOT/'StructuralGoal20261016/WindowMomentEnergyData.lean'
write_lean(path,body)
modules = ['StructuralGoal20261016.WindowMomentEnergyData']
for k in range(2):
    name = f'WindowMomentEnergyCase{k:02}'
    body = '''/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentEnergyData
'''+options+f'''noncomputable section
namespace StructuralGoal20261016.{name}
open WindowMomentEnergyCertificate WindowMomentEnergyData

theorem geometry : checkGeometry cell{k} packet{k} = true := by decide +kernel
theorem second : checkSecond cell{k} packet{k} = true := by decide +kernel
theorem checked : check cell{k} packet{k} = true := by
 simpa only [check,Bool.and_eq_true] using And.intro geometry second

theorem lower {{g : Fin 9 → ℝ}} (hg : WindowDifferenceCell.Contains cell{k} g) :
 polynomial packet{k} g ≤ WindowGapEnergy.Fw24 g :=
 WindowMomentEnergyCertificate.lower checked hg

theorem sublevel {{g : Fin 9 → ℝ}} {{c : ℝ}}
 (hg : WindowDifferenceCell.Contains cell{k} g) (hbelow : WindowGapEnergy.Fw24 g < c) :
 polynomial packet{k} g < c := WindowMomentEnergyCertificate.sublevel checked hg hbelow

set_option pp.fullNames true
#print axioms geometry
#print axioms second
#print axioms checked
#print axioms lower
#print axioms sublevel
end StructuralGoal20261016.{name}
end
'''
    write_lean(ROOT/f'StructuralGoal20261016/{name}.lean',body)
    modules.append('StructuralGoal20261016.'+name)
out = {'friendly_sha256':sha(friendly_raw),'grouped_cases_sha256':sha(cases_raw),
       'modules':[{'module':m,'source_sha256':sha((ROOT/(m.replace('.','/')+'.lean')).read_bytes())} for m in modules],
       'actual_Lean_energy_bounds':False,'actual_Lean_exclusions':False,'complete_global_cover':False}
(HERE/'window_moment_energy_case_modules.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
print(json.dumps({'generated_modules':modules,'actual_Lean_energy_bounds':False}))
