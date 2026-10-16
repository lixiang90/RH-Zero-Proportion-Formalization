"""Emit new point and q2 checkpoints; reuse the old 331 checked grid rows."""
from window_moment_frozen_write import write_lean
from pathlib import Path
from fractions import Fraction as F
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent
P=HERE/'window-moment-friendly-packets.json'
raw=P.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='83fa5971057aab9afd1f6f7bac1e3c860c6c3676967514fb331497fd17917057'
packet=json.loads(raw)
points=packet['point_rows'];grids=packet['new_q2_rows']
assert len(points)==82 and len(grids)==403

def rat(value):
    q=F(value)
    return f'(({q.numerator}:ℚ)/{q.denominator})'

def write(name,body):
    path=ROOT/f'StructuralGoal20261016/{name}.lean'
    write_lean(path,body)
    return 'StructuralGoal20261016.'+name

options='set_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
point_data='''/- SPDX-License-Identifier: Apache-2.0
Coarse, untrusted value/slope packets at the two actual midpoint centres.
-/
import StructuralGoal20261016.WindowAnchorCertificate
'''+options+'''namespace StructuralGoal20261016.WindowMomentPointData
open WindowAnchorCertificate
'''
for group in range(6):
    literals=[]
    for r in points[group*16:(group+1)*16]:
        literals.append(f"⟨{r['n']},{rat(r['p'])},{rat(r['value_lower'])},{rat(r['slope'])},{rat(r['slope_error'])}⟩")
    point_data+=f'def rows{group:02} : List Row := ['+',\n '.join(literals)+']\n'
point_data+='def row (i : ℕ) : Row :=\n match i/16 with\n'
for group in range(6):point_data+=f' | {group} => rows{group:02}.getD (i%16) defaultRow\n'
point_data+=' | _ => defaultRow\nend StructuralGoal20261016.WindowMomentPointData\n'
point_modules=[write('WindowMomentPointData',point_data)]
for group in range(6):
    name=f'WindowMomentPointChecks{group:02}'
    body='''/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentPointData
'''+options+f'''namespace StructuralGoal20261016.WindowMomentPointChecks
open WindowAnchorCertificate WindowMomentPointData
theorem checks{group:02} : ∀ j : Fin 16, {group}*16+(j:ℕ) < 82 →
 check (row ({group}*16+(j:ℕ))) = true := by decide +kernel
set_option pp.fullNames true
#print axioms checks{group:02}
end StructuralGoal20261016.WindowMomentPointChecks
'''
    point_modules.append(write(name,body))
body='/- SPDX-License-Identifier: Apache-2.0 -/\n'+''.join('import '+m+'\n' for m in point_modules[1:])+options+'''namespace StructuralGoal20261016.WindowMomentPointAll
open WindowAnchorCertificate WindowMomentPointData WindowMomentPointChecks
theorem checks : ∀ g : Fin 6, ∀ j : Fin 16, (g:ℕ)*16+(j:ℕ) < 82 →
 check (row ((g:ℕ)*16+(j:ℕ))) = true := by
 intro g
 fin_cases g
'''+''.join(f' · exact checks{group:02}\n'for group in range(6))+'''
theorem valid (i : ℕ) (hi : i < 82) : Valid (row i) := by
 have hg : i/16 < 6 := by omega
 have hj : i%16 < 16 := Nat.mod_lt i (by decide)
 have he : i/16*16+i%16 = i := by omega
 have hc := checks ⟨i/16,hg⟩ ⟨i%16,hj⟩ (by change i/16*16+i%16 < 82; omega)
 change check (row (i/16*16+i%16)) = true at hc
 rw [he] at hc
 exact WindowAnchorCertificate.sound hc
set_option pp.fullNames true
#print axioms valid
end StructuralGoal20261016.WindowMomentPointAll
'''
point_modules.append(write('WindowMomentPointAll',body))

grid_data='''/- SPDX-License-Identifier: Apache-2.0
Only 403 additional q2 cells. Old checked q2/q4 source data are reused.
-/
import StructuralGoal20261016.WindowCurvatureGridAll
'''+options+'''namespace StructuralGoal20261016.WindowMomentSecondData
open WindowCurvatureGrid
'''
for group in range(13):
    literals=[]
    for r in grids[group*32:(group+1)*32]:
        L=F(r['lower'])*10**15;U=F(r['upper'])*10**15
        assert L.denominator==U.denominator==1
        literals.append(f"⟨{r['k']},true,{r['mask']},({int(L)}),({int(U)}),false,0,0⟩")
    grid_data+=f'def rows{group:02} : List Row := ['+',\n '.join(literals)+']\n'
grid_data+='def newRow (i : ℕ) : Row :=\n match i/32 with\n'
for group in range(13):grid_data+=f' | {group} => rows{group:02}.getD (i%32) defaultRow\n'
grid_data+=' | _ => defaultRow\n'
grid_data+='def newCells : List ℕ := ['+','.join(str(r['k'])for r in grids)+']\n'
grid_data+='''def row (i : ℕ) : Row :=
 if i < 331 then WindowCurvatureGridData.row i else newRow (i-331)
def index (k : ℕ) : ℕ :=
 if (WindowCurvatureGridData.row (WindowCurvatureGridData.index k)).has2 then
   WindowCurvatureGridData.index k else 331+newCells.idxOf k
end StructuralGoal20261016.WindowMomentSecondData
'''
grid_modules=[write('WindowMomentSecondData',grid_data)]
for group in range(13):
    name=f'WindowMomentSecondChecks{group:02}'
    body='''/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentSecondData
'''+options+f'''namespace StructuralGoal20261016.WindowMomentSecondChecks
open WindowCurvatureGrid WindowMomentSecondData
theorem checks{group:02} : ∀ j : Fin 32, {group}*32+(j:ℕ) < 403 →
 check (newRow ({group}*32+(j:ℕ))) = true := by decide +kernel
set_option pp.fullNames true
#print axioms checks{group:02}
end StructuralGoal20261016.WindowMomentSecondChecks
'''
    grid_modules.append(write(name,body))
body='/- SPDX-License-Identifier: Apache-2.0 -/\n'+''.join('import '+m+'\n'for m in grid_modules[1:])+options+'''noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowMomentSecondAll
open WindowCurvatureGrid WindowMomentSecondData WindowMomentSecondChecks
theorem checks : ∀ g : Fin 13, ∀ j : Fin 32, (g:ℕ)*32+(j:ℕ) < 403 →
 check (newRow ((g:ℕ)*32+(j:ℕ))) = true := by
 intro g
 fin_cases g
'''+''.join(f' · exact checks{group:02}\n'for group in range(13))+'''
theorem newValid (i : ℕ) (hi : i < 403) : Valid (newRow i) := by
 have hg : i/32 < 13 := by omega
 have hj : i%32 < 32 := Nat.mod_lt i (by decide)
 have he : i/32*32+i%32 = i := by omega
 have hc := checks ⟨i/32,hg⟩ ⟨i%32,hj⟩ (by change i/32*32+i%32 < 403; omega)
 change check (newRow (i/32*32+i%32)) = true at hc
 rw [he] at hc
 exact WindowCurvatureGrid.sound hc
theorem valid (i : ℕ) (hi : i < 734) : Valid (row i) := by
 by_cases hold : i < 331
 · simpa only [row,if_pos hold] using WindowCurvatureGridAll.valid i hold
 · simpa only [row,if_neg hold] using newValid (i-331) (by omega)
theorem second {k0 k1 : ℕ} {a b L U : ℚ}
 (hc : secondCheck row index 734 k0 k1 a b L U = true)
 {x : ℝ} (hx : x ∈ Icc (a:ℝ) b) :
 (L:ℝ) ≤ iteratedDeriv 2 WindowScalarMinorant.f x ∧
   iteratedDeriv 2 WindowScalarMinorant.f x ≤ (U:ℝ) :=
 WindowCurvatureGrid.second valid hc hx
set_option pp.fullNames true
#print axioms newValid
#print axioms valid
#print axioms second
end StructuralGoal20261016.WindowMomentSecondAll
end
'''
grid_modules.append(write('WindowMomentSecondAll',body))
manifest={'source_sha256':hashlib.sha256(raw).hexdigest(),'point_modules':point_modules,'grid_modules':grid_modules,
          'point_rows':82,'new_q2_rows':403,'old_q2_reused':175,'old_modules_recompiled':False,
          'new_q4_rows':0,'ordinary_Lean_proven':False}
(HERE/'window_moment_numeric_modules.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'point_modules':len(point_modules),'grid_modules':len(grid_modules),'ordinary_Lean_proven':False}))
