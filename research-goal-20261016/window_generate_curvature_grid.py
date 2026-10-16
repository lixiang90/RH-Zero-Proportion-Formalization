"""Generate selected actual q2/q4 checks; dispatch only the pilot separately.

Every stored mask and quantized endpoint is untrusted input to the generic
proved cell checker. The 51KB active-only feed is frozen and not modified.
"""
from pathlib import Path
import json,hashlib
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
P=HERE/'cover-curvature-actual-active.json'
assert hashlib.sha256(P.read_bytes()).hexdigest()=='21edc54bd8ef52690d33acc6991853e8e5625c4e84149df3fac4fa6da5875bbb'
feed=json.loads(P.read_bytes());rows=feed['grid_rows'];COUNT=len(rows);SIZE=32;GROUPS=(COUNT+SIZE-1)//SIZE
assert COUNT==331
data='''/- SPDX-License-Identifier: Apache-2.0
Untrusted compact masks and original quantized q2/q4 cell payments.
-/
import StructuralGoal20261016.WindowCurvatureGrid
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowCurvatureGridData
open WindowCurvatureGrid
'''
for g in range(GROUPS):
    out=[]
    for r in rows[g*SIZE:(g+1)*SIZE]:
        m2,l,u=r.get('q2',[0,0,0]);m4,B=r.get('q4',[0,0])
        out.append(f"⟨{r['k']},{str('q2' in r).lower()},{m2},({l}),({u}),{str('q4' in r).lower()},{m4},({B})⟩")
    data+=f'def rows{g:02} : List Row := ['+',\n '.join(out)+']\n\n'
data+='def row (i : ℕ) : Row :=\n match i/32 with\n'
for g in range(GROUPS):data+=f' | {g} => rows{g:02}.getD (i%32) defaultRow\n'
data+=' | _ => defaultRow\n'
data+='def cells : List ℕ := ['+','.join(str(r['k'])for r in rows)+']\n'
data+='def index (k : ℕ) : ℕ := cells.idxOf k\n'
data+='end StructuralGoal20261016.WindowCurvatureGridData\n'
(ROOT/'StructuralGoal20261016/WindowCurvatureGridData.lean').write_text(data,encoding='utf8',newline='\n')
modules=[]
for g in range(GROUPS):
    name=f'WindowCurvatureGridChecks{g:02}'
    src=f'''/- SPDX-License-Identifier: Apache-2.0
Actual selected derivative cell checks, indices {g*SIZE}..{min(COUNT-1,(g+1)*SIZE-1)}.
-/
import StructuralGoal20261016.WindowCurvatureGridData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowCurvatureGridChecks
open WindowCurvatureGrid WindowCurvatureGridData
theorem checks{g:02} : ∀ j : Fin {SIZE}, {g}*{SIZE}+(j:ℕ) < {COUNT} →
 check (row ({g}*{SIZE}+(j:ℕ))) = true := by decide +kernel
set_option pp.fullNames true
#print axioms checks{g:02}
end StructuralGoal20261016.WindowCurvatureGridChecks
'''
    (ROOT/f'StructuralGoal20261016/{name}.lean').write_text(src,encoding='utf8',newline='\n')
    modules.append(f'StructuralGoal20261016.{name}')
src='''/- SPDX-License-Identifier: Apache-2.0
All selected actual q2/q4 derivative cells, with finite-query consumers.
-/
'''+''.join(f'import {m}\n'for m in modules)+f'''set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowCurvatureGridAll
open WindowCurvatureGrid WindowCurvatureGridData WindowCurvatureGridChecks
theorem checks : ∀ g : Fin {GROUPS}, ∀ j : Fin {SIZE}, (g:ℕ)*{SIZE}+(j:ℕ) < {COUNT} →
 check (row ((g:ℕ)*{SIZE}+(j:ℕ))) = true := by
 intro g
 fin_cases g
'''+''.join(f' · exact checks{g:02}\n'for g in range(GROUPS))+f'''
theorem valid (i : ℕ) (hi : i < {COUNT}) : Valid (row i) := by
 have hg : i/{SIZE} < {GROUPS} := by omega
 have hj : i%{SIZE} < {SIZE} := Nat.mod_lt i (by decide)
 have he : i/{SIZE}*{SIZE}+i%{SIZE} = i := by omega
 have hc := checks ⟨i/{SIZE},hg⟩ ⟨i%{SIZE},hj⟩
   (by change i/{SIZE}*{SIZE}+i%{SIZE} < {COUNT}; omega)
 change check (row (i/{SIZE}*{SIZE}+i%{SIZE})) = true at hc
 rw [he] at hc
 exact WindowCurvatureGrid.sound hc

theorem second {{k0 k1 : ℕ}} {{a b L U : ℚ}}
 (hc : secondCheck row index {COUNT} k0 k1 a b L U = true)
 {{x : ℝ}} (hx : x ∈ Icc (a:ℝ) b) :
 (L:ℝ) ≤ iteratedDeriv 2 WindowScalarMinorant.f x ∧
 iteratedDeriv 2 WindowScalarMinorant.f x ≤ (U:ℝ) :=
 WindowCurvatureGrid.second valid hc hx

theorem fourth {{k0 k1 : ℕ}} {{a b M : ℚ}}
 (hc : fourthCheck row index {COUNT} k0 k1 a b M = true)
 {{x : ℝ}} (hx : x ∈ Icc (a:ℝ) b) :
 |iteratedDeriv 4 WindowScalarMinorant.f x| ≤ (M:ℝ) :=
 WindowCurvatureGrid.fourth valid hc hx

set_option pp.fullNames true
#print axioms valid
#print axioms second
#print axioms fourth
end StructuralGoal20261016.WindowCurvatureGridAll
end
'''
(ROOT/'StructuralGoal20261016/WindowCurvatureGridAll.lean').write_text(src,encoding='utf8',newline='\n')
modules.append('StructuralGoal20261016.WindowCurvatureGridAll')
(HERE/'window_curvature_grid_modules.json').write_text(json.dumps(modules,indent=2)+'\n',encoding='utf8')
print(json.dumps({'cells':COUNT,'blocks':GROUPS,'data_bytes':len(data.encode()),'ordinary_Lean_proven':False}))
