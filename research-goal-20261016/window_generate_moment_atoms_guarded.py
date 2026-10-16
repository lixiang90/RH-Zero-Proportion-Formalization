"""Emit only old actual rows selected by the two grouped moment certificates.

No optimizer is called. Existing derivative-grid endpoints and the original
slab/facet constants are retained. Each selected atom is checked in Lean.
"""
from window_moment_frozen_write import write_lean
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sha = lambda raw: hashlib.sha256(raw).hexdigest()
raw = (HERE/'cover-cross-moment-factor-friendly-cases.json').read_bytes()
assert sha(raw) == 'bf45540baf5919358a8a4182fe41c323be2157c89f3897f2620602a8581629a7'
document = json.loads(raw)
cases = document['cases']
SC, DS, D = 32768,10**15,10**10
Q = 2*SC*DS*D
parameters_raw = (ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes()
parameters = json.loads(parameters_raw)
terms = [(i,j,a) for i,j,a in parameters['a_upper'] if a]
pairs = [(i,i+1) for i in range(9)]+[(i,j) for i in range(9) for j in range(i+2,10)]
index = {p:k for k,p in enumerate(pairs)}
grid_raw = (HERE/'window_choice_grid.json').read_bytes()
grid = {61+i:r for i,r in enumerate(json.loads(grid_raw)['rows'])}
norm_raw = (HERE/'window_normalized_interval.json').read_bytes()
norm = json.loads(norm_raw)
FS = 10**30
W = {int(n):[(int(F(l)*FS),int(F(u)*FS)) for l,u in rows] for n,rows in norm['integer_w_Taylor_coefficients'].items()}

def point_error(n,q,p,v):
    cs = [tuple(z*factorial(k+q)//factorial(k) for z in W[n][k+q]) for k in range(24-q)]
    z = cs[-1]
    delta = p-n
    for c in cs[-2::-1]:
        ps = [F(x)*delta for x in z]
        z = (c[0]+min(ps).__floor__(),c[1]+max(ps).__ceil__())
    return max(abs(F(z[0],FS)-v),abs(F(z[1],FS)-v))+F(44,7)**24*abs(delta)**(24-q)/factorial(24-q)

def qlit(value):
    value = F(value)
    return f'(({value.numerator}:ℚ)/{value.denominator})'

def vector(values,conv=str):
    return '!['+','.join(conv(v) for v in values)+']'

options = 'set_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
source = '''/- SPDX-License-Identifier: Apache-2.0
Untrusted selected actual atoms and nonnegative grouped multipliers.
-/
import StructuralGoal20261016.WindowMomentEnergyData
import StructuralGoal20261016.WindowLiftedKKT
'''+options+'''namespace StructuralGoal20261016.WindowMomentAtomData
open WindowMomentEnergyData
'''
modules = ['StructuralGoal20261016.WindowMomentAtomData']
generated = []
for case_number,case in enumerate(cases):
    lo,hi = case['cell']
    scalar_data = dict(case['scalar_affine_data'])
    scalar_literals = {}
    factors = case['factors']
    assert len(factors) == [103,106][case_number]
    for e,(anchor,m0,m1,error,kind) in scalar_data.items():
        anchor,m0,m1,error = map(int,[anchor,m0,m1,error])
        i,j,_ = terms[e]; z = index[i,j]; l,u = lo[z],hi[z]
        first = l//512;last = (max(l+1,u)+511)//512-1
        L = min(grid[k][2] for k in range(first,last+1))
        U = max(grid[k][3] for k in range(first,last+1))
        M = max(grid[k][4] for k in range(first,last+1))
        p = F(anchor,2*SC); n=round(p);radius=F(u-l,2*SC)
        if kind == 'affine':
            required=point_error(n,1,p,F(m0,DS))+point_error(n,2,p,F(m1,DS))*radius+F(M,DS)*radius**2/2
            assert required <= F(error,DS),(case_number,e,'slab payment')
        else:
            assert kind=='interval' and m1==0 and m0-error <= L and U <= m0+error
        scalar_literals[e] = f'⟨⟨({anchor}),({m0}),({m1}),({error})⟩,{str(kind=="affine").lower()},{n},{first},{last},{qlit(F(L,DS))},{qlit(F(U,DS))},{qlit(F(M,DS))}⟩'
    source += f'def scalar{case_number} (e : Fin 41) : WindowFirstOrderCertificate.Scalar :=\n match (e:ℕ) with\n'
    for e,s in scalar_literals.items():source += f' | {e} => {s}\n'
    source += ' | _ => ⟨⟨0,0,0,0⟩,false,0,0,0,0,0,0⟩\n'
    atoms=[];A=[];b=[]
    for factor in factors:
        desc=factor['old_meta'];kind=desc[0];sgn=int(desc[2]);upper=str(sgn==1).lower()
        A.append(int(factor['A']))
        bs=[0]*9
        for s,value in factor['b']:bs[s]=int(value)
        assert sum(map(abs,bs)) <= A[-1]
        b.append(bs)
        if kind=='DBM':
            i,j=pairs[desc[1]]
            if sgn==-1:i,j=j,i
            atoms.append(f'.dbm {i} {j}')
        elif kind=='KKT':
            r=desc[1]
            assert sgn==-1 or F(lo[r],SC)>F(123,128)
            atoms.append(f'.kkt {r} {upper}')
        elif kind=='slab':
            e=desc[1];assert e in scalar_literals
            atoms.append(f'.slab {e} {upper} (scalar{case_number} {e})')
        else:
            assert kind=='facet'
            e=desc[1];S,C=map(int,desc[3:]);i,j,_=terms[e];z=index[i,j];l,u=lo[z],hi[z]
            first=l//512;last=(max(l+1,u)+511)//512-1
            for k in range(first,last+1):
                xl=max(l,k*512);xu=min(u,(k+1)*512)
                if sgn==1:assert SC*grid[k][3]-S*(xl if S>=0 else xu)<=C
                else:assert C<=SC*grid[k][2]-S*(xu if S>=0 else xl)
            atoms.append(f'.facet {e} {upper} ({S}) ({C}) {first} {last}')
    count=len(atoms)
    source += f'def atoms{case_number} : Fin {count} → WindowLiftedKKT.Atom := '+vector(atoms)+'\n'
    source += f'def atom{case_number} (i : ℕ) : WindowLiftedKKT.Atom := atoms{case_number} ⟨i%{count},Nat.mod_lt i (by decide)⟩\n'
    source += f'def factorA{case_number} : Fin {count} → ℤ := '+vector(A,lambda x:f'({x})')+'\n'
    source += f'def factorB{case_number} : Fin {count} → Fin 9 → ℤ := '+vector(b,lambda row:vector(row,lambda x:f'({x})'))+'\n'
    for group in range((count+15)//16):
        name=f'WindowMomentAtoms{case_number}Checks{group:02}'
        generated.append((name,case_number,group,count))
source+='end StructuralGoal20261016.WindowMomentAtomData\n'
write_lean(ROOT/'StructuralGoal20261016/WindowMomentAtomData.lean',source)
for name,c,g,count in generated:
    body='''/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentAtomData
'''+options+f'''namespace StructuralGoal20261016.WindowMomentAtomChecks
open WindowMomentAtomData WindowMomentEnergyData
theorem checks{c}_{g:02} : ∀ j : Fin 16, {g}*16+(j:ℕ) < {count} →
 WindowLiftedKKT.checkAtom (123/128) cell{c} (atom{c} ({g}*16+(j:ℕ))) = true := by decide +kernel
set_option pp.fullNames true
#print axioms checks{c}_{g:02}
end StructuralGoal20261016.WindowMomentAtomChecks
'''
    write_lean(ROOT/f'StructuralGoal20261016/{name}.lean',body)
    modules.append('StructuralGoal20261016.'+name)
out={'scope':__doc__,'grouped_packet_sha256':sha(raw),'grid_sha256':sha(grid_raw),'normalized_sha256':sha(norm_raw),
     'parameters_sha256':sha(parameters_raw),'case_atoms':[103,106],'active_scalar_terms':[10,13],
     'modules':modules,'ordinary_Lean_verified':False,'actual_Lean_exclusions':False,'complete_global_cover':False}
(HERE/'window_moment_atom_modules.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
print(json.dumps({'generated_modules':len(modules),'preflight_all_passed':True,'actual_Lean_exclusions':False}))
