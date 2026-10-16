"""Emit an actual 43-row lifted derivative-graph pilot in small checkpoints.

The same 10 slab errors and 22 graph facets are retained. All pair maps,
slabs, facets, KKT feasibility, aggregate coefficients and forest bounds
are checked by ordinary Lean consumers. No optimizer is called here.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import json,hashlib
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
P=HERE/'cover-lifted-graph-pilot.json';raw=P.read_bytes();j=json.loads(raw)
SC,DS,D,Q=map(int,[j['SC'],j['DS'],j['D'],j['Q']]);assert SC==32768 and DS==10**15 and D==10**10 and Q==2*SC*DS*D
terms=[tuple(map(int,t))for t in j['positive_terms']];pairs=[tuple(map(int,p))for p in j['pair_order']];bs=list(map(int,j['b_numerators']))
INDEX={p:k for k,p in enumerate(pairs)};lo,hi=j['cell'];cert=j['certificate'];weighted=cert['weighted_rows'];N=len(weighted);assert N==43
gridrows=json.loads((HERE/'window_choice_grid.json').read_bytes())['rows'];grid={61+i:r for i,r in enumerate(gridrows)}
norm=json.loads((HERE/'window_normalized_interval.json').read_bytes());FS=10**30
W={int(n):[(int(F(l)*FS),int(F(u)*FS))for l,u in rows]for n,rows in norm['integer_w_Taylor_coefficients'].items()}

def point_error(n,q,p,v):
    cs=[tuple(z*factorial(k+q)//factorial(k)for z in W[n][k+q])for k in range(24-q)];z=cs[-1];delta=p-n
    for c in cs[-2::-1]:
        ps=[F(x)*delta for x in z];z=(c[0]+min(ps).__floor__(),c[1]+max(ps).__ceil__())
    return max(abs(F(z[0],FS)-v),abs(F(z[1],FS)-v))+F(44,7)**24*abs(delta)**(24-q)/factorial(24-q)

def qlit(q):
    q=F(q);return f'(({q.numerator}:ℚ)/{q.denominator})'
def zvec(v):return '!['+','.join(f'({int(x)})'for x in v)+']'
def cell_lit():
    M=[[0]*10 for _ in range(10)]
    for z,(i,k)in enumerate(pairs):M[i][k]=hi[z];M[k][i]=-lo[z]
    return '!['+',\n '.join(zvec(r)for r in M)+']'

slabs={desc[1]for desc,mu in weighted if desc[0]=='slab'}
scalars={};atom_text=[];gap=[0]*9;ys=[0]*41;B=0
for e in sorted(slabs):
    i,k,aw=terms[e];z=INDEX[i,k];l,u=lo[z],hi[z];P0,m0,m1,err,kind=cert['scalar_affine_data'][e]
    P0,m0,m1,err=map(int,[P0,m0,m1,err]);assert P0==l+u
    first=l//512;last=(max(l+1,u)+511)//512-1;assert 61<=first<=last<2048
    L=min(grid[k][2]for k in range(first,last+1));U=max(grid[k][3]for k in range(first,last+1));M=max(grid[k][4]for k in range(first,last+1))
    p=F(P0,2*SC);n=round(p);r=F(u-l,2*SC)
    if kind=='affine':
        required=point_error(n,1,p,F(m0,DS))+point_error(n,2,p,F(m1,DS))*r+F(M,DS)*r*r/2
        assert required<=F(err,DS),(e,'actual slab payment')
    else:assert kind=='interval'and m1==0 and m0-err<=L and U<=m0+err
    scalars[e]=f'⟨⟨({P0}),({m0}),({m1}),({err})⟩,{str(kind=="affine").lower()},{n},{first},{last},{qlit(F(L,DS))},{qlit(F(U,DS))},{qlit(F(M,DS))}⟩'
for desc,mu0 in weighted:
    mu=int(mu0);assert mu>=0;kind=desc[0];sgn=int(desc[2]);upper=str(sgn==1).lower();g=[0]*9;y=[0]*41
    if kind=='DBM':
        z=desc[1];i,k=pairs[z];ii,kk=(i,k)if sgn==1 else(k,i)
        atom_text.append(f'.dbm {ii} {kk}');g=[sgn*Q*int(i<=r<k)for r in range(9)]
        b=2*DS*D*(hi[z]if sgn==1 else-lo[z])
    elif kind=='KKT':
        r=desc[1];atom_text.append(f'.kkt {r} {upper}');assert sgn==-1 or lo[r]>123*SC//128
        y=[sgn*2*SC*DS*aw*int(i<=r<k)for i,k,aw in terms];b=-sgn*2*SC*DS*bs[r]
    else:
        e=desc[1];i,k,aw=terms[e]
        if kind=='slab':
            atom_text.append(f'.slab {e} {upper} (scalar {e})')
            anchor,m0,m1,err,_=cert['scalar_affine_data'][e];anchor,m0,m1,err=map(int,[anchor,m0,m1,err])
            coefficient=-sgn*2*SC*m1*D;b=D*(sgn*(2*SC*m0-m1*anchor)+2*SC*err)
        else:
            assert kind=='facet';S,C=map(int,desc[3:]);z=INDEX[i,k];l,u=lo[z],hi[z];first=l//512;last=(max(l+1,u)+511)//512-1
            for kk in range(first,last+1):
                xl=max(l,kk*512);xu=min(u,(kk+1)*512)
                if sgn==1:assert SC*grid[kk][3]-S*(xl if S>=0 else xu)<=C
                else:assert C<=SC*grid[kk][2]-S*(xu if S>=0 else xl)
            atom_text.append(f'.facet {e} {upper} ({S}) ({C}) {first} {last}')
            coefficient=-sgn*2*SC*S*D;b=sgn*2*D*C
        g=[coefficient*int(i<=r<k)for r in range(9)];y[e]=sgn*Q
    gap=[x+mu*z for x,z in zip(gap,g)];ys=[x+mu*z for x,z in zip(ys,y)];B+=mu*b
assert gap==list(map(int,cert['gap_coefficients'])),'actual gap form differs from discovery'
assert ys==list(map(int,cert['scalar_coefficients'])),'actual scalar form differs from discovery'
assert B==int(cert['rhs']),'actual bound form differs from discovery'
minimum=int(cert['minimum_numerator']);margin=minimum-7*SC*sum(map(abs,ys))-SC*B
assert margin==int(cert['strict_margin'])and margin>0
edges=[(r[0],r[1])for r in cert['flow']['nonzero_flow']]
data=f'''/- SPDX-License-Identifier: Apache-2.0
Untrusted lifted actual derivative-graph pilot. Input SHA256 {hashlib.sha256(raw).hexdigest()}.
-/
import StructuralGoal20261016.WindowLiftedKKT
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowLiftedPilotData
def cell : DifferenceCell.Cell 10 := {cell_lit()}
def pairFirst : Fin 41 → ℕ := {zvec(t[0]for t in terms)}
def pairLast : Fin 41 → ℕ := {zvec(t[1]for t in terms)}
def scalar (e : Fin 41) : WindowFirstOrderCertificate.Scalar :=
 match (e:ℕ) with
'''
for e,s in scalars.items():data+=f' | {e} => {s}\n'
data+=' | _ => ⟨⟨0,0,0,0⟩,false,0,0,0,0,0,0⟩\n'
data+='def atoms : Fin 43 → WindowLiftedKKT.Atom := !['+',\n '.join(atom_text)+']\n'
data+='def atom (i : ℕ) : WindowLiftedKKT.Atom := atoms ⟨i%43,Nat.mod_lt i (by decide)⟩\n'
data+='def weights : Fin 43 → ℤ := '+zvec(int(v)for _,v in weighted)+'\n'
data+='def stated : WindowLiftedFarkas.Form where\n gap := '+zvec(gap)+'\n scalar := '+zvec(ys)+f'\n bound := ({B})\n'
data+=f'def minimum : ℤ := ({minimum})\n'
data+='def edges : List FlowBasisCodec.Edge := ['+','.join(f'({i},{k})'for i,k in edges)+']\n'
data+='end StructuralGoal20261016.WindowLiftedPilotData\n'
(ROOT/'StructuralGoal20261016/WindowLiftedPilotData.lean').write_text(data,encoding='utf8',newline='\n')
modules=[]
for group in range(6):
    name=f'WindowLiftedPilotAtoms{group:02}'
    source=f'''/- SPDX-License-Identifier: Apache-2.0
Actual lifted atom checks {group*8}..{min(42,group*8+7)}.
-/
import StructuralGoal20261016.WindowLiftedPilotData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowLiftedPilotAtoms
open WindowLiftedPilotData
theorem checks{group:02} : ∀ k : Fin 8, {group}*8+(k:ℕ) < 43 →
 WindowLiftedKKT.checkAtom (123/128) cell (atom ({group}*8+(k:ℕ))) = true := by decide +kernel
set_option pp.fullNames true
#print axioms checks{group:02}
end StructuralGoal20261016.WindowLiftedPilotAtoms
'''
    (ROOT/f'StructuralGoal20261016/{name}.lean').write_text(source,encoding='utf8',newline='\n');modules.append('StructuralGoal20261016.'+name)
out={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'slab_indices':sorted(slabs),'atoms':43,'groups':6,'scalar_preflight_passed':True,
    'facet_preflight_passed':True,'aggregate_matches_original':True,'strict_margin':str(margin),'data_bytes':len(data.encode()),'ordinary_Lean_proven':False,
    'complete_global_cover':False,'new_zero_proportion_proven':False}
(HERE/'window_lifted_pilot_generation.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
(HERE/'window_lifted_pilot_atom_modules.json').write_text(json.dumps(modules,indent=2)+'\n',encoding='utf8')
assert P.read_bytes()==raw
print(json.dumps(out),flush=True)
