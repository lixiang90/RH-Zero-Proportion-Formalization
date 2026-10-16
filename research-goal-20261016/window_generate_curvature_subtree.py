"""Generate a checked actual-kernel pilot for the three-leaf LCA subtree.

Frozen ancestry is decoded without an optimizer. The only mathematical
claims are in the emitted ordinary-Lean checks. Old scalar quantizations
are retained and compared to the already proved normalized K/W tables.
The output covers one LCA cell, never the global pressure root.
"""
from pathlib import Path
from fractions import Fraction as F
from types import SimpleNamespace
from math import factorial
import functools,gzip,hashlib,json,re
import window_interval_kernel as ik
import cover_compact_codec as codec
from cover_correlated_replay import a
HERE=Path(__file__).parent;ROOT=HERE.parent;SC=32768;DS=10**15;LD=10**12;D=10**10;DEN=LD*D*SC;Q=10**30
LCA='r00100000110110111000111';CORE=6881;TMAX=1<<24
ceil=lambda q:-((-q.numerator)//q.denominator)
floor=lambda q:q.numerator//q.denominator
sha=lambda b:hashlib.sha256(b).hexdigest()

@functools.lru_cache(None)
def old_support(p):
    n=round(F(p,SC));assert 1<=n<=16 and n*SC-CORE<=p<=n*SC+CORE
    v,d=ik.w_jet(F(p,SC),1);l,u=n*SC-CORE,n*SC+CORE
    if d.u<=0 and v.u+d.u*F(u-p,SC)<=0:u=TMAX
    if d.l>=0 and v.u+d.l*F(l-p,SC)<=0:l=0
    vl=floor(v.l*10**10);dl=floor(d.l*10**9);du=ceil(d.u*10**9)
    return l,u,vl,dl,du-dl

@functools.lru_cache(None)
def old_constant(l,u):
    if u-l>=SC:return 0
    p=round(F(l+u,128))*64;k,d=ik.kernel_jet(F(p,SC),1)
    radius=F(max(abs(l-p),abs(u-p)),SC)
    err=max(abs(d.l),abs(d.u))*radius+2*radius*radius
    kl,ku=k.l-err,k.u+err
    value=min(abs(kl),abs(ku))**2 if kl*ku>0 else F(0)
    return floor(value*10**10)

def raw_tables():
    s=(ROOT/'StructuralGoal20261016/WindowJetTableData.lean').read_text(encoding='utf8')
    ans={}
    for name,nxt in [('kValues','wValues'),('wValues','E')]:
        part=s.split('def '+name+' :',1)[1].split('def '+nxt,1)[0]
        pairs=[(int(l),int(u))for l,u in re.findall(r'qi30 \((-?\d+)\) \((-?\d+)\)',part)]
        assert len(pairs)==33*24,(name,len(pairs))
        ans[name]=[pairs[n*24:(n+1)*24]for n in range(33)]
    return ans['kValues'],ans['wValues']

def poly(C,delta):
    z=C[-1]
    for c in C[-2::-1]:
        products=[F(x)*delta for x in z]
        z=(c[0]+floor(min(products)),c[1]+ceil(max(products)))
    return F(z[0],Q),F(z[1],Q)

def point_interval(C,n,p,q,majorant):
    cs=[tuple(z*factorial(j+q)//factorial(j)for z in C[n][j+q])for j in range(24-q)]
    l,u=poly(cs,p-n);err=majorant**24*abs(p-n)**(24-q)/factorial(24-q)
    return l-err,u+err

def qlit(q):
    q=F(q)
    return f'(({q.numerator}:ℚ)/{q.denominator})'
def zvec(xs):return '!['+','.join(f'({int(x)})'for x in xs)+']'
def matrix(state):return [[a.edge_value(state,i,j)for j in range(10)]for i in range(10)]
def cell_lit(state):return '!['+',\n '.join(zvec(row)for row in matrix(state))+']'

def main():
    folder=HERE/'cover-targeted-curvature-evidence';manifest=json.loads((folder/'manifest.json').read_bytes())
    raw=(folder/'proof.json.gz').read_bytes();assert sha(raw)==manifest['sha256'];doc=json.loads(gzip.decompress(raw))
    ext=json.loads((folder/'cross-extension.json').read_bytes());cases=[doc]+ext['cases']
    params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    terms=[tuple(t)for t in params['a_upper']if t[2]];bs=params['b_numerators']
    g=SimpleNamespace(LD=LD,DEN=DEN,SC=SC,BS=bs,TERMS=terms)
    w=SimpleNamespace(g=g,constant_lower=old_constant,original_support=old_support)
    target=11*(DEN//1250);assert doc['target']=='11/1250'
    state=doc['root'];path='r';records={};states={}
    # Reconstruct only the ancestry needed to identify the exact LCA input.
    for bit in doc['path'][1:]:
        states[path]=state
        if path in doc['ancestor_OBBT']:
            step=codec.unpack_obbt(state,doc['ancestor_OBBT'][path],target,w)
            if path in [LCA,LCA+'0']:records[path]=step
            state=step['new_cell']
        assert not doc['ancestor_Newton'].get(path)
        branch=doc['ancestor_branches'][path]
        state=a.child(state,branch['axis'],branch['cut'],bit=='0');assert state is not None;path+=bit
    assert state==doc['cell'] and len(records)==2
    parent=states[LCA];left=states[LCA+'0']
    refined=records[LCA]['new_cell'];refined_left=records[LCA+'0']['new_cell']
    assert a.child(refined,7,38166,False)==cases[1]['cell']
    assert a.child(refined_left,1,38810,True)==cases[0]['cell']
    assert a.child(refined_left,1,38810,False)==cases[2]['cell']
    K,W=raw_tables();supports=[];support_ids={};constant_audit=[]
    def intern(expression):
        if expression not in support_ids:support_ids[expression]=len(supports);supports.append(expression)
        return support_ids[expression]
    zero=intern('WindowScalarLine.Support.zero')
    @functools.lru_cache(None)
    def tangent(p):
        pl,pu,V,S,E=old_support(p);n=round(F(p,SC));x=F(p,SC)
        vl,vu=point_interval(W,n,x,0,F(44,7));dl,du=point_interval(W,n,x,1,F(44,7))
        assert F(V,10**10)<=vl and F(S,10**9)<=dl and du<=F(S+E,10**9),(p,'tangent point payment')
        return intern(f'.tangent ⟨{n},({p}),({V}),({S}),({E})⟩')
    @functools.lru_cache(None)
    def constant(l,u):
        V=old_constant(l,u)
        if V==0:return zero
        P=round(F(l+u,128))*64;x=F(P,SC);n=round(x);r=F(max(abs(l-P),abs(u-P)),SC)
        kl,ku=point_interval(K,n,x,0,F(22,7));dl,du=point_interval(K,n,x,1,F(22,7))
        # Store outward Q30 point endpoints, leaving the original V floor.
        kl=F(floor(kl*Q),Q);ku=F(ceil(ku*Q),Q);dl=F(floor(dl*Q),Q);du=F(ceil(du*Q),Q)
        err=max(abs(dl),abs(du))*r+2*r*r;lo=kl-err;hi=ku+err
        assert (lo>=0 and F(V,10**10)<=lo*lo)or(hi<=0 and F(V,10**10)<=hi*hi),(l,u,V,'constant payment')
        constant_audit.append({'l':l,'u':u,'P':P,'original_value':V})
        return intern(f'.constant ⟨{n},({P}),{qlit(kl)},{qlit(ku)},{qlit(dl)},{qlit(du)},{qlit(r)},({V})⟩')
    bound_rows=[];node_bounds={};counter=0
    for node in [LCA,LCA+'0']:
        row=records[node];lo,hi=row['old_cell'];node_bounds[node]=[]
        for cert in row['certificates']:
            grouped=[[]for _ in terms]
            for t,p,weight,C,S in cert['minorant']['mixture']:
                i,j,_=terms[t];z=a.INDEX[i,j];idx=constant(lo[z],hi[z])if p==-1 else tangent(p)
                if p!=-1:
                    pl,pu,V,sl,err=old_support(p)
                    assert C==str(SC*V-10*sl*p-10*err*max(p-lo[z],0))and S==str(10*sl)
                grouped[t].append((int(weight),idx))
            size=max(map(len,grouped));assert size>0
            lam=[];scalar=[]
            for entries in grouped:
                entries=entries+[(0,zero)]*(size-len(entries))
                lam.append(zvec(v for v,_ in entries));scalar.append('!['+','.join(f'support {i}'for _,i in entries)+']')
            z=cert['axis'];i,j=a.PAIRS[z]
            ci,cj,bound=(j,i,-cert['new_lower'])if cert['sign']==1 else(i,j,cert['new_upper'])
            edges=[(r[0],r[1])for r in cert['flow']['nonzero_flow']]
            node_bounds[node].append(counter)
            bound_rows.append({'id':counter,'node':node,'size':size,'lam':lam,'scalar':scalar,'cut':(ci,cj,bound),
                'payment':cert['multiplier_numerator'],'scale':cert['multiplier_denominator'],'minimum':int(cert['minimum_numerator']),'edges':edges})
            counter+=1
    assert len(bound_rows)==24
    data='''/- SPDX-License-Identifier: Apache-2.0
Untrusted actual-scalar OBBT payloads for one three-leaf LCA subtree.
No assertion about the global pressure root is made here.
-/
import StructuralGoal20261016.WindowMixedContractions
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowCurvatureSubtreeData
'''
    for name,state in [('parent',parent),('leftParent',left),('refined',refined),('leftRefined',refined_left)]:
        data+=f'def {name} : DifferenceCell.Cell 10 := {cell_lit(state)}\n\n'
    data+='def supports : List WindowScalarLine.Support := ['+',\n '.join(supports)+']\n'
    data+='def support (i : ℕ) : WindowScalarLine.Support := supports.getD i .zero\n\n'
    for b in bound_rows:
        k=b['id'];ci,cj,v=b['cut'];size=b['size']
        data+=f'def bound{k:02} : WindowMixedContractions.OBBTBound where\n  size := {size}\n'
        data+='  lam := !['+',\n    '.join(b['lam'])+']\n'
        data+='  scalar := !['+',\n    '.join(b['scalar'])+']\n'
        data+=f'  cut := ⟨{ci},{cj},({v})⟩\n  payment := {b["payment"]}\n  scale := {b["scale"]}\n  minimum := ({b["minimum"]})\n'
        data+='  edges := ['+','.join(f'({i},{j})'for i,j in b['edges'])+']\n\n'
    data+='end StructuralGoal20261016.WindowCurvatureSubtreeData\n'
    (ROOT/'StructuralGoal20261016/WindowCurvatureSubtreeData.lean').write_text(data,encoding='utf8',newline='\n')
    modules=[]
    for b in bound_rows:
        k=b['id'];parent_name='parent'if b['node']==LCA else'leftParent';name=f'WindowCurvatureOBBT{k:02}'
        source=f'''/- SPDX-License-Identifier: Apache-2.0
Actual scalar/capacity/rounding/forest-flow OBBT check {k} of 24.
-/
import StructuralGoal20261016.WindowCurvatureSubtreeData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowCurvatureOBBT
open WindowCurvatureSubtreeData
theorem checked{k:02} : WindowMixedContractions.obbtCheck WindowMixedCover.target880 {parent_name} bound{k:02} = true := by
 decide +kernel
set_option pp.fullNames true
#print axioms checked{k:02}
end StructuralGoal20261016.WindowCurvatureOBBT
'''
        # target880 is defined in MixedCover, not its Contractions dependency.
        source=source.replace('import StructuralGoal20261016.WindowCurvatureSubtreeData','import StructuralGoal20261016.WindowCurvatureSubtreeData\nimport StructuralGoal20261016.WindowMixedCover')
        (ROOT/f'StructuralGoal20261016/{name}.lean').write_text(source,encoding='utf8',newline='\n');modules.append(f'StructuralGoal20261016.{name}')
    (HERE/'window_curvature_subtree_modules.json').write_text(json.dumps(modules,indent=2)+'\n',encoding='utf8')
    receipt={'scope':__doc__,'LCA':LCA,'ancestor_input_gzip_sha256':sha(raw),'parent_state':parent,'left_parent_state':left,
        'bounds':[{k:v for k,v in b.items()if k not in ['lam','scalar']}for b in bound_rows],
        'support_count':len(supports),'constant_nonzero_supports':constant_audit,'data_bytes':len(data.encode()),
        'all_point_and_constant_payments_replayed':True,'ordinary_Lean_proven':False,'complete_global_cover':False,'new_zero_proportion_proven':False}
    (HERE/'window_curvature_subtree_generation.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:receipt[k]for k in ['LCA','support_count','data_bytes','all_point_and_constant_payments_replayed']}),flush=True)
if __name__=='__main__':main()
