"""Independent stdlib audit of shared quartic moments and dynamic remainders.

Rebuild jets/w5 from the older independent interval-Horner checker.  Check
all edge Taylor/error polynomials, 5795 scalar rows and 4070 PSD entries.
Actual frozen Taylor/F0 enclosures remain explicit analytic inputs; no
optimizer or new actual-kernel sampling position is used in this replay.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import factorial
import gzip,hashlib,json,sys,time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OLD=ROOT/'research-goal-20261016'
sys.path.insert(0,str(OLD))
from cover_correlated_replay import ScalarReplay,J

SC=32768;DS=10**15;OUT=HERE/'quartic-replay.json'
MON=[m for d in range(5) for m in combinations_with_replacement(range(9),d)];INDEX={m:k for k,m in enumerate(MON)}
ALL=[(i,i+1) for i in range(9)]+[(i,j) for i in range(9) for j in range(i+2,10)];LOOK={e:k for k,e in enumerate(ALL)}
HP=[(i,j) for i in range(9) for j in range(i,9)]


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def put(a,k,v):
    z=a.get(k,F(0))+v
    if z:a[k]=z
    else:a.pop(k,None)
def add(a,b,s=F(1)):
    a=a.copy()
    for k,v in b.items():put(a,k,s*v)
    return a
def times(a,b):
    p={}
    for k,v in a.items():
        for l,w in b.items():
            m=tuple(sorted(k+l));assert len(m)<=4;put(p,m,v*w)
    return p
def scale(a,s):return {k:v*s for k,v in a.items() if v*s}
def unpack(p):return {MON[k]:F(v) for k,v in p}
def form(p):return {'constant':str(p.get((),F(0))),
    'coefficients':[[INDEX[k]-1,str(v)] for k,v in sorted(p.items(),key=lambda z:INDEX[z[0]]) if k]}


def main():
    assert not OUT.exists();began=time.monotonic()
    modelpath=HERE/'quartic-model.json.gz';buildpath=HERE/'quartic-build.json'
    inputpath=OLD/'cover-residual-psd-rational-inputs.json';tablepath=OLD/'cover_newjet.json'
    parampath=ROOT/'research-20261016-followup/window_reweight_rational.json'
    paths=[Path(__file__),modelpath,buildpath,inputpath,tablepath,parampath,OLD/'cover_correlated_replay.py']
    pins={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths}
    raw=gzip.decompress(modelpath.read_bytes());model=json.loads(raw);build=json.loads(buildpath.read_bytes())
    assert sha(modelpath)==build['model_compressed_sha256'] and hashlib.sha256(raw).hexdigest()==build['model_uncompressed_sha256']
    for p,h in model['source_sha256_start'].items():assert sha(ROOT/p)==h
    assert model['source_sha256_start']==model['source_sha256_end']
    inputs=json.loads(inputpath.read_bytes());params=json.loads(parampath.read_bytes());tab=json.loads(tablepath.read_bytes())
    assert tab['receipt']['parameter_sha256']==sha(parampath)
    assert model['monomials']==list(map(list,MON)) and len(MON)==715 and MON[:55][-1] in list(combinations_with_replacement(range(9),2))
    assert model['Taylor_table_terms']==23 and model['Taylor_table_degree']==22 and model['whole_grid_w5_remainder_power']==19
    assert all(len(v)==23 for v in tab['integer_taylor_coefficients'].values())
    assert sum(F(abs(v),10**9) for v in params['window_coefficient_numerators_1e9'])<F(2,25)
    scalar=ScalarReplay(tab);M=F(44,7)**24;state=inputs['cell'];packet=inputs['energy_packets'][0]
    anchor=list(map(F,packet['centre']));center=[F(l+u,2*SC) for l,u in zip(state[0][:9],state[1][:9])]
    radius=[F(u-l,2*SC) for l,u in zip(state[0][:9],state[1][:9])];assert all(v>0 for v in radius)
    assert all(l>123*SC//128 for l in state[0][:9])
    spans=[];slacks=[]
    for (i,j),l,u in zip(ALL,*state):
        lo,hi=F(l,SC),F(u,SC);assert lo<hi and lo<=sum(anchor[i:j])<=hi
        p={():sum(center[i:j]),**{(r,):radius[r] for r in range(i,j)}};spans.append(p)
        low=scale(add(p,{():lo},F(-1)),1/(hi-lo));slacks.extend([low,add({():F(1)},low,F(-1))])
    assert [unpack(p) for p in model['normalized_geometry_slacks']]==slacks
    fifth={}
    def cell_bound(k):
        if k not in fifth:
            n=round(F(2*k+1,2*scalar.step));x=J(F(k,scalar.step)-n,F(k+1,scalar.step)-n)
            v=scalar.poly(n,x,4);r=M*F(1,2)**19/factorial(19)
            a=max(abs(v.l-r),abs(v.u+r))*DS;fifth[k]=F(-((-a.numerator)//a.denominator),DS)
        return fifth[k]
    terms=[tuple(t) for t in params['a_upper'] if t[2]];den=params['denominator'];c=F(model['target'])
    H=[{():F(b,den)} for b in params['b_numerators']];E=[{} for _ in range(9)];L4={():F(packet['F_interval'][0])}
    for r,b in enumerate(params['b_numerators']):L4=add(L4,{():center[r]-anchor[r],(r,):radius[r]},F(b,den))
    for e,((i,j,aw),stored) in enumerate(zip(terms,model['edge_packets'])):
        axis=LOOK[i,j];p=sum(anchor[i:j]);P=2*SC*p;assert P.denominator==1
        assert P.numerator==stored['doubled_anchor_integer'] and stored['edge']==[i,j]
        n=round(p);delta=p-n;jets=[]
        for order in range(1,5):
            value=scalar.poly(n,J(delta),order-1);rem=M*abs(delta)**(24-order)/factorial(24-order)
            jets.append((value.l-rem,value.u+rem))
        assert jets==[tuple(map(F,v)) for v in stored['anchor_derivative_intervals_orders_1_to_4']]
        mid=[(l+u)/2 for l,u in jets];eps=[(u-l)/2 for l,u in jets]
        lo,hi=state[0][axis],state[1][axis];R=max(p-F(lo,SC),F(hi,SC)-p)
        grid=list(range(lo//scalar.width,(hi+scalar.width-1)//scalar.width));B=max(cell_bound(k) for k in grid)
        assert grid==stored['whole_span_w5_grid_cells'] and B==F(stored['whole_span_absolute_w5_bound']) and R==F(stored['radius_about_anchor'])
        d=add(spans[axis],{():p},F(-1));powers=[{():F(1)}]
        for k in range(4):powers.append(times(powers[-1],d))
        u={};energy={}
        for k in range(4):u=add(u,powers[k],mid[k]/factorial(k))
        err={():eps[0]+eps[1]*R};err=add(err,powers[2],eps[2]/2+eps[3]*R/6);err=add(err,powers[4],B/24)
        for k in range(1,5):energy=add(energy,powers[k],mid[k-1]/factorial(k))
        energy=add(energy,{():eps[0]*R},F(-1));energy=add(energy,powers[2],-(eps[1]/2+eps[2]*R/6));energy=add(energy,powers[4],-(eps[3]/24+B*R/120))
        assert unpack(stored['derivative_cubic'])==u and unpack(stored['derivative_error_dynamic_quartic'])==err
        assert unpack(stored['energy_increment_lower_quartic'])==energy
        L4=add(L4,energy,F(aw,den))
        for r in range(i,j):H[r]=add(H[r],u,F(aw,den));E[r]=add(E[r],err,F(aw,den))
    assert L4==unpack(model['new_quartic_L4']) and H==[unpack(p) for p in model['KKT_cubic_polynomials']] and E==[unpack(p) for p in model['KKT_dynamic_error_polynomials']]
    L2={():F(packet['quadratic_constant'])}
    for k,v in packet['row']:
        if k<9:L2=add(L2,{():center[k],(k,):radius[k]},F(v))
        else:assert 50<=k<95;put(L2,HP[k-50],F(v))
    assert L2==unpack(model['old_quadratic_L2'])
    expected=[]
    def positive(p,meta):
        f=form(scale(p,F(-1)));bound=-F(f['constant']);s=max([abs(bound)]+[abs(F(v)) for _,v in f['coefficients']]) or F(1)
        expected.append({'coefficients':f['coefficients'],'bound':str(bound),'scale':str(s),'meta':meta})
    for k,g in enumerate(slacks):positive(g,['DBM_mean',k])
    for k,g in enumerate(slacks):
        for l in range(k,90):positive(times(g,slacks[l]),['all_slack_pair_RLT',k,l])
    for r in range(9):
        for s,test in enumerate([H[r]]+[times(H[r],{(t,):F(1)}) for t in range(9)]):
            for sign in [-1,1]:positive(add(E[r],test,F(sign)),['free_KKT_with_dynamic_error',r,s,sign])
    for k,m in enumerate(MON[1:]):
        even=all(m.count(t)%2==0 for t in set(m));low=F(0) if even else F(-1)
        expected.extend([{'coefficients':[[k,'-1']],'bound':str(-low),'scale':'1','meta':['redundant_cube_moment_box',k,-1]},
                         {'coefficients':[[k,'1']],'bound':'1','scale':'1','meta':['redundant_cube_moment_box',k,1]}])
    f=form(L4);s=max([abs(c-F(f['constant']))]+[abs(F(v)) for _,v in f['coefficients']]+[F(1,1000)])
    expected.extend([{'coefficients':f['coefficients']+[[714,'-1/1000']],'bound':str(c-F(f['constant'])),'scale':str(s),'meta':['quartic_energy_only_slack']},
                     {'coefficients':[[714,'-1']],'bound':'0','scale':'1','meta':['energy_slack_nonnegative']}])
    assert expected==model['linear_rows'] and len(expected)==5795
    multipliers=[{():F(1)},scale(add({():c},L2,F(-1)),1/c)]+[scale(times(slacks[2*k],slacks[2*k+1]),F(4)) for k in range(45)]
    entries=0
    for b,(block,g) in enumerate(zip(model['PSD_blocks'],multipliers)):
        basis=MON[:55] if b==0 else MON[:10];want=[]
        for j in range(len(basis)):
            for i in range(j,len(basis)):want.append([i,j,form(times(g,{tuple(sorted(basis[i]+basis[j])):F(1)}))])
        assert want==block['entries'] and g==unpack(block['multiplier_polynomial']);entries+=len(want)
    assert entries==4070 and len(model['PSD_blocks'])==47
    assert not any(n.split('.')[0] in ['numpy','scipy','scs'] for n in sys.modules)
    final={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths};assert final==pins
    result={'scope':__doc__,'status':'shared_quartic_coefficients_rows_and_localizers_independently_verified',
        'path':model['path'],'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,
        'Taylor_table_terms':23,'Taylor_table_degree':22,'whole_w5_remainder_exponent':19,
        'edge_packets_checked':41,'linear_rows_checked':5795,'PSD_entries_checked':4070,
        'moments_including_constant':715,'whole_w5_grid_cells':len(fifth),
        'new_scalar_positions':0,'actual_analytic_input_proved_here':False,'solver_calls':0,'Lean_invocations':0,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    OUT.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:result[k] for k in ['status','linear_rows_checked','PSD_entries_checked','elapsed_milliseconds']}),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
