"""Shared gap moments through degree four: exact static model construction.

Nine normalized gaps are the only underlying variables.  All 715 monomials
(714 nonconstant) are shared by energy, KKT, geometry and localizers.
Reuse the old common anchor and degree-22 (23-term) Taylor table for w'.
No scalar sampling position, optimizer, or Lean invocation is added here.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import factorial
import gzip,hashlib,json,time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OLD=ROOT/'research-goal-20261016'
SC=32768;C=F(11,1250);DS=10**15
MON=[m for d in range(5) for m in combinations_with_replacement(range(9),d)]
MI={m:k for k,m in enumerate(MON)};B1=MON[:10];B2=MON[:55]
ALL=[(i,i+1) for i in range(9)]+[(i,j) for i in range(9) for j in range(i+2,10)]
LOOK={e:k for k,e in enumerate(ALL)}
HP=[(i,j) for i in range(9) for j in range(i,9)]
OUT=HERE/'quartic-model.json.gz';RECEIPT=HERE/'quartic-build.json'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def put(p,m,v):
    z=p.get(m,F(0))+v
    if z:p[m]=z
    else:p.pop(m,None)
def add(p,q,s=F(1)):
    p=p.copy()
    for m,v in q.items():put(p,m,s*v)
    return p
def mul(p,q):
    ans={}
    for m,v in p.items():
        for n,w in q.items():
            z=tuple(sorted(m+n));assert len(z)<=4;put(ans,z,v*w)
    return ans
def scale(p,s):return {m:v*s for m,v in p.items() if v*s}
def evaluate(p,y):
    ans=F(0)
    for m,v in p.items():
        for r in m:v*=y[r]
        ans+=v
    return ans
def pack(p):return [[MI[m],str(v)] for m,v in sorted(p.items(),key=lambda x:MI[x[0]])]
def linear_form(p):return {'constant':str(p.get((),F(0))),
    'coefficients':[[MI[m]-1,str(v)] for m,v in sorted(p.items(),key=lambda x:MI[x[0]]) if m]}


class J:
    def __init__(self,l,u=None):self.l=F(l);self.u=F(l if u is None else u);assert self.l<=self.u
    def __add__(self,x):
        if not isinstance(x,J):x=J(x)
        return J(self.l+x.l,self.u+x.u)
    __radd__=__add__
    def __mul__(self,x):
        if not isinstance(x,J):x=J(x)
        values=[self.l*x.l,self.l*x.u,self.u*x.l,self.u*x.u]
        return J(min(values),max(values))
    __rmul__=__mul__


class Table:
    def __init__(self,doc):
        self.cs={int(n):[J(l,u) for l,u in row] for n,row in doc['integer_taylor_coefficients'].items()}
        assert set(map(len,self.cs.values()))=={23}
        self.M=F(44,7)**24;self.step=doc['receipt']['grid_step'];self.width=SC//self.step;self.fifth={}
        assert self.step==64 and doc['receipt']['order']==24 and len(self.cs)==33
    def poly(self,n,x,d):
        ans=J(0)
        for k in range(22,d-1,-1):ans=ans*x+self.cs[n][k]*F(factorial(k),factorial(k-d))
        return ans
    def anchor_jets(self,P):
        p=F(P,2*SC);n=round(p);x=p-n;out=[]
        for order in range(1,5):
            value=self.poly(n,J(x),order-1);rem=self.M*abs(x)**(24-order)/factorial(24-order)
            out.append(J(value.l-rem,value.u+rem))
        return out
    def fifth_cell(self,k):
        if k not in self.fifth:
            n=round(F(2*k+1,2*self.step));x=J(F(k,self.step)-n,F(k+1,self.step)-n)
            value=self.poly(n,x,4);rem=self.M*F(1,2)**19/factorial(19)
            bound=max(abs(value.l-rem),abs(value.u+rem))*DS
            ceil=-((-bound.numerator)//bound.denominator)
            self.fifth[k]=F(ceil,DS)
        return self.fifth[k]
    def fifth_range(self,l,u):
        assert 0<=l<u<=32*SC
        ks=list(range(l//self.width,(u+self.width-1)//self.width))
        return max(self.fifth_cell(k) for k in ks),ks


def main():
    assert not OUT.exists() and not RECEIPT.exists();began=time.monotonic()
    inputpath=OLD/'cover-residual-psd-rational-inputs.json';tablepath=OLD/'cover_newjet.json'
    parampath=ROOT/'research-20261016-followup/window_reweight_rational.json'
    paths=[Path(__file__),inputpath,tablepath,parampath,OLD/'cover-cross-moment-remaining-six.json',OLD/'cover-full-u-face-files.json']
    pins={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths}
    inputs=json.loads(inputpath.read_bytes());table_doc=json.loads(tablepath.read_bytes());params=json.loads(parampath.read_bytes())
    assert table_doc['receipt']['parameter_sha256']==sha(parampath)
    state=inputs['cell'];packet=inputs['energy_packets'][0];anchor=list(map(F,packet['centre']))
    assert all(l>123*SC//128 for l in state[0][:9])
    assert len(MON)==715 and len(B2)==55 and len(B1)==10
    center=[F(l+u,2*SC) for l,u in zip(state[0][:9],state[1][:9])]
    radius=[F(u-l,2*SC) for l,u in zip(state[0][:9],state[1][:9])];assert all(v>0 for v in radius)
    span=[];slacks=[];geometry=[]
    for axis,(i,j) in enumerate(ALL):
        lo,hi=F(state[0][axis],SC),F(state[1][axis],SC);assert lo<hi
        p=sum(anchor[i:j]);assert lo<=p<=hi
        s={():sum(center[i:j]),**{(r,):radius[r] for r in range(i,j)}}
        lower=scale(add(s,{():lo},F(-1)),1/(hi-lo));upper=add({():F(1)},lower,F(-1))
        slacks.extend([lower,upper]);span.append(s)
        geometry.append(scale(mul(lower,upper),F(4)))
    oracle=Table(table_doc);terms=[tuple(t) for t in params['a_upper'] if t[2]];den=params['denominator']
    assert len(terms)==41
    f0lower=F(packet['F_interval'][0]);L4={():f0lower};H=[{():F(b,den)} for b in params['b_numerators']]
    E=[{} for _ in range(9)];data=[]
    for r,b in enumerate(params['b_numerators']):L4=add(L4,{():center[r]-anchor[r],(r,):radius[r]},F(b,den))
    for e,(i,j,aw) in enumerate(terms):
        axis=LOOK[i,j];lo,hi=state[0][axis],state[1][axis];p=sum(anchor[i:j]);P=2*SC*p;assert P.denominator==1
        R=max(p-F(lo,SC),F(hi,SC)-p);assert R>0
        jets=oracle.anchor_jets(P.numerator);mid=[(q.l+q.u)/2 for q in jets];eps=[(q.u-q.l)/2 for q in jets]
        M5,grid=oracle.fifth_range(lo,hi)
        d=add(span[axis],{():p},F(-1));powers=[{():F(1)}]
        for k in range(4):powers.append(mul(powers[-1],d))
        upoly={}
        for k in range(4):upoly=add(upoly,powers[k],mid[k]/factorial(k))
        err={():eps[0]+eps[1]*R}
        err=add(err,powers[2],eps[2]/2+eps[3]*R/6)
        err=add(err,powers[4],M5/24)
        energy={}
        for k in range(1,5):energy=add(energy,powers[k],mid[k-1]/factorial(k))
        energy=add(energy,{():eps[0]*R},F(-1))
        energy=add(energy,powers[2],-(eps[1]/2+eps[2]*R/6))
        energy=add(energy,powers[4],-(eps[3]/24+M5*R/120))
        a=F(aw,den);L4=add(L4,energy,a)
        for r in range(i,j):H[r]=add(H[r],upoly,a);E[r]=add(E[r],err,a)
        data.append({'term':e,'edge':[i,j],'span_axis':axis,'anchor':str(p),'doubled_anchor_integer':P.numerator,
            'anchor_in_whole_span_interval':True,'radius_about_anchor':str(R),
            'anchor_derivative_intervals_orders_1_to_4':[[str(q.l),str(q.u)] for q in jets],
            'anchor_derivative_midpoints':list(map(str,mid)),'anchor_derivative_errors':list(map(str,eps)),
            'whole_span_absolute_w5_bound':str(M5),'whole_span_w5_grid_cells':grid,
            'd_polynomial':pack(d),'derivative_cubic':pack(upoly),'derivative_error_dynamic_quartic':pack(err),
            'energy_increment_lower_quartic':pack(energy)})
    L2={():F(packet['quadratic_constant'])}
    for index,raw in packet['row']:
        coefficient=F(raw)
        if index<9:L2=add(L2,{():center[index],(index,):radius[index]},coefficient)
        else:
            assert 50<=index<95
            put(L2,HP[index-50],coefficient)
    y0=[(p-c)/r for p,c,r in zip(anchor,center,radius)]
    assert evaluate(L2,y0)==f0lower-F(packet['uniform_gradient_error_payment'])
    assert evaluate(L4,y0)==f0lower-sum(F(aw,den)*F(row['anchor_derivative_errors'][0])*F(row['radius_about_anchor']) for row,(_,_,aw) in zip(data,terms))
    rows=[]
    def append_nonnegative(poly,meta):
        f=linear_form(scale(poly,F(-1)));bound=-F(f['constant']);coeff=f['coefficients']
        s=max([abs(bound)]+[abs(F(v)) for _,v in coeff]) or F(1)
        rows.append({'coefficients':coeff,'bound':str(bound),'scale':str(s),'meta':meta})
    for k,g in enumerate(slacks):append_nonnegative(g,['DBM_mean',k])
    for k,g in enumerate(slacks):
        for l in range(k,len(slacks)):append_nonnegative(mul(g,slacks[l]),['all_slack_pair_RLT',k,l])
    for r in range(9):
        tests=[H[r]]+[mul(H[r],{(s,):F(1)}) for s in range(9)]
        for s,test in enumerate(tests):
            for sign in [-1,1]:append_nonnegative(add(E[r],test,F(sign)),['free_KKT_with_dynamic_error',r,s,sign])
    # Redundant cube moment boxes: follow from M2 and the nine adjacent
    # (1-y_r^2)*M1 localizers, which bound every M2 diagonal by one.
    for index,m in enumerate(MON[1:]):
        even=all(m.count(r)%2==0 for r in set(m));lower=F(0) if even else F(-1)
        rows.append({'coefficients':[[index,'-1']],'bound':str(-lower),'scale':'1','meta':['redundant_cube_moment_box',index,-1]})
        rows.append({'coefficients':[[index,'1']],'bound':'1','scale':'1','meta':['redundant_cube_moment_box',index,1]})
    # Only the new quartic energy row is softened by the one energy slack.
    energy_form=linear_form(L4);energy_scale=max([abs(C-F(energy_form['constant']))]+[abs(F(v)) for _,v in energy_form['coefficients']]+[F(1,1000)])
    energy_row={'coefficients':energy_form['coefficients']+[[714,'-1/1000']],
        'bound':str(C-F(energy_form['constant'])),'scale':str(energy_scale),'meta':['quartic_energy_only_slack']}
    rows.append(energy_row);rows.append({'coefficients':[[714,'-1']],'bound':'0','scale':'1','meta':['energy_slack_nonnegative']})
    assert len(rows)==90+4095+180+1428+2
    blocks=[]
    def block(name,basis,g):
        entries=[]
        for j in range(len(basis)):
            for i in range(j,len(basis)):
                entry=mul(g,{tuple(sorted(basis[i]+basis[j])):F(1)})
                entries.append([i,j,linear_form(entry)])
        blocks.append({'name':name,'size':len(basis),'multiplier_polynomial':pack(g),'entries':entries})
    block('M2_shared_degree4',B2,{():F(1)})
    block('sublevel_old_quadratic_energy',B1,scale(add({():C},L2,F(-1)),1/C))
    for axis,g in enumerate(geometry):block('span_product_'+str(axis),B1,g)
    assert len(blocks)==47 and sum(len(b['entries']) for b in blocks)==4070
    final={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths};assert final==pins
    result={'scope':__doc__,'status':'shared_quartic_model_statically_constructed','path':inputs['path'],'cell':state,
        'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,
        'underlying_real_variables':9,'moment_count_including_constant':715,'nonconstant_moment_variables':714,'slack_index':714,
        'monomials':[list(m) for m in MON],'target':str(C),'normalized_gap_center':list(map(str,center)),
        'normalized_gap_radius':list(map(str,radius)),'common_anchor':list(map(str,anchor)),
        'common_F0_interval':packet['F_interval'],'common_F0_lower_used':str(f0lower),
        'Taylor_table_terms':23,'Taylor_table_degree':22,'Taylor_table_function':'w prime',
        'global_absolute_w24_bound':str(oracle.M),'anchor_wj_remainder_power':'24-j for j=1..4',
        'whole_grid_w5_remainder_power':19,'whole_grid_w5_remainder_factorial':19,
        'new_scalar_positions':0,'whole_grid_w5_cells_rebuilt':len(oracle.fifth),'edge_packets':data,
        'old_quadratic_L2':pack(L2),'new_quartic_L4':pack(L4),'KKT_cubic_polynomials':[pack(p) for p in H],
        'KKT_dynamic_error_polynomials':[pack(p) for p in E],
        'normalized_geometry_slacks':[pack(p) for p in slacks],
        'linear_rows':rows,'PSD_blocks':blocks,'row_counts':{'DBM_mean':90,'slack_pair_RLT':4095,'KKT_bidirectional':180,'redundant_moment_boxes':1428,'energy_and_slack':2},
        'PSD_sizes':[b['size'] for b in blocks],'unsoftened_sublevel_localizer':True,
        'analytic_inputs':['frozen anchor F interval and integer Taylor coefficient enclosures are actual new-window enclosures',
            'positive normalized Fourier profile implies abs(w24)<= (2*pi)^24 < (44/7)^24',
            'all nine original coordinates are free KKT coordinates at a putative minimum',
            'candidate belongs to this cell and F<c; L2<=actual F on the whole cell'],
        'actual_analytic_inputs_Lean_proved_here':False,'solver_calls':0,'Lean_invocations':0,
        'cell_exclusion_proven':False,'new_zero_proportion_proven':False,'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    raw=(json.dumps(result,separators=(',',':'),allow_nan=False)+'\n').encode();OUT.write_bytes(gzip.compress(raw,mtime=0))
    summary={k:result[k] for k in ['status','path','source_sha256_start','source_sha256_end','nonconstant_moment_variables',
        'Taylor_table_terms','Taylor_table_degree','whole_grid_w5_remainder_power','whole_grid_w5_cells_rebuilt','PSD_sizes','row_counts','elapsed_milliseconds']}
    summary.update({'model_compressed_sha256':sha(OUT),'model_uncompressed_sha256':hashlib.sha256(raw).hexdigest(),
        'model_compressed_bytes':OUT.stat().st_size,'model_uncompressed_bytes':len(raw),'linear_rows':len(rows)})
    RECEIPT.write_text(json.dumps(summary,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:summary[k] for k in ['status','nonconstant_moment_variables','linear_rows','PSD_sizes','whole_grid_w5_cells_rebuilt','elapsed_milliseconds','model_compressed_bytes']}),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
