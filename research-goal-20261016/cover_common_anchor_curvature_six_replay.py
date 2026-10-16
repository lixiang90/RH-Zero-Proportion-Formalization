"""Read-only stdlib replay: scalar jets, SPD witnesses, and rational LP payment.

The pure algebraic monomial-row builder is reused from the pinned producer
via an explicit AST whitelist, without importing its numerical modules.
Scalar interval Horner/remainders and actual-Hessian witnesses are
recomputed here. No numerical solver or Lean is called.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations_with_replacement
from collections import Counter
from math import factorial
from types import SimpleNamespace
import argparse,ast,hashlib,json,sys,time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;SC=32768
SOURCE=HERE/'cover_common_anchor_curvature_six.py'
DATA=HERE/'cover-common-anchor-curvature-six.json'
OUT=HERE/'cover-common-anchor-curvature-six-replay.json'
MON=[(i,) for i in range(9)]+list(combinations_with_replacement(range(9),2))+list(combinations_with_replacement(range(9),3))
INDEX={t:k for k,t in enumerate(MON)};N=len(MON)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def mul(a,b):
    v=[x*y for x in a for y in b];return min(v),max(v)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    start=time.monotonic();doc=json.loads(DATA.read_bytes())
    assert len(doc['cases'])==6 and doc['LP_calls']==4 and doc['new_cell_exclusions']==0
    for rel,h in doc['input_sha256'].items():assert sha(ROOT/rel)==h
    params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    table=json.loads((HERE/'cover_newjet.json').read_bytes());step=table['receipt']['grid_step'];width=SC//step
    terms=[tuple(r) for r in params['a_upper'] if r[2]];den=params['denominator']
    coeff={int(n):[(F(l),F(u)) for l,u in cs] for n,cs in table['integer_taylor_coefficients'].items()}
    allspans=[(i,i+1) for i in range(9)]+[(i,j) for i in range(10) for j in range(i+2,10)]
    lookup={p:k for k,p in enumerate(allspans)};M24=F(44,7)**24
    def poly(n,x,d):
        value=(F(0),F(0))
        for j in range(len(coeff[n])-1,d-1,-1):
            a,b=mul(value,x);c,e=coeff[n][j];factor=F(factorial(j),factorial(j-d));value=(a+factor*c,b+factor*e)
        return value
    @lru_cache(None)
    def jet(P,d):
        x=F(P,2*SC);n=round(x);h=x-n;l,u=poly(n,(h,h),d-1)
        err=M24*abs(h)**(24-d)/factorial(24-d);return l-err,u+err
    @lru_cache(None)
    def sixth(k):
        n=round(F(2*k+1,2*step));x=(F(k,step)-n,F(k+1,step)-n)
        l,u=poly(n,x,5);err=M24*F(1,2)**18/factorial(18);return l-err,u+err
    tree=ast.parse(SOURCE.read_text());names={'add','product_range','rows_for'}
    selected=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in names]
    assert {n.name for n in selected}==names
    namespace={'F':F,'MON':MON,'INDEX':INDEX,'N':N,'SC':SC,'old':SimpleNamespace(g=SimpleNamespace(ALL=allspans))}
    exec(compile(ast.Module(body=selected,type_ignores=[]),str(SOURCE),'exec'),namespace)
    spd=[];direction_sign_flips=[];upper=[];signed_upper=[]
    for row in doc['cases']:
        state=row['cell'];free=[i for i in range(9) if state[0][i]>123*SC//128]
        assert free==row['strict_free_coordinates'];actualpoints=[]
        for point in row['canonical_points']:
            kind=point['kind']
            prefix=[0]+[(state[0][lookup[0,j]]+state[1][lookup[0,j]]) if kind=='mean' else 2*state[int(kind=='upper')][lookup[0,j]] for j in range(1,10)]
            assert prefix==point['prefix_twice_SC']
            assert all(2*l<=prefix[j]-prefix[i]<=2*u for (i,j),l,u in zip(allspans,*state))
            tight=[jet(prefix[j]-prefix[i],2) for i,j,a in terms]
            vals=[tuple(map(F,p)) for p in point['actual_w2_intervals']]
            assert all(a<=l<=u<=b for (l,u),(a,b) in zip(tight,vals));actualpoints.append(vals)
            mid=[[F(0) for j in range(9)] for i in range(9)];err=[[F(0) for j in range(9)] for i in range(9)]
            for (i,j,a),(l,u) in zip(terms,vals):
                for r in range(i,j):
                    for s in range(i,j):mid[r][s]+=F(a,den)*(l+u)/2;err[r][s]+=F(a,den)*(u-l)/2
            pay=[sum(a) for a in err];assert pay==list(map(F,point['diagonal_error_payment']))
            witness=point['lower_Hessian_LDL']
            if witness:
                L=[list(map(F,r)) for r in witness['unit_lower']];D=list(map(F,witness['positive_diagonal']));assert len(D)==len(free) and all(d>0 for d in D)
                for i,r in enumerate(free):
                    assert L[i][i]==1 and all(L[i][k]==0 for k in range(i+1,len(free)))
                    for j,s in enumerate(free):assert mid[r][s]-(pay[r] if r==s else 0)==sum(L[i][k]*D[k]*L[j][k] for k in range(len(free)))
                spd.append([row['case'],kind])
        if not row['LP_calls']:continue
        d=row['direction'];norm=sum(v*v for v in d);assert norm==int(row['direction_norm_squared'])
        assert all(not v or i in free for i,v in enumerate(d))
        flips=[]
        for vals,(kind,lo,up) in zip(actualpoints,row['canonical_normalized_curvature_intervals']):
            gotlo=sum(F(a*sum(d[i:j])**2,den*norm)*l for (i,j,a),(l,u) in zip(terms,vals))
            gotup=sum(F(a*sum(d[i:j])**2,den*norm)*u for (i,j,a),(l,u) in zip(terms,vals))
            assert gotlo==F(lo) and gotup==F(up)
            if gotlo>0:flips.append(kind)
        if flips:direction_sign_flips.append([row['case'],flips])
        anchor=list(map(F,row['anchor_gaps']));radius=list(map(F,row['coordinate_normalization_radius']))
        C=E=Eplus=F(0);pc=[F(0)]*N
        for data,(i,j,a) in zip(row['scalar_cubic_data'],terms):
            rho=F(a*sum(d[i:j])**2,den*norm);s0=sum(anchor[i:j]);P=2*SC*s0;assert P.denominator==1
            z=lookup[i,j];r=max(s0-F(state[0][z],SC),F(state[1][z],SC)-s0)
            tight=[jet(int(P),k) for k in (2,3,4,5)]
            vals=[tuple(map(F,p)) for p in data['derivative_intervals']]
            assert all(a<=l<=u<=b for (l,u),(a,b) in zip(tight,vals))
            m=[(l+u)/2 for l,u in vals];ee=[(u-l)/2 for l,u in vals]
            first=state[0][z]//width;last=(max(state[0][z]+1,state[1][z])+width-1)//width
            sixth_intervals=[sixth(k) for k in range(first,last)]
            tightM=max(max(abs(l),abs(u)) for l,u in sixth_intervals)
            Mplus=max(F(0),max(u for l,u in sixth_intervals))
            M=F(data['sixth_absolute_bound']);assert M>=tightM
            anchorpay=sum(ee[k]*r**k/factorial(k) for k in range(4))
            payment=anchorpay+M*r**4/24
            assert data['rho']==str(rho) and data['radius']==str(r) and data['anchor_span']==str(s0)
            assert F(data['sixth_absolute_bound'])==M and F(data['error_payment'])==payment
            C+=rho*m[0];E+=rho*payment;Eplus+=rho*(anchorpay+Mplus*r**4/24)
            for degree in (1,2,3):
                for mon in combinations_with_replacement(range(i,j),degree):
                    v=rho*m[degree]
                    for mult in Counter(mon).values():v/=factorial(mult)
                    for k in mon:v*=radius[k]
                    pc[INDEX[mon]]+=v
        assert C==F(row['polynomial_constant']) and E==F(row['polynomial_error']) and pc==list(map(F,row['polynomial_coefficients']))
        rows,rhs,bounds,kinds=namespace['rows_for'](state,anchor,radius);assert len(rows)==row['LP_rows']==3510
        result=row['LP_result'];residual=pc.copy();paid=F(0);q=result['dual_quantum']
        for k,w in result['nonzero_integer_dual']:
            lam=F(int(w),q);assert lam>=0;paid+=lam*rhs[k]
            for j,a in rows[k].items():residual[j]-=lam*a
        boxpay=sum(a*(u if a>=0 else l) for a,(l,u) in zip(residual,bounds))
        bound=C+E+paid+boxpay
        assert residual==list(map(F,result['uncancelled_polynomial_coefficients']))
        assert paid==F(result['dual_payment']) and boxpay==F(result['residual_box_payment']) and bound==F(result['exact_upper'])>0
        upper.append([row['case'],str(bound)])
        signedbound=C+Eplus+paid+boxpay
        assert Eplus<=E and signedbound>0
        signed_upper.append({'case':row['case'],'signed_sixth_error_payment':str(Eplus),
            'same_dual_signed_sixth_upper':str(signedbound),'upper_display_only':float(signedbound)})
    assert spd==[[0,'mean'],[3,'upper']]
    assert [c for c,k in direction_sign_flips]==[1,2,4]
    assert not any(n.split('.')[0] in ('numpy','scipy','scs') for n in sys.modules)
    result={'status':'exact_scalar_obstructions_and_cubic_upper_payments_replayed','scope':__doc__,
        'input_sha256':{p.relative_to(ROOT).as_posix():sha(p) for p in [Path(__file__),SOURCE,DATA]},
        'actual_Hessian_SPD_witnesses':spd,'fixed_direction_sign_flip_witnesses':direction_sign_flips,
        'exact_cubic_upper_payments':upper,'new_cell_exclusions':0,'solver_calls':0,'Lean_runs':0,
        'one_sided_sixth_remainder_same_dual':signed_upper,
        'whole_fixed_direction_route_refuted':False,'elapsed_milliseconds':int(1000*(time.monotonic()-start))}
    if args.write_receipt:OUT.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:result[k] for k in ['status','actual_Hessian_SPD_witnesses','fixed_direction_sign_flip_witnesses','one_sided_sixth_remainder_same_dual','new_cell_exclusions','elapsed_milliseconds']}))

if __name__=='__main__':main()
