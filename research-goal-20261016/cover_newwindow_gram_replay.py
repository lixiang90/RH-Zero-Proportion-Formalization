"""Independent stdlib replay of the new-window 69 coherent Gram certificates.

Rebuilds integer kernel values by the exact closed formula, integrates the
saved w' Taylor polynomial for point values, checks scalar slope payments,
curvature choices, matrix assembly, Az=b, LDL positivity and Gram floors.
The saved interval jets still require their actual-kernel Lean connection.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial,isqrt,comb
import argparse, functools, hashlib, json, time
from cover_correlated_replay import J, ScalarReplay
HERE=Path(__file__).parent;ROOT=HERE.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def add(x,y):return x+y
def neg(x):return J(-x.u,-x.l)
def sub(x,y):return x+neg(y)
def div(x,y):
    assert y.l*y.u>0
    return x*J(1/y.u,1/y.l)
def square(x):return J(0 if x.l*x.u<=0 else min(x.l*x.l,x.u*x.u),max(x.l*x.l,x.u*x.u))
def atan(q,n=100):
    z=F(1,q);s=sum(((-1)**k*z**(2*k+1)/F(2*k+1) for k in range(n)),F(0));r=(-1)**n*z**(2*n+1)/F(2*n+1)
    return J(min(s,s+r),max(s,s+r))
def sinpoint(x,n=60):
    s=sum(((-1)**k*x**(2*k+1)/F(factorial(2*k+1)) for k in range(n)),F(0));r=(-1)**n*x**(2*n+1)/F(factorial(2*n+1))
    return min(s,s+r),max(s,s+r)

class Values:
    def __init__(self,table):
        self.scalar=ScalarReplay(table);self.coefficients=[F(n,10**9) for n in table['receipt']['coefficient_numerators_1e9']]
        self.pi=sub(16*atan(5),4*atan(239));scale=10**100;n=isqrt(2*scale*scale);theta=J(F(n,2*scale),F(n+1,2*scale))
        sn=J(sinpoint(theta.l)[0],sinpoint(theta.u)[1]);self.Z=div(sn,theta)
    @functools.lru_cache(None)
    def integer(self,n):
        # At integer n every cosine mode vanishes except its removable sinc
        # term, while the main sqrt(2) mode simplifies without a sine.
        denom=sub(2*n*n*self.pi*self.pi,J(1));base=div(J((-1)**(n+1)),denom)
        extra=div(J(self.coefficients[n] if n<len(self.coefficients) else 0),2*self.Z)
        return square(base+extra)
    @functools.lru_cache(10000)
    def at(self,p):
        n=round(p);x=p-n;coeff=self.scalar.coeff[n];value=J(0)
        for j in range(len(coeff)-1,-1,-1):value=value*J(x)+coeff[j]*F(1,j+1)
        value=self.integer(n)+value*J(x);err=F(44,7)**24*abs(x)**24/factorial(24)
        derivative=self.scalar.poly(n,J(x),0);ed=F(44,7)**24*abs(x)**23/factorial(23)
        return J(value.l-err,value.u+err),J(derivative.l-ed,derivative.u+ed)

def curvature_check(doc):
    bounds={}
    for region in doc['regions']:
        n=int(region['center']);center=F(region['center']);left=F(region['left']);right=F(region['right']);order=region['derivative_order']
        jets=[J(l,u) for l,u in region['jet_intervals']];coeff=[jets[j+2]*F(1,factorial(j)) for j in range(order-2)]
        radius=max(abs(left-center),abs(right-center));rem=F(44,7)**order*radius**(order-2)/factorial(order-2)
        assert rem==F(region['taylor_remainder']) and F(region['minimum_lower'])>0
        for row in region['subintervals']:
            l=F(row['left'])-center;r=F(row['right'])-center;degree=len(coeff)-1;power=[J(0) for _ in coeff]
            for j,c in enumerate(coeff):
                for k in range(j+1):power[k]=power[k]+c*(comb(j,k)*l**(j-k)*(r-l)**k)
            beta=[sum((power[j]*F(comb(k,j),comb(degree,j)) for j in range(k+1)),J(0)) for k in range(degree+1)]
            assert min(v.l for v in beta)-rem>=F(row['w_second_lower'])>=F(region['minimum_lower'])
        bounds[n]=F(region['minimum_lower'])
    return bounds

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--certificate',type=Path,default=HERE/'cover-newwindow-gram.json')
    ap.add_argument('--output',type=Path,default=HERE/'cover-newwindow-gram-replay.json');args=ap.parse_args();start=time.monotonic()
    doc=json.loads(args.certificate.read_bytes());receipt=doc['receipt'];tablepath=HERE/'cover_newjet.json';table=json.loads(tablepath.read_bytes())
    curvaturepath=HERE/'window_interval_kernel.json';curves=json.loads(curvaturepath.read_bytes());params_path=ROOT/'research-20261016-followup/window_reweight_rational.json';params=json.loads(params_path.read_bytes())
    assert sha(tablepath)==receipt['Taylor_table_sha256'] and sha(curvaturepath)==receipt['curvature_source_sha256'] and sha(params_path)==receipt['parameter_sha256']
    m2=curvature_check(curves);point=Values(table);D=params['denominator'];terms=[(i,j,F(a,D)) for i,j,a in params['a_upper'] if a];bs=[F(b,D) for b in params['b_numerators']]
    radius=F(receipt['radius']);floor=F(receipt['floor']);minimum=None;diagonal_minimum=None;rows=[]
    for k,region in enumerate(doc['results'],1):
        q=list(map(F,region['anchor']));integers=region['integer_gaps'];C=sum(b*x for b,x in zip(bs,q));gradient=bs.copy();A=[[F(0) for _ in range(9)] for _ in range(9)];diag=[F(0)]*9
        assert len(region['scalar_minorants'])==len(terms)
        for (i,j,a),row in zip(terms,region['scalar_minorants']):
            assert row['pair']==[i,j];anchor=sum(q[i:j]);n=sum(integers[i:j]);assert row['integer_center']==n and F(row['anchor'])==anchor and abs(anchor-n)<radius
            v,d=point.at(anchor);vlow=F(row['value_lower']);slope=F(row['slope']);loss=F(row['slope_error_loss']);alpha=F(row['quadratic_coefficient'])
            assert vlow<=v.l and loss>=max(abs(d.l-slope),abs(d.u-slope))*(radius+abs(anchor-n))
            assert 0<2*alpha<=m2[n]
            C+=a*(vlow-loss)
            if j==i+1:diag[i]+=a*alpha
            for u in range(i,j):
                gradient[u]+=a*slope
                for z in range(i,j):A[u][z]+=a*alpha
        assert C==F(region['quadratic_center_constant']) and gradient==list(map(F,region['gradient'])) and A==[list(map(F,row)) for row in region['matrix']]
        inverse=list(map(F,region['inverse_gradient']));L=[list(map(F,row)) for row in region['LDL_unit_lower']];dd=list(map(F,region['LDL_positive_diagonal']))
        assert all(d>0 for d in dd) and all(L[i][j]==int(i==j) for i in range(9) for j in range(i,9))
        assert all(A[i][j]==sum(L[i][z]*dd[z]*L[j][z] for z in range(9)) for i in range(9) for j in range(9))
        assert all(sum(A[i][j]*inverse[j] for j in range(9))==gradient[i] for i in range(9))
        penalty=sum(x*y for x,y in zip(gradient,inverse))/4;bound=C-penalty
        assert penalty==F(region['Gram_correction']) and bound==F(region['lower_bound']) and bound>=floor
        assert all(d>0 for d in diag);diagonal_bound=C-sum(v*v/(4*d) for v,d in zip(gradient,diag))
        rows.append({'integer_gaps':integers,'anchor':region['anchor'],'constant':str(C),'gradient':list(map(str,gradient)),'diagonal':list(map(str,diag)),
          'diagonal_only_lower_bound':str(diagonal_bound),'passes_original_884_floor':diagonal_bound>=F(221,25000)})
        minimum=bound if minimum is None else min(minimum,bound);diagonal_minimum=diagonal_bound if diagonal_minimum is None else min(diagonal_minimum,diagonal_bound)
        if k%10==0:print(json.dumps({'checked':k,'seconds':time.monotonic()-start}),flush=True)
    result={'scope':__doc__,'passed':True,'certificate_sha256':sha(args.certificate),'script_sha256':sha(Path(__file__)),'Taylor_table_sha256':sha(tablepath),
      'curvature_certificate_sha256':sha(curvaturepath),'parameter_sha256':sha(params_path),'patterns':len(rows),'scalar_minorants':sum(len(r['scalar_minorants']) for r in doc['results']),
      'minimum_Gram_lower_bound':str(minimum),'minimum_Gram_lower_bound_hint':float(minimum),'minimum_diagonal_only_lower_bound':str(diagonal_minimum),
      'minimum_diagonal_only_lower_bound_hint':float(diagonal_minimum),'all_diagonal_bounds_also_pass_original_884_floor':all(r['passes_original_884_floor'] for r in rows),
      'all_integer_point_values_independently_rebuilt':True,'all_Taylor_point_slope_payments_checked':True,'all_curvature_Bernstein_checks_replayed':True,
      'all_matrix_and_LDL_identities_checked':True,'actual_kernel_Lean_connection':False,'global_minimizer_chamber_cover':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'receipt':result,'diagonal_bounds':rows},separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(result),flush=True)
if __name__=='__main__':main()
