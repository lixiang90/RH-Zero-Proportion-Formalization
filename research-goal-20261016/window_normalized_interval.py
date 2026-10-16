"""Lean-friendly normalized integer-centre jets on a fixed 10^-30 grid.

The FTC sinc recurrence is applied to Taylor coefficients, not raw high
derivatives: b_(r+1)=(pi/z)*(pi^r*cos(z+r*pi/2)/(r+1)!-b_r).
At z=0 the moment is exact. Kernel coefficients combine linearly; w=k^2
coefficients are an ordinary convolution. Every interval operation rounds
outwards to the same 10^-30 grid. Inputs use elementary existing Lean bounds.
No global floor is asserted. The matching Lean arithmetic consumer remains
a separate obligation.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import hashlib,json,time
import window_interval_kernel as ik
ik.interval.Q=10**30 # Only this standalone process; frozen files are untouched.
I=ik.I;Q=10**30;HERE=Path(__file__).resolve().parent
PI=I(F(314159265358979323846,10**20),F(314159265358979323847,10**20))
THETA=I(F(707106781186547524400844362104,10**30),F(707106781186547524400844362105,10**30))
SIN=I(F(649636939080062444129454621098,10**30),F(649636939080062444132,10**21))
COS=I(F(760244597075630151252,10**21),F(760244597075630151253567702555,10**30))
Z=SIN/THETA

def normalized_sinc(z,sn,cs,order):
    e=[I(1)]
    for r in range(order):e.append(e[-1]*PI/(r+2))
    if z.l==0 and z.u==0:
        return [v*[1,0,-1,0][r%4] for r,v in enumerate(e)]
    assert z.l*z.u>0
    phase=[cs,-sn,-cs,sn];ans=[sn/z]
    ratio=PI/z
    for r in range(order):ans.append(ratio*(e[r]*phase[r%4]-ans[-1]))
    return ans

def integer_coefficients(n,order=23):
    sign=(-1)**n;total=[I(0) for _ in range(order+1)]
    for e in [-1,1]:
        values=normalized_sinc(PI*n+e*THETA,e*sign*SIN,sign*COS,order)
        for r,v in enumerate(values):total[r]+=v
    for j,c in enumerate(ik.COEFF[1:],1):
        for e in [-1,1]:
            m=n+e*j;values=normalized_sinc(PI*m,I(0),I((-1)**m),order)
            for r,v in enumerate(values):total[r]+=c*v
    ks=[v/(2*Z) for v in total]
    return [sum((ks[j]*ks[r-j] for j in range(r+1)),I(0)) for r in range(order+1)]

def main():
    start=time.monotonic();tables={n:integer_coefficients(n) for n in range(33)}
    old=json.loads((HERE/'window_interval_kernel.json').read_bytes());curvature=[]
    for n in range(1,17):
        coeff=[tables[n][j+2]*((j+1)*(j+2)) for j in range(14)]
        rem=F(44,7)**16*F(21,100)**14/factorial(14)
        lower=min(ik.bernstein_lower(coeff,-F(21,100)+F(42,100)*F(k,8),-F(21,100)+F(42,100)*F(k+1,8))-rem for k in range(8))
        threshold=F((F(old['regions'][n-1]['minimum_lower'])*10**12).__floor__(),10**12)
        assert lower>=threshold,(n,lower,threshold)
        curvature.append({'center':n,'lower':str(lower),'original_twice_alpha':str(threshold)})
    gram=json.loads((HERE/'cover-newwindow-gram.json').read_bytes());count=0;vmin=None;smin=None
    cache={}
    for row in gram['results']:
        for scalar in row['scalar_minorants']:
            p=F(scalar['anchor']);n=round(p);x=p-n
            if p not in cache:
                cs=tables[n];value=I(0);derivative=I(0)
                for j in range(23,-1,-1):value=value*x+cs[j]
                for j in range(22,-1,-1):derivative=derivative*x+cs[j+1]*(j+1)
                ev=F(44,7)**24*abs(x)**24/factorial(24);ed=F(44,7)**24*abs(x)**23/factorial(23)
                cache[p]=(I(value.l-ev,value.u+ev),I(derivative.l-ed,derivative.u+ed))
            v,d=cache[p];vm=v.l-F(scalar['value_lower']);slope=F(scalar['slope'])
            sm=F(scalar['slope_error_loss'])-max(abs(d.l-slope),abs(d.u-slope))*(F(21,100)+abs(p-scalar['integer_center']))
            assert vm>=0 and sm>=0,(scalar['pair'],p,vm,sm)
            count+=1;vmin=vm if vmin is None else min(vmin,vm);smin=sm if smin is None else min(smin,sm)
    out={'scope':__doc__,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'parameter_sha256':hashlib.sha256(ik.PARAM.read_bytes()).hexdigest(),
      'Gram_input_sha256':hashlib.sha256((HERE/'cover-newwindow-gram.json').read_bytes()).hexdigest(),
      'scale':Q,'normalization_interval':[str(Z.l),str(Z.u)],
      'elementary_input_intervals':{name:[str(v.l),str(v.u)] for name,v in [('pi',PI),('theta',THETA),('sin_theta',SIN),('cos_theta',COS)]},
      'integer_w_Taylor_coefficients':{str(n):[[str(v.l),str(v.u)] for v in values] for n,values in tables.items()},
      'curvature_checks':curvature,'scalar_checks':count,'minimum_value_margin':str(vmin),
      'minimum_slope_loss_margin':str(smin),'all_original_curvature_and_scalar_constants_preserved':True,
      'actual_interval_consumer_Lean_proven':False,'global_floor_proven':False,'seconds':time.monotonic()-start}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['scale','scalar_checks','all_original_curvature_and_scalar_constants_preserved','seconds']}))
if __name__=='__main__':main()
