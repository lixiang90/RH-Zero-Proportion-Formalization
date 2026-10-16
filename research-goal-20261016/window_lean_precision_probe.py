"""Test jet evidence using only elementary inputs available to ordinary Lean.

This does not edit the frozen discovery oracle. Integer-centred sinc phases
are exact; pi uses 20 decimal places, theta 30, and sin/cos theta use explicit
order-20 bounds. A Lean proof of the input enclosures is being checked.
All output remains finite numerical evidence until the analytic consumer
and exact arithmetic checker are proved in Lean.
"""
from pathlib import Path
from fractions import Fraction as F
from math import comb,factorial
import argparse,hashlib,json,time
import window_interval_kernel as ik
I=ik.I;HERE=Path(__file__).resolve().parent
PI=I(F(314159265358979323846,10**20),F(314159265358979323847,10**20))
THETA=I(F(707106781186547524400844362104,10**30),F(707106781186547524400844362105,10**30))
SIN=I(F(649636939080062444129454621098,10**30),F(649636939080062444132,10**21))
COS=I(F(760244597075630151252,10**21),F(760244597075630151253567702555,10**30))
Z=SIN/THETA

def integer_jet(n,order=23):
    total=[I(0) for _ in range(order+1)]
    sign=(-1)**n
    for e in [-1,1]:
        z=PI*n+e*THETA
        jets=ik.sinc_jet(z,e*sign*SIN,sign*COS,order)
        for r,v in enumerate(jets):total[r]+=v
    for j,c in enumerate(ik.COEFF[1:],1):
        for e in [-1,1]:
            m=n+e*j
            jets=ik.sinc_jet(PI*m,I(0),I((-1)**m),order)
            for r,v in enumerate(jets):total[r]+=c*v
    kp=[v*ik.ipow(PI,r)/(2*Z) for r,v in enumerate(total)]
    return [sum((comb(r,j)*kp[j]*kp[r-j] for j in range(r+1)),I(0)) for r in range(order+1)]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--maximum',type=int,default=32)
    ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));args=ap.parse_args()
    start=time.monotonic();rows=[];tables={}
    original=json.loads((HERE/'window_interval_kernel.json').read_bytes())
    for n in range(args.maximum+1):
        jets=integer_jet(n)
        tables[n]=[[str(v.l),str(v.u)] for v in jets]
        if n and n<=16:
            p=F(n);left=p-F(21,100);right=p+F(21,100)
            coeff=[jets[j+2]*F(1,factorial(j)) for j in range(14)]
            rem=F(44,7)**16*F(21,100)**14/factorial(14)
            lower=min(ik.bernstein_lower(coeff,left-p+(right-left)*F(k,8),left-p+(right-left)*F(k+1,8))-rem for k in range(8))
            old=F(original['regions'][n-1]['minimum_lower'])
            oldalpha=F((old*10**12).numerator//(old*10**12).denominator,2*10**12)
            rows.append({'center':n,'w_second_lower':str(lower),'positive':lower>0,
                         'original_twice_alpha':str(2*oldalpha),'proves_original_curvature_constant':lower>=2*oldalpha})
        print(json.dumps({'center':n,'seconds':time.monotonic()-start}),flush=True)
    out={'scope':__doc__,'parameter_sha256':hashlib.sha256(ik.PARAM.read_bytes()).hexdigest(),
      'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'input_intervals':{name:[str(v.l),str(v.u)] for name,v in [('pi',PI),('theta',THETA),('sin_theta',SIN),('cos_theta',COS)]},
      'integer_w_jets':tables,'convexity':rows,'all_convexity_positive':all(r['positive'] for r in rows),
      'all_original_curvatures_preserved':all(r['proves_original_curvature_constant'] for r in rows),
      'Lean_input_enclosures_proven':False,'actual_jet_Lean_connection_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['all_convexity_positive','all_original_curvatures_preserved','seconds']}),flush=True)
if __name__=='__main__':main()
