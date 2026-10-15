"""Exact rational interval evaluation of the refuted W10 parameters at one point.

This is an independent arithmetic certificate, not a Lean theorem. It uses
Machin's identity, alternating Taylor enclosures, and exact Fourier identities.
"""
from pathlib import Path
from fractions import Fraction as Q
import importlib.util,json,hashlib
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('intervals',HERE.parent/'scripts/am_lossless_majorant_certificate.py')
t=importlib.util.module_from_spec(spec);spec.loader.exec_module(t)
S=10**40
def outward(a):return (Q(a[0].numerator*S//a[0].denominator,S),Q(-((-a[1].numerator*S)//a[1].denominator),S))
def add(a,b):return outward(t.add(a,b))
def mul(a,b):return outward(t.mul(a,b))
def scale(a,k):return outward(t.scale(a,k))
def divide(a,b):
    assert not b[0]<=0<=b[1]
    if b[1]<0:return divide(scale(a,-1),scale(b,-1))
    return outward(t.divide(a,b))
pi=outward(t.add(t.scale(t.atan_interval(5),16),t.scale(t.atan_interval(239),-4)))
norm=outward(t.trig_interval((Q(1,2),Q(1,2)),True))
cot=divide(outward(t.trig_interval((Q(1,2),Q(1,2)))),norm)
def kernel_interval(x):
    # Reduce pi*x modulo pi to a residual pi*r in[-pi/2,pi/2].
    k=(x+Q(1,2)).numerator//(x+Q(1,2)).denominator;r=x-k
    angle=scale(pi,r);square=scale(mul(pi,pi),r*r)
    sin=scale(mul(angle,outward(t.trig_interval(square,True))),(-1)**k)
    cos=scale(outward(t.trig_interval(square)),(-1)**k)
    pix=scale(pi,x)
    # Half the two shifted sinc terms, normalized by sinc(sqrt(1/2)).
    base=divide(add(mul(mul(pix,cot),sin),scale(cos,Q(-1,2))),
        add(mul(pix,pix),(Q(-1,2),Q(-1,2))))
    correction=(Q(0),Q(0))
    for j,c in enumerate(t.CS,1):
        correction=add(correction,divide(scale(sin,Q(c,10**9)*(-1)**j*x),scale(pi,x*x-j*j)))
    return add(base,divide(correction,norm))
source=HERE/'spectral-w10-rational.json';doc=json.loads(source.read_text());D=doc['denominator']
gapnums=[1039243369,1967418424,1037486930,1042471508,2911055661,
         1042471508,1037486930,1967418424,1039243369]
g=[Q(v,10**9) for v in gapnums];assert min(g)>Q(17,20)
points=[Q(0)]
for v in g:points.append(points[-1]+v)
pressure=sum((Q(v,D)*x for v,x in zip(doc['b_numerators'],g)),Q(0));total=(pressure,pressure)
for i,j,v in doc['a_upper']:
    if not v:continue
    lower,upper=kernel_interval(points[j]-points[i])
    squared=(Q(0) if lower<=0<=upper else min(lower*lower,upper*upper),max(lower*lower,upper*upper))
    total=add(total,scale(squared,Q(v,D)))
assert total[1]<Q(433,50000)
def small(a,den=10**20):
    return [str(Q(a[0].numerator*den//a[0].denominator,den)),str(Q(-((-a[1].numerator*den)//a[1].denominator),den))]
record={'scope':'Exact rational interval counterexample; independent arithmetic, not a Lean theorem',
    'candidate':source.name,'candidate_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
    'gap_numerators':gapnums,'gap_denominator':10**9,'all_gaps_gt17_over20':True,
    'F_exact_outward_interval':small(total),'F_decimal_interval':[float(v) for v in total],
    'refuted_floor_exact':'433/50000','certified_strict_upper':'17299/2000000 =0.0086495',
    'upper_lt_refuted_floor':total[1]<Q(433,50000),
    'pi_exact_interval':small(pi,10**35),
    'identities':'Machin; alternating13-term cos/sinc Taylor; exact normalized Fourier formula for K; interval arithmetic rounded outward to1e-40'}
assert total[1]<Q(17299,2000000)
(HERE/'spectral-w10-counterexample-interval.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
