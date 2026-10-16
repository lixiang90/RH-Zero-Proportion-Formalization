"""Exact rational interval UPPER bound from one feasible period-two sequence.

This is an obstruction to improving the current rank totals by a bounded
coboundary. It is emphatically not an energy lower bound or a zeta result.
Only the standard library is used; all interval endpoints are rational.
Pi is enclosed by the Machin arctangent identity and an alternating series.
Square root of two is enclosed by integer square root. Sin uses a Taylor
polynomial and its Lagrange remainder after exact interval range reduction.
"""
from pathlib import Path
from fractions import Fraction as F
from math import isqrt,factorial
import hashlib,json,time
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
Q=10**70
def down(x):return F(x.numerator*Q//x.denominator,Q)
def up(x):return -down(-x)
class I:
    def __init__(self,l,u=None):self.l=down(F(l));self.u=up(F(l if u is None else u));assert self.l<=self.u
    @staticmethod
    def lift(x):return x if isinstance(x,I) else I(x)
    def __add__(self,x):x=I.lift(x);return I(self.l+x.l,self.u+x.u)
    __radd__=__add__
    def __neg__(self):return I(-self.u,-self.l)
    def __sub__(self,x):return self+-I.lift(x)
    def __rsub__(self,x):return I.lift(x)+-self
    def __mul__(self,x):
        x=I.lift(x);v=[self.l*x.l,self.l*x.u,self.u*x.l,self.u*x.u];return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,x):
        x=I.lift(x);assert x.l*x.u>0;return self*I(1/x.u,1/x.l)
    def square(self):
        if self.l>=0:return I(self.l*self.l,self.u*self.u)
        if self.u<=0:return I(self.u*self.u,self.l*self.l)
        return I(0,max(self.l*self.l,self.u*self.u))

def atan_bound(q,n=120):
    x=F(1,q);s=sum((-1)**k*x**(2*k+1)/F(2*k+1) for k in range(n))
    nxt=(-1)**n*x**(2*n+1)/F(2*n+1)
    return I(min(s,s+nxt),max(s,s+nxt))
PI=16*atan_bound(5)-4*atan_bound(239)
sqscale=10**100;sr=isqrt(2*sqscale*sqscale);SQRT2=I(F(sr,sqscale),F(sr+1,sqscale))

def sin_interval(x):
    x=I.lift(x);m=round(float((x.l+x.u)/2)/(2*float((PI.l+PI.u)/2)))
    x=x-2*m*PI;assert max(abs(x.l),abs(x.u))<F(22,7)
    # P_101(x), and |R_102| <= (22/7)^103/103! for this odd polynomial.
    z=x*x;p=I(F((-1)**50,factorial(101)))
    for k in range(49,-1,-1):p=p*z+F((-1)**k,factorial(2*k+1))
    p=p*x;error=F(22,7)**103/F(factorial(103))
    return I(p.l-error,p.u+error)

COEF=[F(1),F(12310798,10**9),F(-15041681,10**9),F(3867664,10**9),F(6489926,10**9),F(-992327,10**9),F(5580097,10**9),F(-6846472,10**9),F(3781297,10**9),F(-5670353,10**9),F(3355089,10**9),F(-450523,10**9),F(-218483,10**9)]
NORMAL=2*sin_interval(SQRT2/2)/SQRT2
def amplitude(x):
    p=PI*x;s=sin_interval(p)
    k=sin_interval(p+SQRT2/2)/(2*p+SQRT2)+sin_interval(p-SQRT2/2)/(2*p-SQRT2)
    for j in range(1,13):
        assert x*x!=j*j
        k=k+COEF[j]*((-1)**j)*s*x/(PI*(x*x-j*j))
    return k/NORMAL

def main():
    start=time.monotonic();par=ROOT/'research-20261016/spectral-w10-refined-rational.json';doc=json.loads(par.read_text());d=doc['denominator']
    ranks=[sum(F(a,d) for i,j,a in doc['a_upper'] if j-i==r) for r in range(1,10)]
    pressure=sum(F(b,d) for b in doc['b_numerators'])
    gaps=[F(104168822065,10**11),F(197157891366,10**11)]
    energy=I(pressure*sum(gaps)/2)
    terms=[]
    for r,weight in enumerate(ranks,1):
        for i in range(2):
            span=sum(gaps[(i+j)%2] for j in range(r));term=amplitude(span).square()*weight/2;energy=energy+term
            terms.append({'rank':r,'start':i,'span_exact':str(span),'term_interval':[str(term.l),str(term.u)]})
    asserted_upper=F(4337,500000) # .008674, safely above the feasible value.
    assert energy.u<asserted_upper
    h=F(6721684105641188747759983512104999330646,10**40)
    ratio_upper=(h-pressure)/(1-asserted_upper)
    out={'scope':__doc__,'parameter_sha256':hashlib.sha256(par.read_bytes()).hexdigest(),
        'exact_periodic_gaps':list(map(str,gaps)),'rank_totals_exact':list(map(str,ranks)),
        'pressure_exact':str(pressure),'pi_interval':[str(PI.l),str(PI.u)],
        'sqrt_two_interval':[str(SQRT2.l),str(SQRT2.u)],'normalization_interval':[str(NORMAL.l),str(NORMAL.u)],
        'energy_interval':[str(energy.l),str(energy.u)],'energy_interval_float':[float(energy.l),float(energy.u)],
        'strict_energy_upper_bound_exact':str(asserted_upper),'ratio_ceiling_from_this_simple_upper_bound_exact':str(ratio_upper),
        'ratio_ceiling_percent_float':float(100*ratio_upper),'terms':terms,'seconds':time.monotonic()-start,
        'new_unconditional_zeta_bound_proven':False,'lean_verified':False,
        'restriction':'Only methods with unchanged W10 rank totals and pressure, with bounded telescoping potential.'}
    target=HERE/'global_periodic_upper_bound.json';target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['terms','scope','pi_interval','sqrt_two_interval','normalization_interval']}))
if __name__=='__main__':main()
