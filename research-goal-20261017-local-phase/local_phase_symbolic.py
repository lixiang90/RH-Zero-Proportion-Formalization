"""Exact symbolic rational cross-multiplication of the regular local formula.

The stated sinc periodicity and sin/cos substitutions are assumptions of this
algebra audit. No point evaluation, transcendental approximation, solver, Lean
or search is run. Actual analytic sources and domains are recorded separately.
"""
from pathlib import Path
import hashlib
import json
import time

HERE = Path(__file__).resolve().parent
NAMES = ['x','n','j','pi','alpha','Z','S','c','sigma_n','sigma_j','d_n','d_j']
ZERO = (0,)*len(NAMES)


def padd(a,b):
    out = a.copy()
    for m,v in b.items():
        out[m] = out.get(m,0)+v
        if not out[m]:
            del out[m]
    return out


def pneg(a):
    return {m:-v for m,v in a.items()}


def pmul(a,b):
    out = {}
    for m,v in a.items():
        for n,w in b.items():
            e = tuple(i+j for i,j in zip(m,n))
            out[e] = out.get(e,0)+v*w
            if not out[e]:
                del out[e]
    return out


class RF:
    def __init__(self,num,den=None):
        self.num = {ZERO:num} if isinstance(num,int) and num else ({} if num==0 else num)
        self.den = {ZERO:1} if den is None else den
        assert self.den

    @staticmethod
    def lift(a):
        return RF(a) if isinstance(a,int) else a

    def __neg__(self):
        return RF(pneg(self.num),self.den)

    def __add__(self,b):
        b = RF.lift(b)
        return RF(padd(pmul(self.num,b.den),pmul(b.num,self.den)),pmul(self.den,b.den))

    __radd__ = __add__

    def __sub__(self,b):
        return self+-RF.lift(b)

    def __rsub__(self,b):
        return RF.lift(b)+-self

    def __mul__(self,b):
        b = RF.lift(b)
        return RF(pmul(self.num,b.num),pmul(self.den,b.den))

    __rmul__ = __mul__

    def __truediv__(self,b):
        b = RF.lift(b)
        assert b.num
        return RF(pmul(self.num,b.den),pmul(self.den,b.num))

    def __rtruediv__(self,b):
        return RF.lift(b)/self

    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        out = RF(1)
        for _ in range(n):
            out = out*self
        return out


def var(name):
    e = list(ZERO)
    e[NAMES.index(name)] = 1
    return RF({tuple(e):1})


def same(a,b):
    assert not padd(pmul(a.num,b.den),pneg(pmul(b.num,a.den)))


def main():
    began = time.monotonic()
    x,n,j,pi,alpha,Z,S,c,sn,sj,dn,dj = map(var,NAMES)
    delta = x-n
    sinx = sn*pi*delta*S
    cosx = sn*c
    base_old = (cosx-2*alpha*pi*x*sinx)/(1-2*pi**2*x**2)
    base_C = sn*delta*(2*alpha*pi**2*x/(2*pi**2*x**2-1))
    D = sn/(1-2*pi**2*x**2)
    same(base_old,base_C*S+D*c)
    active_old = dn/(2*Z)*(S+delta*S/(x+n))
    active_C = dn*x/(Z*(x+n))
    same(active_old,active_C*S)
    nonactive_old = (dj/Z)*sj*x*sinx/(pi*(x**2-j**2))
    nonactive_C = sn*delta*(dj/Z)*sj*x/(x**2-j**2)
    same(nonactive_old,nonactive_C*S)
    same(base_old+active_old+nonactive_old,(base_C+active_C+nonactive_C)*S+D*c)
    same(dn*n/(Z*(n+n)),dn/(2*Z))
    out = {'scope':__doc__,
           'status':'symbolic_rational_identities_verified_under_stated_trigonometric_substitutions',
           'indeterminates':NAMES,'coefficient_ring':'integer multivariate polynomials with rational-function fractions',
           'checks':['normalized_base_two_phase_terms','active_sinc_pair_without_delta_division',
                     'arbitrary_nonactive_mode','combined_local_formula','active_centre_value'],
           'all_cross_multiplied_polynomials_exactly_zero':True,
           'assumed_analytic_inputs':['sin(pi*x)=(-1)^n*pi*(x-n)*sinc(pi*(x-n))',
                                     'cos(pi*x)=(-1)^n*cos(pi*(x-n))',
                                     'active paired-sinc periodicity including x=n',
                                     'actual finite-sinc and normalized base formulas',
                                     'stated domain makes all displayed denominators nonzero'],
           'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           'new_point_evaluations':0,'solver_calls':0,'Lean_invocations':0,
           'new_actual_kernel_identity_Lean_proven':False,'new_exclusion':False,
           'elapsed_seconds':time.monotonic()-began}
    path = HERE/'symbolic-identity-audit.json'
    assert not path.exists()
    path.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'status':out['status'],'identities':len(out['checks']),
                      'elapsed_seconds':out['elapsed_seconds']}))


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled')
    main()
