"""Independent source SZ-pair/IV operator evaluation; definitions only.

Keeps separate nonnegative p/n counters and source rounding branches. It does
not import the O provider or use its signed-endpoint arithmetic implementation.
"""
import ast
from fractions import Fraction
import re

def sub(a,b):return max(a-b,0)
def div(a,b):return a//b if b else 0
def up(a,b):return div(sub(a+b,1),b)

class Z:
    def __init__(self,p=0,n=0):
        assert type(p) is int and type(n) is int and p>=0 and n>=0
        self.p,self.n=p,n
    @property
    def v(self):return self.p-self.n
    def ge0(self):return self.n<=self.p
    def le(self,b):return self.p+b.n<=b.p+self.n
    def plus(self,b):return Z(self.p+b.p,self.n+b.n)
    def minus(self,b):return Z(self.p+b.n,self.n+b.p)
    def neg(self):return Z(self.n,self.p)
    def times(self,b):return Z(self.p*b.p+self.n*b.n,self.p*b.n+self.n*b.p)
    def natural(self,m):return Z(m*self.p,m*self.n)
    def floor(self,d):
        return Z(div(sub(self.p,self.n),d),0) if self.ge0() else Z(0,up(sub(self.n,self.p),d))
    def ceil(self,d):
        return Z(up(sub(self.p,self.n),d),0) if self.ge0() else Z(0,div(sub(self.n,self.p),d))
    def minimum(self,b):return self if self.le(b) else b
    def maximum(self,b):return b if self.le(b) else self

class I:
    def __init__(self,l,h,z):self.l,self.h,self.z=l,h,z
    @classmethod
    def naturals(cls,l,h,z):return cls(Z(l),Z(h),z)
    def plus(self,b):assert self.z==b.z;return I(self.l.plus(b.l),self.h.plus(b.h),self.z)
    def minus(self,b):assert self.z==b.z;return I(self.l.minus(b.h),self.h.minus(b.l),self.z)
    def neg(self):return I(self.h.neg(),self.l.neg(),self.z)
    def natural(self,m):return I(self.l.natural(m),self.h.natural(m),self.z)
    def times(self,b):
        assert self.z==b.z
        a,b1,c,d=self.l.times(b.l),self.l.times(b.h),self.h.times(b.l),self.h.times(b.h)
        low=a.minimum(b1).minimum(c.minimum(d));high=a.maximum(b1).maximum(c.maximum(d))
        return I(low.floor(self.z),high.ceil(self.z),self.z)
    def coefficient(self,b):
        assert self.z==b.z and self.l.ge0()
        low=(self.l if b.l.ge0() else self.h).times(b.l)
        high=(self.h if b.h.ge0() else self.l).times(b.h)
        return I(low.floor(self.z),high.ceil(self.z),self.z)
    def divide(self,d):return I(self.l.floor(d),self.h.ceil(d),self.z)
    def positive_divide(self,e0,e1):
        assert 0<e0<=e1
        low=self.l.natural(self.z).floor(e1 if self.l.ge0() else e0)
        high=self.h.natural(self.z).ceil(e0 if self.h.ge0() else e1)
        return I(low,high,self.z)
    def signed_natural(self,negative,m):
        out=self.natural(m);return out.neg() if negative else out
    def data(self):return [self.l.v,self.h.v]

def read_parameters(text):
    def n(name):
        found=re.findall(r'(?m)^noncomputable def '+name+r' : ℕ := (\d+)\s*$',text)
        assert found and len(set(found))==1;return int(found[0])
    p={k:n(k) for k in ['DZ','DZ2','SC','PLN','PUN','E20','ERRD','E9','GAM0','GAM1']}
    assert p['SC']==32768 and p['DZ']==2*p['DZ2']
    for k in ['PIC','PI2C','G1C','G2C','RHOC','SIGC','TAUC']:
        m=re.findall(r'(?m)^noncomputable def '+k+r' : IV := IV.ofN (\d+) (\d+)\s*$',text)
        assert len(m)==1;p[k]=tuple(map(int,m[0]))
    p['CE']=ast.literal_eval(re.search(r'def CE : List[^\n]*:=\s*(\[[\s\S]*?\])',text)[1].replace('true','True').replace('false','False'))
    cj=text.split('noncomputable def CJ (j : ℕ)',1)[1].split('structure Acc',1)[0]
    p['CJ']={int(k):(int(v),b=='true') for k,v,b in re.findall(r'\| (\d+) => \((\d+), (true|false)\)',cj)}
    fa=text.split('noncomputable def FA (c : CellA)',1)[1].split('noncomputable def nearOn',1)[0]
    assert [(int(k),int(v),b=='true') for k,v,b in re.findall(r'\b(\d+) (\d+) (true|false)\)',fa)]==p['CE']
    assert [r[0] for r in p['CE']]==list(range(1,13)) and set(p['CJ'])==set(range(1,13))
    literal=re.search(r'(?m)^noncomputable def REG : ℕ × ℕ × List \(List ℕ\) := (.*)$',text)[1]
    A,B,chains=ast.literal_eval(literal);assert len(chains)==16
    cells=[]
    for k,chain in enumerate(chains):
        lo=(A>>(20*k))&1048575;hi=(B>>(20*k))&1048575
        if not chain:assert hi<lo;continue
        previous=lo
        for ordinal,end in enumerate(chain):
            assert previous<=end and end+1<=1048576
            cells.append({'chain':k,'ordinal':ordinal,'L':previous,'U':end});previous=end
        assert previous==hi
    p['REG']={'A':A,'B':B,'chains':chains,'cells':cells};return p

def evaluate(p,L,U):
    assert any(c['L']==L and c['U']==U for c in p['REG']['cells'])
    z,sc=p['DZ'],p['SC'];er=p['ERRD'];E20=p['E20'];E9=p['E9']
    zero=lambda:I.naturals(0,0,z)
    c=lambda name:I.naturals(*p[name],z)
    k=div(2*(L+U)+sc,2*sc);side=k*sc<=2*L
    XL=div(L*z,sc);XU=up(U*z,sc);AD=k*p['DZ2']
    RLO=sub(XL,AD) if side else sub(AD,XU);RHI=sub(XU,AD) if side else sub(AD,XL)
    TL=div(p['PLN']*RLO,E20);TU=up(p['PUN']*RHI,E20)
    def cosP(t):return 3628800*z**10+151200*t**4*z**6+90*t**8*z**2
    def cosN(t):return 1814400*t*t*z**8+5040*t**6*z**4+t**10
    def sinP(t):return 39916800*t*z**10+332640*t**5*z**6+110*t**9*z**2
    def sinN(t):return 6652800*t**3*z**8+7920*t**7*z**4+t**11
    CI=I(Z(div(sub(cosP(TU),cosN(TU)),3628800*z**9),er),Z(up(sub(cosP(TL),cosN(TL)),3628800*z**9)+er),z)
    SI=I(Z(div(sub(sinP(TL),sinN(TL)),39916800*z**10),er),Z(up(sub(sinP(TU),sinN(TU)),39916800*z**10)+er),z)
    km=k%4
    if km==0:CX=CI;SX=SI if side else SI.neg()
    elif km==1:CX=SI.neg() if side else SI;SX=CI
    elif km==2:CX=CI.neg();SX=SI.neg() if side else SI
    else:CX=SI if side else SI.neg();SX=CI.neg()
    BL=div(p['PLN']*XL,E20);BU=up(p['PUN']*XU,E20)
    BI=I.naturals(BL,BU,z);PG=I.naturals(div(p['GAM0']*BL,z),up(p['GAM1']*BU,z),z)
    NI=CX.minus(PG.coefficient(SX))
    E0=sub(div(2*BL*BL,z),z);E1=sub(up(2*BU*BU,z),z)
    E2L=div(E0*E0,z);E2U=up(E1*E1,z);E3L=div(E2L*E0,z);E3U=up(E2U*E1,z)
    ok=L<=U and TU<=z and (k*sc<=2*L if side else 2*U<=k*sc) and E0>0
    assert ok and E2L>0 and E3L>0
    def mnum(n,X,J2):
        if n==0:return X*z**2
        if n==1:return (X*X+J2)*z**3
        return 2*X*(X*X+3*J2)*z**4
    def hden(n,Y):return 2*Y if n==0 else 2*Y*Y if n==1 else Y**3
    def mneg(n,ab):return True if n==1 else not ab
    def far(n):
        pl=ph=nl=nh=0
        for j,e,sg in p['CE']:
            J=j*z;J2=J*J
            if 2*j==k:
                a=div(z**(n+2),hden(n,XU+J));b=up(z**(n+2),hden(n,XL+J));negative=sg^(n==1)
            elif 2*j<k:
                a=div(mnum(n,XU,J2),sub(XU*XU,J2)**(n+1));b=up(mnum(n,XL,J2),sub(XL*XL,J2)**(n+1));negative=sg^mneg(n,True)
            else:
                a=div(mnum(n,XL,J2),sub(J2,XL*XL)**(n+1));b=up(mnum(n,XU,J2),sub(J2,XU*XU)**(n+1));negative=sg^mneg(n,False)
            assert 0<=a<=b
            if negative:nl+=e*a;nh+=e*b
            else:pl+=e*a;ph+=e*b
        return I(Z(pl,nh),Z(ph,nl),z).divide(E9)
    FA0,FA1,FA2=far(0),far(1),far(2)
    B0,B1,B2=zero(),zero(),zero()
    if k%2==0 and 2<=k<=24:
        def scP(t):return 39916800*z**10+332640*t**4*z**6+110*t**8*z**2
        def scN(t):return 6652800*t*t*z**8+7920*t**6*z**4+t**10
        def s1P(t):return 133056*t**3*z**6+88*t**7*z**2
        def s1N(t):return 1330560*t*z**8+4752*t**5*z**4+t**9
        def s2P(t):return 3991680*t*t*z**8+6160*t**6*z**4+t**10
        def s2N(t):return 13305600*z**10+237600*t**4*z**6+90*t**8*z**2
        def series(P,N,den,error):return I(Z(P(TL),N(TU)).floor(den).minus(Z(error)),Z(P(TU),N(TL)).ceil(den).plus(Z(error)),z)
        S0=series(scP,scN,39916800*z**9,er);G1=series(s1P,s1N,3991680*z**8,2*er);G2=series(s2P,s2N,39916800*z**9,5*er)
        mag,ng=p['CJ'][k//2]
        B0=S0.signed_natural(ng,mag).divide(2*E9)
        B1=c('PIC').coefficient(G1 if side else G1.neg()).signed_natural(ng,mag).divide(2*E9)
        B2=c('PI2C').coefficient(G2).signed_natural(ng,mag).divide(2*E9)
    EI=I.naturals(E0,E1,z);SF0=SX.times(FA0)
    K0=NI.neg().positive_divide(E0,E1).plus(c('SIGC').coefficient(SF0).plus(c('RHOC').coefficient(B0)))
    MI=EI.coefficient(c('G1C').coefficient(SX).plus(PG.coefficient(CX))).plus(BI.natural(4).coefficient(NI))
    K1=c('PIC').coefficient(MI.positive_divide(E2L,E2U)).plus(c('RHOC').coefficient(CX.times(FA0)).plus(c('SIGC').coefficient(SX.times(FA1))).plus(c('RHOC').coefficient(B1)))
    N2=PG.coefficient(SX).minus(c('G2C').coefficient(CX))
    PP=I.naturals(E2L,E2U,z).coefficient(N2).minus(EI.coefficient(NI).natural(4)).plus(BI.coefficient(MI).natural(8))
    K2=c('PI2C').coefficient(PP.positive_divide(E3L,E3U)).neg().plus(c('RHOC').coefficient(CX.times(FA1)).natural(2).minus(c('TAUC').coefficient(SF0)).plus(c('SIGC').coefficient(SX.times(FA2)).plus(c('RHOC').coefficient(B2))))
    abs1=Z().maximum(K1.l.maximum(K1.h.neg()))
    w=abs1.times(abs1).plus(K0.times(K2).l.natural(z));assert w.ge0()
    return {'L':L,'U':U,'source_CellA_ok':ok,'E2L':E2L,'E3L':E3L,'k':k,'side':side,
        'FA0':FA0.data(),'FA1':FA1.data(),'FA2':FA2.data(),'K0':K0.data(),'K1':K1.data(),'K2':K2.data(),
        'W2L_signed_integer':str(w.v),'m_quantitative':str(Fraction(2*w.v,z*z))}
