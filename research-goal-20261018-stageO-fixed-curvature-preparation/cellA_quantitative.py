"""Prepared source CellA integer interval transcription, definitions only.

The future gate may evaluate ONLY original REG consecutive endpoint cells.
No decimal transcendental values, fresh anchors, adaptive subdivision or jets.
"""
from fractions import Fraction as F
import ast
import re

def ceildiv(a,b):
    assert b>0;return -(-a//b)
def ndiv(a,b):return a//b if b else 0
def ndivc(a,b):return ceildiv(a,b) if b else 0
def nat(a):return max(0,a)

class IV:
    def __init__(self,lo,hi,z):self.lo=lo;self.hi=hi;self.z=z;assert lo<=hi
    def __neg__(self):return IV(-self.hi,-self.lo,self.z)
    def __add__(self,b):assert self.z==b.z;return IV(self.lo+b.lo,self.hi+b.hi,self.z)
    def __sub__(self,b):return self+-b
    def mul(self,b):
        assert self.z==b.z;v=[x*y for x in (self.lo,self.hi) for y in (b.lo,b.hi)]
        return IV(min(v)//self.z,ceildiv(max(v),self.z),self.z)
    def mulc(self,b):
        assert self.z==b.z and self.lo>=0
        return IV((self.lo*b.lo if b.lo>=0 else self.hi*b.lo)//self.z,
            ceildiv(self.hi*b.hi if b.hi>=0 else self.lo*b.hi,self.z),self.z)
    def muln(self,n):assert n>=0;return IV(self.lo*n,self.hi*n,self.z)
    def divn(self,n):assert n>0;return IV(self.lo//n,ceildiv(self.hi,n),self.z)
    def divp(self,lo,hi):
        assert 0<lo<=hi
        return IV(self.lo*self.z//(hi if self.lo>=0 else lo),
            ceildiv(self.hi*self.z,lo if self.hi>=0 else hi),self.z)
    def scale(self,negative,n):return -self.muln(n) if negative else self.muln(n)
    def data(self):return [self.lo,self.hi]

def parameters(text):
    """Literal-only extraction, called only under the future execution gate."""
    def number(name):
        vals=re.findall(r'(?m)^noncomputable def '+re.escape(name)+r' : ℕ := (\d+)\s*$',text)
        assert vals and len(set(vals))==1,(name,vals);return int(vals[0])
    out={n:number(n) for n in ['DZ','DZ2','SC','PLN','PUN','E20','ERRD','E9','GAM0','GAM1']}
    assert out['SC']==32768 and 2*out['DZ2']==out['DZ']
    for name in ['PIC','PI2C','G1C','G2C','RHOC','SIGC','TAUC']:
        vals=re.findall(r'(?m)^noncomputable def '+name+r' : IV := IV.ofN (\d+) (\d+)\s*$',text)
        assert len(vals)==1;out[name]=list(map(int,vals[0]))
    ce=re.search(r'noncomputable def CE : List[^\n]*:=\s*(\[[\s\S]*?\])',text)[1]
    out['CE']=ast.literal_eval(ce.replace('true','True').replace('false','False'))
    cj=re.search(r'noncomputable def CJ \(j : ℕ\)[\s\S]*?(?=^structure Acc)',text,re.M)[0]
    out['CJ']={int(j):(int(v),sg=='true') for j,v,sg in re.findall(r'\| (\d+) => \((\d+), (true|false)\)',cj)}
    assert [a[0] for a in out['CE']]==list(range(1,13)) and set(out['CJ'])==set(range(1,13))
    fa=re.search(r'noncomputable def FA \(c : CellA\)[\s\S]*?(?=^noncomputable def nearOn)',text,re.M)[0]
    assert [(int(j),int(v),sg=='true') for j,v,sg in re.findall(r'\b(\d+) (\d+) (true|false)\)',fa)]==out['CE']
    reg=re.search(r'(?m)^noncomputable def REG : ℕ × ℕ × List \(List ℕ\) := (.*)$',text)[1]
    A,B,chains=ast.literal_eval(reg);assert len(chains)==16
    catalog=[]
    for k,chain in enumerate(chains):
        lo=(A>>(20*k))&1048575;hi=(B>>(20*k))&1048575
        if not chain:assert hi<lo;continue
        assert chain==sorted(set(chain)) and lo<=chain[0] and chain[-1]==hi
        points=[lo]+chain
        for t,(l,u) in enumerate(zip(points,points[1:])):
            assert l<=u and u+1<=1048576
            catalog.append({'chain':k,'ordinal':t,'L':l,'U':u})
    out['REG']={'packed_A':str(A),'packed_B':str(B),'chains':chains,'cells':catalog}
    return out

def evaluate_original_cell(p,L,U):
    """Exactly one pre-existing ccell(L,U), only after membership is checked."""
    assert any(c['L']==L and c['U']==U for c in p['REG']['cells'])
    z=p['DZ'];sc=p['SC'];err=p['ERRD'];e9=p['E9'];e20=p['E20']
    iv=lambda a,b:IV(a,b,z)
    const=lambda name:iv(*p[name])
    k=(2*(L+U)+sc)//(2*sc);side=k*sc<=2*L
    xl=L*z//sc;xu=ceildiv(U*z,sc);ad=k*p['DZ2']
    rl=nat(xl-ad) if side else nat(ad-xu);ru=nat(xu-ad) if side else nat(ad-xl)
    tl=p['PLN']*rl//e20;tu=ceildiv(p['PUN']*ru,e20)
    cp=lambda t:3628800*z**10+151200*t**4*z**6+90*t**8*z**2
    cn=lambda t:1814400*t**2*z**8+5040*t**6*z**4+t**10
    sp=lambda t:39916800*t*z**10+332640*t**5*z**6+110*t**9*z**2
    sn=lambda t:6652800*t**3*z**8+7920*t**7*z**4+t**11
    ci=iv(nat(cp(tu)-cn(tu))//(3628800*z**9)-err,ceildiv(nat(cp(tl)-cn(tl)),3628800*z**9)+err)
    si=iv(nat(sp(tl)-sn(tl))//(39916800*z**10)-err,ceildiv(nat(sp(tu)-sn(tu)),39916800*z**10)+err)
    if k%4==0:cx=ci;sx=si if side else -si
    elif k%4==1:cx=-si if side else si;sx=ci
    elif k%4==2:cx=-ci;sx=-si if side else si
    else:cx=si if side else -si;sx=-ci
    bl=p['PLN']*xl//e20;bu=ceildiv(p['PUN']*xu,e20)
    bi=iv(bl,bu);pg=iv(p['GAM0']*bl//z,ceildiv(p['GAM1']*bu,z))
    ni=cx-pg.mulc(sx);e0=nat(2*bl*bl//z-z);e1=nat(ceildiv(2*bu*bu,z)-z)
    ok=L<=U and tu<=z and (k*sc<=2*L if side else 2*U<=k*sc) and e0>0
    e2l=e0*e0//z;e2u=ceildiv(e1*e1,z);e3l=e2l*e0//z;e3u=ceildiv(e2u*e1,z)
    assert ok and e2l>0 and e3l>0,'original_REG_CellA_guard_failure'
    def mnum(n,x,j2):
        if n==0:return x*z**2
        if n==1:return (x*x+j2)*z**3
        return 2*x*(x*x+3*j2)*z**4
    def hden(n,y):return 2*y if n==0 else 2*y*y if n==1 else y**3
    def far(n):
        lo=hi=0
        for j,e,sg in p['CE']:
            J=j*z;j2=J*J
            if 2*j==k:
                m0=ndiv(z**(n+2),hden(n,xu+J));m1=ndivc(z**(n+2),hden(n,xl+J))
                negative=bool(sg)^bool(n==1)
            elif 2*j<k:
                m0=ndiv(mnum(n,xu,j2),nat(xu*xu-j2)**(n+1))
                m1=ndivc(mnum(n,xl,j2),nat(xl*xl-j2)**(n+1))
                negative=bool(sg)^bool(n==1)
            else:
                m0=ndiv(mnum(n,xl,j2),nat(j2-xl*xl)**(n+1))
                m1=ndivc(mnum(n,xu,j2),nat(j2-xu*xu)**(n+1));negative=not bool(sg)
            assert 0<=m0<=m1
            if negative:lo-=e*m1;hi-=e*m0
            else:lo+=e*m0;hi+=e*m1
        return iv(lo,hi).divn(e9)
    fa0,fa1,fa2=far(0),far(1),far(2)
    b0=b1=b2=iv(0,0)
    if k%2==0 and 2<=k<=24:
        p0=lambda t:39916800*z**10+332640*t**4*z**6+110*t**8*z**2
        n0=lambda t:6652800*t**2*z**8+7920*t**6*z**4+t**10
        p1=lambda t:133056*t**3*z**6+88*t**7*z**2
        n1=lambda t:1330560*t*z**8+4752*t**5*z**4+t**9
        p2=lambda t:3991680*t**2*z**8+6160*t**6*z**4+t**10
        n2=lambda t:13305600*z**10+237600*t**4*z**6+90*t**8*z**2
        s0=iv((p0(tl)-n0(tu))//(39916800*z**9)-err,ceildiv(p0(tu)-n0(tl),39916800*z**9)+err)
        g1=iv((p1(tl)-n1(tu))//(3991680*z**8)-2*err,ceildiv(p1(tu)-n1(tl),3991680*z**8)+2*err)
        g2=iv((p2(tl)-n2(tu))//(39916800*z**9)-5*err,ceildiv(p2(tu)-n2(tl),39916800*z**9)+5*err)
        mag,neg=p['CJ'][k//2]
        b0=s0.scale(neg,mag).divn(2*e9)
        b1=const('PIC').mulc(g1 if side else -g1).scale(neg,mag).divn(2*e9)
        b2=const('PI2C').mulc(g2).scale(neg,mag).divn(2*e9)
    sf0=sx.mul(fa0);ei=iv(e0,e1)
    K0=(-ni).divp(e0,e1)+const('SIGC').mulc(sf0)+const('RHOC').mulc(b0)
    mi=ei.mulc(const('G1C').mulc(sx)+pg.mulc(cx))+bi.muln(4).mulc(ni)
    K1=const('PIC').mulc(mi.divp(e2l,e2u))+const('RHOC').mulc(cx.mul(fa0))+const('SIGC').mulc(sx.mul(fa1))+const('RHOC').mulc(b1)
    n2=pg.mulc(sx)-const('G2C').mulc(cx)
    pp=iv(e2l,e2u).mulc(n2)-ei.mulc(ni).muln(4)+bi.mulc(mi).muln(8)
    K2=-const('PI2C').mulc(pp.divp(e3l,e3u))+const('RHOC').mulc(cx.mul(fa1)).muln(2)-const('TAUC').mulc(sf0)+const('SIGC').mulc(sx.mul(fa2))+const('RHOC').mulc(b2)
    absK1=max(0,K1.lo,-K1.hi);w2l=absK1**2+K0.mul(K2).lo*z
    assert w2l>=0,'source_hR_convOk_inconsistent_or_transcription_failure'
    return {'L':L,'U':U,'source_CellA_ok':ok,'E2L':e2l,'E3L':e3l,'k':k,'side':side,
        'FA0':fa0.data(),'FA1':fa1.data(),'FA2':fa2.data(),'K0':K0.data(),'K1':K1.data(),'K2':K2.data(),
        'W2L_signed_integer':str(w2l),'m_quantitative':str(F(2*w2l,z*z)),
        'analytic_transfer_required':'same-source CellA quantitative w2 >= 2*W2L.v/DZ^2; not newly Lean-proved here'}
