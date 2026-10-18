"""Original new-source COV true-guard integer replay only (Stage A supplement).
Generic exact IV/SZ arithmetic is adapted from finite_margin_20261015.py;
all Fourier/normalization parameters are extracted from the fixed NEW source.
No new intervals, kernel anchors, thresholds, solver, leafscan or Lean run.
"""
from pathlib import Path
from hashlib import sha256
import ast,json,re,os,time,traceback
import packing_parser_v3 as parser
HERE=Path(__file__).resolve().parent
SOURCE=parser.SOURCE
PARAMS={};COEFF=[];CJ={};SIGC=();RHOC=();DZ=0

def nat(n):return max(0,n)

def ceildiv(a,b):return -(-a//b)
class IV:
 def __init__(self,l,h):self.l=l;self.h=h
 def __neg__(self):return IV(-self.h,-self.l)
 def __add__(self,o):return IV(self.l+o.l,self.h+o.h)
 def __sub__(self,o):return IV(self.l-o.h,self.h-o.l)
 def mul(self,o):
  vals=[a*b for a in [self.l,self.h] for b in [o.l,o.h]]
  return IV(min(vals)//DZ,ceildiv(max(vals),DZ))
 def mulc(self,o):
  return IV((self.l*o.l if o.l>=0 else self.h*o.l)//DZ,
     ceildiv(self.h*o.h if o.h>=0 else self.l*o.h,DZ))
 def muln(self,n):return IV(n*self.l,n*self.h)
 def divn(self,d):return IV(self.l//d,ceildiv(self.h,d))
 def divp(self,e0,e1):return IV(self.l*DZ//(e1 if self.l>=0 else e0),ceildiv(self.h*DZ,e0 if self.h>=0 else e1))
def cell_wz(L,U):
 SC,PLN,PUN,E20,ERRD,E9,SW,GAM0,GAM1=(PARAMS[n] for n in ['SC','PLN','PUN','E20','ERRD','E9','SW','GAM0','GAM1'])
 k=(2*(L+U)+SC)//(2*SC);side=k*SC<=2*L
 xl=L*DZ//SC;xu=ceildiv(U*DZ,SC);ad=k*DZ//2
 rl=nat(xl-ad) if side else nat(ad-xu);ru=nat(xu-ad) if side else nat(ad-xl)
 tl=PLN*rl//E20;tu=ceildiv(PUN*ru,E20)
 cp=lambda t:3628800*DZ**10+151200*t**4*DZ**6+90*t**8*DZ**2
 cn=lambda t:1814400*t**2*DZ**8+5040*t**6*DZ**4+t**10
 sp=lambda t:39916800*t*DZ**10+332640*t**5*DZ**6+110*t**9*DZ**2
 sn=lambda t:6652800*t**3*DZ**8+7920*t**7*DZ**4+t**11
 CI=IV(nat(cp(tu)-cn(tu))//(3628800*DZ**9)-ERRD,ceildiv(nat(cp(tl)-cn(tl)),3628800*DZ**9)+ERRD)
 SI=IV(nat(sp(tl)-sn(tl))//(39916800*DZ**10)-ERRD,ceildiv(nat(sp(tu)-sn(tu)),39916800*DZ**10)+ERRD)
 if k%4==0:CX=CI;SX=SI if side else -SI
 elif k%4==1:CX=-SI if side else SI;SX=CI
 elif k%4==2:CX=-CI;SX=-SI if side else SI
 else:CX=SI if side else -SI;SX=-CI
 bl=PLN*xl//E20;bu=ceildiv(PUN*xu,E20)
 PG=IV(GAM0*bl//DZ,ceildiv(GAM1*bu,DZ))
 NI=CX-PG.mulc(SX);e0=nat(2*bl*bl//DZ-DZ);e1=nat(ceildiv(2*bu*bu,DZ)-DZ)
 assert L<=U and tu<=DZ and (k*SC<=2*L if side else 2*U<=k*SC) and e0>0
 coeff=COEFF
 total=IV(0,0)
 for j,e,sg in coeff:
  J=j*DZ
  if 2*j==k:l=DZ**2//(2*(xu+J));h=ceildiv(DZ**2,2*(xl+J));ng=sg
  elif 2*j<k:l=xu*DZ**2//nat(xu*xu-J*J);h=ceildiv(xl*DZ**2,nat(xl*xl-J*J));ng=sg
  else:l=xl*DZ**2//nat(J*J-xl*xl);h=ceildiv(xu*DZ**2,nat(J*J-xu*xu));ng=not sg
  term=IV(e*l,e*h);total=total+(-term if ng else term)
 FA=total.divn(E9);B0=IV(0,0)
 if k%2==0 and 2<=k<=24:
  p0=lambda t:39916800*DZ**10+332640*t**4*DZ**6+110*t**8*DZ**2
  n0=lambda t:6652800*t**2*DZ**8+7920*t**6*DZ**4+t**10
  S0=IV((p0(tl)-n0(tu))//(39916800*DZ**9)-ERRD,ceildiv(p0(tu)-n0(tl),39916800*DZ**9)+ERRD)
  magnitude,negative=CJ[k//2];cs=-magnitude if negative else magnitude
  B0=S0.muln(abs(cs)).divn(2*E9)
  if cs<0:B0=-B0
 K0=(-NI).divp(e0,e1)+(IV(*SIGC).mulc(SX.mul(FA))+IV(*RHOC).mulc(B0))
 kan=max(0,K0.l,-K0.h)
 return kan*kan*SW//(DZ*DZ)

