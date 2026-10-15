"""Replay the accepted nine-point finite inequalities with exact integers.

This is an independent discovery audit, not a Lean proof or a website
acceptance receipt. It replays every serialized walk, checks every numerical
leaf twice (a compact translation and the printed mcheckP syntax tree), and
recomputes the root-cover arithmetic. Existing analytic/tangent-table
soundness is supplied by the separately kernel-checked Lean source.

Run:
  python scripts/finite_margin_20261015.py
  python scripts/finite_margin_20261015.py --output -
"""
from pathlib import Path
import argparse
import hashlib
import re, ast, functools, json, time, sys
ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--source", type=Path,
    default=ROOT / "formal/upstream/ajp88-reweighted-nine-point.lean")
parser.add_argument("--output",
    default=str(ROOT / "verification/gram-defect-20261015/finite-margin.json"))
args = parser.parse_args() if __name__ == "__main__" else parser.parse_args([])
NEW_CN = 859538525913875481
OBJECTIVE_SCALE = 10**20
sys.set_int_max_str_digits(0)
SRC = args.source
text=SRC.read_text(encoding='utf8')
start=text.index('namespace AMW.Cert.PC9QB6M\n')
cert=text[start:]
D=1<<40; BB=1<<42; TB=2*BB; MASK32=(1<<32)-1
SLOPE=335544320000000000

def nat(n): return max(0,n)
def lst(name): return ast.literal_eval(re.search(r'def '+name+r'\s*:[^\n]*:= (\[[^\n]*\])',cert).group(1))
BS=lst('BS'); TS=lst('TS'); PR=lst('PR'); BND=lst('BND')
CN=int(re.search(r'def cN[^\n]*:= (\d+)',cert).group(1)); SIG=int(re.search(r'def SIG[^\n]*:= (\d+)',cert).group(1))
TOP=int(re.search(r'def TOP[^\n]*:= (0x[\da-f]+)',cert).group(1),16)
BK={int(j):int(x,16) for j,x in re.findall(r'def BK_(\d+)[^\n]*:= (0x[\da-f]+)',cert)}
WL={}
for j,k,x in re.findall(r'def WL(\d+)_(\d+)[^\n]*:= (0x[\da-f]+)',cert): WL.setdefault(int(j),{})[int(k)]=int(x,16)
PT={}
for j,l in re.findall(r'\.lf (\d+) (\[[^\]]*\])',cert):
 for k,v in ast.literal_eval(l): PT[1024*int(j)+k]=v&((1<<96)-1)
rootrecords={int(r):(tuple(map(int,idx.split())),int(e)) for r,idx,e in re.findall(r'theorem rc(\d+) : Covered \(RC ([\d ]+)\) := rcOf WD\d+ (\d+)',cert)}
covtxt=re.search(r'def COV[^\n]*:= (\[[\s\S]*?)\ndef SMAX',cert).group(1)
COV=ast.literal_eval(covtxt.replace('true','True').replace('false','False'))
BAD=[[(a,b) for a,b,c in row if not c] for row in COV]
ALL=[(i,i+1) for i in range(8)]+PR
LOOK={t:i for i,t in enumerate(ALL)}
DSTEP=int('27723537362511871605908476295798662247233181642325596381965450035666703580892695812701556801522819903482709807068884625171714348091451162793954575790575100589725652890107126812452448984028529561041497038633556695377889700159758912')
@functools.lru_cache(None)
def entry(l,i):
 if l>=20: return 0
 if l>=11: return (TOP>>(32*((1<<nat(19-l))+i)))&MASK32
 j=i>>nat(10-l); x=BK.get(j,0); kk=l+nat((x&31)-l); d=nat(10-kk)
 a=nat((1<<d)-1)+nat((i>>nat(kk-l))-(j<<d))
 return (x>>(5+32*a))&MASK32
@functools.lru_cache(None)
def lb(lo,hi):
 if hi<=lo or hi>=524289: return 0
 k=((hi-lo)>>5).bit_length(); E=((hi-1)>>k)+1; g=lo>>k; ans=None
 for _ in range(14):
  d=nat(E-g); ix=17*(g&15)+min(d,16); t=(DSTEP>>(3*ix))&7; h=g>>t
  v=entry(k+t,h); ans=v if ans is None else min(ans,v)
  g=(h+1)<<t
  if E<=g: return ans
 return 0

def root(idx):
 L=[BAD[r][idx[r]][0] for r in range(8)]; U=[BAD[r][idx[r]][1] for r in range(8)]
 return L+[sum(L[i:j]) for i,j in PR],U+[sum(U[i:j]) for i,j in PR]

def leg(s,a,b):
 if a==b:return 0
 if a<b:return s[1][LOOK[a,b]]
 return -s[0][LOOK[b,a]]

def split(s,i,j,q,upper):
 lo,hi=s; aa,bb,w=(i,j,q) if upper else (j,i,-q)
 col=[nat(BB+leg(s,x,aa)) for x in range(9)]
 row=[nat(BB+w+leg(s,bb,x)) for x in range(9)]
 return ([max(l,nat(TB-col[b]-row[a])) for l,(a,b) in zip(lo,ALL)],
         [min(u,nat(col[a]+row[b]-TB)) for u,(a,b) in zip(hi,ALL)])

def bcut(lo,hi):
 ans=(lo+hi)>>1; best=None
 for z in BND:
  if lo+64<=z and z+64<=hi and (best is None or abs(2*z-lo-hi)<best): ans=z;best=abs(2*z-lo-hi)
 return ans

def gpt(L,U,jj):
 if jj==33: return L
 gs=5 if ((jj>>6)&1)==1 else 8
 ga=((L+(1<<gs)-1)>>gs)<<gs; gb=(U>>gs)<<gs
 x=((L+(nat(U-L)*(jj&63)>>5))>>gs)<<gs
 return ga if x<=ga else gb if gb<=x else x

def dec(w,o,L,U):
 a=(w>>o)&3
 lam=(w>>(o+9))&1023 if a==2 else (w>>(o+16))&1023 if a==3 else 0
 p=gpt(L,U,(w>>(o+2))&127) if a else 0
 r=gpt(L,U,(w>>(o+9))&127) if a==3 else 0
 return (a,lam,p,r),o+({0:2,1:9,2:19,3:26}[a])

def term_bounds(s,i,j):
 lo,hi=s;ix=LOOK[i,j]
 return max(lo[ix],sum(lo[i:j])),min(hi[ix],sum(hi[i:j]))

def ydec(w,o,s):
 lo,hi=s; Ls=lo[:8]; P=[0]*8; S=[0]*8; cp=cm=0
 for _ in range(42):
  if (w>>o)&1:
   c=(w>>(o+1))&31; o1=o+6
   if c<28:
    Y=SIG*((w>>(o1+1))&16383); sd=(w>>o1)&1; i,j=PR[c]; sl=sum(Ls[i:j])
    if sd:
     for r in range(i,j):S[r]+=Y
     cp+=Y*nat(hi[8+c]-sl); cm+=Y*nat(sl-hi[8+c])
    else:
     for r in range(i,j):P[r]+=Y
     cp+=Y*nat(sl-lo[8+c]); cm+=Y*nat(lo[8+c]-sl)
   o=o1+15
   if c>=28:break
  else:
   o+=1; break
 return P,S,cp,cm,o

def weights(k,m):return (1024,0) if k==1 else (m,0) if k==2 else (1024-m,m) if k==3 else (0,0)

def calc(s,w):
 lo,hi=s; L=lo[:8]; U=hi[:8]; fs=[];o=0
 for i,j,a,k in TS:
  l,u=term_bounds(s,i,j); f,o=dec(w,o,l,u); fs.append(f)
 P,S,cp,cm,o=ydec(w,o,s)
 lin=sum(b*l for b,l in zip(BS,L)); mv=cn=cpadd=0; slopes=[0]*8; mass=[0]*8
 for (i,j,a,_),(k,m,p,r) in zip(TS,fs):
  l,u=term_bounds(s,i,j);u=max(l+1,u);l0=sum(L[i:j]); l1,l2=weights(k,m)
  const=0 if k==1 or k==3 else (1024-m) if k==2 else 1024
  vp=PT.get(p,0);vr=PT.get(r,0)
  mv+=a*(const*lb(l,u)+l1*(vp&MASK32)+l2*(vr&MASK32))
  sp=(vp>>32)&MASK32; sr=(vr>>32)&MASK32; dp=vp>>64; dr=vr>>64
  cn+=a*(l1*nat(2000000000-dp)*nat(p-l0)+l2*nat(2000000000-dr)*nat(r-l0))
  cpadd+=a*(l1*nat(dp-2000000000)*nat(p-l0)+l2*nat(dr-2000000000)*nat(r-l0))
  sl=a*(l1*sp+l2*sr); ma=a*(l1+l2)
  for rr in range(i,j): slopes[rr]+=sl; mass[rr]+=ma
 penalty=sum(nat(u-l)*nat(2000000000*ma+pp-(1024000000000*b+sl+ss)) for u,l,ma,pp,b,sl,ss in zip(U,L,mass,P,BS,slopes,S))
 total=10240000000000*lin+32768*mv+10*(cpadd+cm)-10*(cn+cp+penalty)
 return total-SLOPE*CN,o

class Walker:
 def __init__(self,n,direct=False):self.n=n;self.direct=direct;self.blocks=WL[n];self.minmargin=None;self.minleaf=None;self.nodes=0;self.leaves=0;self.farkas=0;self.reverse=0;self.tightened=0
 def bits(self,p):return (self.blocks.get(p//32768,0)>>(p%32768))&((1<<480)-1)
 def walk(self,s,pos=1,depth=128):
  self.nodes+=1
  if depth==0:raise RuntimeError(('fuel',pos))
  w=self.bits(pos)
  if w&1:
   ax=(w>>1)&63;md=(w>>7)&1
   if ax>=len(ALL):raise RuntimeError(('ax',ax,pos))
   i,j=ALL[ax];q=bcut(s[0][ax],s[1][ax]) if md else (s[0][ax]+s[1][ax])>>1
   pp=self.walk(split(s,i,j,q,True),pos+8,depth-1)
   return self.walk(split(s,i,j,q,False),pp,depth-1)
  self.leaves+=1
  if s[1][7]<s[0][0]:self.reverse+=1;return pos+1
  if (w>>1)&1:
   P,S,cp,cm,o=ydec(w>>2,0,s); value=cm-cp-sum(nat(pp-ss)*nat(u-l) for ss,pp,u,l in zip(S,P,s[1][:8],s[0][:8]))
   assert value>0,('farkas',self.n,pos,value)
   self.farkas+=1
  else:
   if any(term_bounds(s,i,j)!=(s[0][LOOK[i,j]],s[1][LOOK[i,j]]) for i,j,_,_ in TS):self.tightened+=1
   margin,o=calc(s,w>>2)
   if self.direct:assert direct_mcheck_margin(s,w>>2)==margin,('AST mismatch',self.n,pos,margin)
   assert margin>=0,('margin',self.n,pos,margin,s)
   if self.minmargin is None or margin<self.minmargin:self.minmargin=margin;self.minleaf={'pos':pos,'lo':s[0],'hi':s[1]}
  return pos+2+o
 def run(self):
  idx,expected=rootrecords[self.n];actual=self.walk(root(idx));assert actual==expected,(self.n,actual,expected)
  return {'root':self.n,'end':actual,'nodes':self.nodes,'leaves':self.leaves,'farkas':self.farkas,'reverse':self.reverse,'tightened':self.tightened,'min_margin':self.minmargin,'leaf':self.minleaf}

# Independent direct evaluation of the arithmetic inequality as printed in
# mcheckP, rather than the compact generic formula used by calc.
@functools.lru_cache(None)
def direct_mcheck_tree():
 line=re.search(r'def mcheckP[^\n]*\n[^\n]*\n([^\n]+)',cert).group(1)
 p=line.index('(Nat.ble'); depth=0; end=p
 for end in range(p,len(line)):
  if line[end]=='(':depth+=1
  elif line[end]==')':
   depth-=1
   if depth==0:break
 expr=line[p:end+1]
 tokens=re.findall(r'[()]|[^\s()]+',expr);ix=0
 def parse():
  nonlocal ix
  t=tokens[ix];ix+=1
  if t!='(':return t
  a=[]
  while tokens[ix]!=')':a.append(parse())
  ix+=1;return a
 tree=parse();assert ix==len(tokens)
 return tree

def direct_mcheck_margin(s,w):
 tree=direct_mcheck_tree()
 lo,hi=s; names=['l0','u0','l1','u1','l2','u2','l3','u3','l4','u4','l5','u5','l6','u6','l7','u7']
 for i,j in PR:names += ['A'+str(i)+str(j),'B'+str(i)+str(j)]
 env={'s.'+name:value for name,value in zip(names,[x for pair in zip(lo,hi) for x in pair])}
 env.update({'cN':CN,'true':True,'false':False,'top':TOP,'bk':BK,'f':lambda p:PT.get(p,0)})
 o=0
 for i,j,_,_ in TS:
  l,u=term_bounds(s,i,j);f,o=dec(w,o,l,u)
  for name,value in zip(['k','m','p','r'],f):env[name+str(i)+str(j)]=value
 P,S,cp,cm,o=ydec(w,o,s)
 env.update({'P'+str(i):P[i] for i in range(8)});env.update({'S'+str(i):S[i] for i in range(8)});env.update(Cp=cp,Cm=cm)
 def mck(f,sg,l,k,m,p,r):
  a,b=weights(k,m)
  return sum(lam*nat((f(q)>>64)-2000000000 if sg else 2000000000-(f(q)>>64))*nat(q-l) for lam,q in [(a,p),(b,r)])
 def msl(f,k,m,p,r):
  a,b=weights(k,m);return a*((f(p)>>32)&MASK32)+b*((f(r)>>32)&MASK32)
 def mv(top,bk,f,l,u,k,m,p,r):
  a,b=weights(k,m);c=1024-a-b
  return c*lb(l,u)+a*(f(p)&MASK32)+b*(f(r)&MASK32)
 env.update({'Nat.add':lambda a,b:a+b,'Nat.mul':lambda a,b:a*b,'Nat.sub':lambda a,b:nat(a-b),
   'Nat.ble':lambda a,b:(a,b),'nmax':max,'nmin':min,'uc':lambda l,u:max(l+1,u),
   'tf':lambda f:f,'mcK':mck,'mwT':lambda k,m:sum(weights(k,m)),'mslK':msl,'mvKF':mv})
 def ev(t):
  if isinstance(t,str):return int(t) if t.isdigit() else env[t]
  return ev(t[0])(*map(ev,t[1:]))
 lhs,rhs=ev(tree)
 return rhs-lhs

DZ=10**15
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
 from math import factorial
 SC=32768;PLN=314159265358979323846;PUN=314159265358979323847;E20=10**20;ERRD=2262000
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
 PG=IV(1654998581400000*bl//DZ,ceildiv(1654998603600000*bu,DZ))
 NI=CX-PG.mulc(SX);e0=nat(2*bl*bl//DZ-DZ);e1=nat(ceildiv(2*bu*bu,DZ)-DZ)
 assert L<=U and tu<=DZ and (k*SC<=2*L if side else 2*U<=k*SC) and e0>0
 coeff=[(1,12310798,True),(2,15041681,True),(3,3867664,True),(4,6489926,False),(5,992327,False),(6,5580097,False),(7,6846472,False),(8,3781297,False),(9,5670353,False),(10,3355089,False),(11,450523,False),(12,218483,True)]
 total=IV(0,0)
 for j,e,sg in coeff:
  J=j*DZ
  if 2*j==k:l=DZ**2//(2*(xu+J));h=ceildiv(DZ**2,2*(xl+J));ng=sg
  elif 2*j<k:l=xu*DZ**2//nat(xu*xu-J*J);h=ceildiv(xl*DZ**2,nat(xl*xl-J*J));ng=sg
  else:l=xl*DZ**2//nat(J*J-xl*xl);h=ceildiv(xu*DZ**2,nat(J*J-xu*xu));ng=not sg
  term=IV(e*l,e*h);total=total+(-term if ng else term)
 FA=total.divn(10**9);B0=IV(0,0)
 if k%2==0 and 2<=k<=24:
  p0=lambda t:39916800*DZ**10+332640*t**4*DZ**6+110*t**8*DZ**2
  n0=lambda t:6652800*t**2*DZ**8+7920*t**6*DZ**4+t**10
  S0=IV((p0(tl)-n0(tu))//(39916800*DZ**9)-ERRD,ceildiv(p0(tu)-n0(tl),39916800*DZ**9)+ERRD)
  cs=[12310798,-15041681,3867664,6489926,-992327,5580097,-6846472,3781297,-5670353,3355089,-450523,-218483][k//2-1]
  B0=S0.muln(abs(cs)).divn(2*10**9)
  if cs<0:B0=-B0
 K0=(-NI).divp(e0,e1)+(IV(346469027075676,346469029528983).mulc(SX.mul(FA))+IV(1088464550157349,1088464557864635).mulc(B0))
 kan=max(0,K0.l,-K0.h)
 return kan*kan*10**13//(DZ*DZ)

def cover_thresholds():
 vals=[];ADJ=[0,7,14,20,25,29,32,33];SMAX=[1040384,573440,434176,376832,376832,434176,573440,1040384]
 for r in range(8):
  a=TS[ADJ[r]][2]
  vals += [('large',r,BS[r]*SMAX[r]//32768),('small',r,a//4)]
  for l,u,b in COV[r]:
   if b:
    wz=cell_wz(l,u);vals.append(('cover',r,l,u,wz,a*wz//10**13))
 return vals

def main():
 started = time.time()
 assert __debug__, "Run with Python assertions enabled"
 source_hash = hashlib.sha256(SRC.read_bytes()).hexdigest()
 assert source_hash == "153e1ebfa23b5ef307dc39e36ee712d6f14d840b3b1fa5ff70b82e9dbc8dd244"
 assert CN == 859538456469471854
 assert len(rootrecords) == 48 and len(PT) > 0
 # Root-cover topology and the bound used for its pair constraints.
 smax = [1040384,573440,434176,376832,376832,434176,573440,1040384]
 for r, row in enumerate(COV):
  pos = 16384
  for lo, hi, closed in row:
   assert lo == pos and lo <= hi and hi < 1048576
   pos = hi
  assert pos == smax[r]
 assert 8 * 1048576 <= 1099511627776
 adjacency = [0,7,14,20,25,29,32,33]
 assert all(TS[k][0:2] == (r,r+1) for r,k in enumerate(adjacency))
 records = [Walker(n, direct=True).run() for n in range(48)]
 covers = cover_thresholds()
 bottleneck = min(records, key=lambda row: row["min_margin"])
 margin = bottleneck["min_margin"]
 increment, residual = divmod(margin,SLOPE)
 maximum_leaf_floor = CN + increment
 maximum_root_floor = min(row[-1] for row in covers)
 maximum_floor = min(maximum_leaf_floor,maximum_root_floor)
 assert maximum_floor == NEW_CN
 assert increment == 69444403627
 assert residual == 235234080000000000
 assert SLOPE-residual == 100310240000000000
 assert all(row["min_margin"] >= 0 for row in records)
 assert all(row[-1] >= CN for row in covers)
 assert all(row["min_margin"] - SLOPE*(NEW_CN-CN) >= 0 for row in records)
 assert all(row[-1] >= NEW_CN for row in covers)
 assert source_hash == hashlib.sha256(SRC.read_bytes()).hexdigest()
 counts = {key:sum(row[key] for row in records)
     for key in ("nodes","leaves","reverse","farkas","tightened")}
 numeric_count = counts["leaves"]-counts["reverse"]-counts["farkas"]
 assert counts == {"nodes":22664,"leaves":11356,"reverse":419,"farkas":0,"tightened":0}
 assert numeric_count == 10937 and len(covers) == 108
 receipt = {
  "audit_kind":"exact_integer_discovery_replay_not_Lean_proof",
  "official_website_acceptance":False,
  "source":str(SRC.relative_to(ROOT) if SRC.is_relative_to(ROOT) else SRC),
  "source_sha256":source_hash,
  "audit_script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
  "all_original_walk_end_pointers_match":True,
  "original_threshold_all_checks_pass":True,
  "new_threshold_all_checks_pass":True,
  "direct_printed_mcheckP_AST_matches_every_numeric_leaf":True,
  "numeric_leaf_AST_comparisons":numeric_count,
  "counts":counts,
  "root_count":len(records),
  "root_condition_count":len(covers),
  "source_original_cN":CN,
  "candidate_cN":NEW_CN,
  "objective_denominator":OBJECTIVE_SCALE,
  "candidate_local_floor":str(NEW_CN)+"/"+str(OBJECTIVE_SCALE),
  "threshold_slope":SLOPE,
  "maximal_cN_for_these_fixed_witnesses_and_denominator":maximum_floor,
  "integer_threshold_increment":increment,
  "bottleneck":{"root":bottleneck["root"],"position":bottleneck["leaf"]["pos"],
      "original_margin":margin,
      "candidate_residual_margin":residual,
      "next_integer_failure_deficit":SLOPE-residual,
      "lower_bounds":bottleneck["leaf"]["lo"],"upper_bounds":bottleneck["leaf"]["hi"]},
  "root_condition_minimum":list(min(covers,key=lambda row:row[-1])),
  "root_condition_margin_in_cN_units":maximum_root_floor-NEW_CN,
  "per_root":[{key:value for key,value in row.items() if key!="leaf"} |
      {"minimum_margin_position":row["leaf"]["pos"],
       "candidate_residual_margin":row["min_margin"]-SLOPE*(NEW_CN-CN)}
      for row in records],
  "all_root_conditions":[list(row) for row in covers],
  "source_inputs_unchanged":True,
  "elapsed_seconds":time.time()-started,
  "scope":"Exact finite numerical inequalities and serialized traversal only; "
     "analytic/tangent validity and final zeta counting statements require the "
     "separate ordinary Lean and independent-kernel checks."
 }
 encoded = json.dumps(receipt,indent=2)+"\n"
 if args.output == "-":
  print(encoded,end="")
 else:
  destination=Path(args.output)
  destination.parent.mkdir(parents=True,exist_ok=True)
  destination.write_text(encoded,encoding="utf8",newline="\n")
  print(json.dumps({"passed":True,"output":str(destination),
      "candidate_cN":NEW_CN,"numeric_leaf_AST_comparisons":numeric_count,
      "root_condition_count":len(covers)}))
if __name__ == "__main__":
 main()

