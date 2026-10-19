"""W9A2 compact integer and direct printed-AST models.

Adapted from the original baseline integer model by changing only the
configure floor assertion. All tables are supplied by the W9A2 parser.
The new mcheckP expression is independently parsed and evaluated per leaf.
"""
import re, functools
D=1<<40
BB=1<<42
TB=2*BB
MASK32=(1<<32)-1
SLOPE=335544320000000000
DSTEP=int('27723537362511871605908476295798662247233181642325596381965450035666703580892695812701556801522819903482709807068884625171714348091451162793954575790575100589725652890107126812452448984028529561041497038633556695377889700159758912')
def configure(model):
    global BS,TS,PR,BND,CN,SIG,TOP,BK,WL,PT,ALL,LOOK,BAD,cert
    BS,TS,PR,BND,CN,SIG,TOP,BK,WL=[model[k] for k in ['BS','TS','PR','BND','CN','SIG','TOP','BK','WL']]
    PT={p:v&((1<<96)-1) for p,v in model['PTraw'].items()}
    ALL=[(i,i+1) for i in range(8)]+PR
    LOOK={edge:i for i,edge in enumerate(ALL)}
    BAD=model['BAD'];cert=model['cert']
    assert str(DSTEP) in model['text']
    assert CN==893029029923108825
    entry.cache_clear();lb.cache_clear();direct_mcheck_tree.cache_clear()

def nat(n): return max(0,n)
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

