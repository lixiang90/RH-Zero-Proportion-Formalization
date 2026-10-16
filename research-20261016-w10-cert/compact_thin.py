"""Lossless ragged encoding and independent thinning of W10 mcheckGX leaves.

Only exact integers choose an accepted change. This is not a coverage proof.
The live search generator and frozen Lean modules are never modified.
"""
from pathlib import Path
import argparse,collections,hashlib,importlib.util,json,sys,time
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('w10_discovery',Path(__file__).with_name('generate.py'))
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
f=g.f;Q=9;SC=32768;THRESH=335544320000000000*86600000
DEN=3355443200000000000000000000

def canon(t):
 k,m,p,r=t
 if k==2:
  if m==0:return [0,0,0,0]
  if m==1024:return [1,0,p,0]
 if k==3:
  if m==0:return [1,0,p,0]
  if m==1024:return [1,0,r,0]
 return [k,m,p,r]

def point_bits(p):
 assert 0<=p<2**19,p
 return (15 if p%32==0 else 20)

def fs_bits(fs):
 return sum(2+(0 if k==0 else point_bits(p) if k==1 else 10+point_bits(p) if k==2 else 10+point_bits(p)+point_bits(r)) for k,m,p,r in map(canon,fs))

def pack_fs(fs):
 out=shift=0
 def put(x,b):
  nonlocal out,shift
  assert 0<=x<1<<b,(x,b)
  out|=x<<shift;shift+=b
 def point(p):
  if p%32==0:put(0,1);put(p//32,14)
  else:put(1,1);put(p,19)
 for k,m,p,r in map(canon,fs):
  put(k,2)
  if k==1:point(p)
  elif k==2:put(m,10);point(p)
  elif k==3:put(m,10);point(p);point(r)
 return out,shift

def unpack_fs(w,n=39):
 def get(b):
  nonlocal w
  x=w%2**b;w//=2**b;return x
 def point():
  flag=get(1);return get(19) if flag else 32*get(14)
 fs=[]
 for i in range(n):
  k=get(2);m=p=r=0
  if k==1:p=point()
  elif k==2:m=get(10);p=point()
  elif k==3:m=get(10);p=point();r=point()
  fs.append([k,m,p,r])
 return fs

def dual_state(lo,hi,steps):
 pp=[0]*Q;ss=[0]*Q;cp=cm=0
 for i,j,upper,y in steps:
  y=int(y);base=sum(lo[i:j]);z=g.LOOK[i,j]
  if upper:
   for r in range(i,j):ss[r]+=y
   cp+=y*max(hi[z]-base,0);cm+=y*max(base-hi[z],0)
  else:
   for r in range(i,j):pp[r]+=y
   cp+=y*max(base-lo[z],0);cm+=y*max(lo[z]-base,0)
 return pp,ss,cp,cm

def term_contribution(t,fs,lo,hi):
 i,j,a=g.TERMS[t];kind,m,p,r=fs;z=g.LOOK[i,j]
 l=lo[z];u=max(l+1,hi[z]);base=sum(lo[i:j])
 l1,l2=f.weights(kind,m);cc=1024-l1-l2
 vp=f.PT.get(p,0);vr=f.PT.get(r,0)
 sp=(vp>>32)&f.MASK32;sr=(vr>>32)&f.MASK32;dp=vp>>64;dr=vr>>64
 mv=a*(cc*f.lb(l,u)+l1*(vp&f.MASK32)+l2*(vr&f.MASK32))
 cn=a*(l1*max(2000000000-dp,0)*max(p-base,0)+l2*max(2000000000-dr,0)*max(r-base,0))
 cpa=a*(l1*max(dp-2000000000,0)*max(p-base,0)+l2*max(dr-2000000000,0)*max(r-base,0))
 sl=a*(l1*sp+l2*sr);ma=a*(l1+l2)
 return [SC*mv+10*(cpa-cn)]+[sl if i<=q<j else 0 for q in range(Q)]+[ma if i<=q<j else 0 for q in range(Q)]

def leaf_thin(rec):
 lo=rec['certificate']['lower_bounds'];hi=rec['certificate']['upper_bounds']
 fs=[canon(t) for t in rec['FS']]
 steps=rec['multiplier']['steps'];pp,ss,cp,cm=dual_state(lo,hi,steps)
 initial=10240000000000*sum(b*l for b,l in zip(g.BS,lo[:Q]))+10*(cm-cp)
 contrib=[term_contribution(t,x,lo,hi) for t,x in enumerate(fs)]
 total=[sum(c[z] for c in contrib) for z in range(19)]
 def value(v):
  pen=sum((u-l)*max(2000000000*v[10+r]+pp[r]-(1024000000000*b+v[1+r]+ss[r]),0)
    for r,(u,l,b) in enumerate(zip(hi[:Q],lo[:Q],g.BS)))
  return initial+v[0]-10*pen
 before=value(total)
 assert before==int(rec['mcheck_numerator']),(before,rec['mcheck_numerator'])
 assert before>=THRESH
 zero=[term_contribution(t,[0,0,0,0],lo,hi) for t in range(39)]
 # Lowest exact cost first; sort by the same direct checker being certified.
 order=sorted((t for t,x in enumerate(fs) if x[0]),key=lambda t:before-value([a-b+c for a,b,c in zip(total,contrib[t],zero[t])]))
 removed=[];simplified=[]
 for t in order:
  cand=[a-b+c for a,b,c in zip(total,contrib[t],zero[t])]
  if value(cand)>=THRESH:
   total=cand;contrib[t]=zero[t];fs[t]=[0,0,0,0];removed.append(t)
 # Keep moves fixed and try a single tangent in place of a two-tangent mixture.
 for t,(k,m,p,r) in enumerate(fs):
  if k!=3:continue
  options=[]
  for pt in (p,r):
   c=term_contribution(t,[1,0,pt,0],lo,hi);v=[a-b+d for a,b,d in zip(total,contrib[t],c)]
   options.append((value(v),pt,c,v))
  val,pt,c,v=max(options,key=lambda x:x[0])
  if val>=THRESH:
   fs[t]=[1,0,pt,0];contrib[t]=c;total=v;simplified.append(t)
 after=value(total);word,bits=pack_fs(fs)
 assert unpack_fs(word)==fs and after>=THRESH
 return {'FS':fs,'fs_word_hex':hex(word),'fs_bits':bits,'before_bits':fs_bits(rec['FS']),
  'before_numerator':str(before),'after_numerator':str(after),'removed_terms':removed,
  'single_tangent_terms':simplified,'moves_unchanged':True}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=Path(__file__).with_name('parallel-master.json'))
 ap.add_argument('--output',type=Path,default=Path(__file__).with_name('thin-100.json'));ap.add_argument('--limit',type=int,default=100)
 args=ap.parse_args();raw=args.input.read_bytes();p=json.loads(raw);accepted=[x for x in p['accepted'] if 'FS' in x['result']]
 allfs=[canon(t) for x in accepted for t in x['result']['FS']];points=[p for k,m,p,r in allfs if k]+[r for k,m,p,r in allfs if k==3]
 started=time.monotonic();out=[]
 for x in accepted[:args.limit]:out.append({'path':x['path'],**leaf_thin(x['result'])})
 stats={'input':str(args.input),'input_sha256':hashlib.sha256(raw).hexdigest(),'accepted_with_FS':len(accepted),
  'kind_counts':dict(collections.Counter(t[0] for t in allfs)),'point_count':len(points),'point_multiple32':sum(p%32==0 for p in points),
  'point_max':max(points,default=0),'processed':len(out),'seconds':time.monotonic()-started,
  'before_bits':sum(x['before_bits'] for x in out),'after_bits':sum(x['fs_bits'] for x in out),
  'removed_term_count':sum(len(x['removed_terms']) for x in out),'single_tangent_count':sum(len(x['single_tangent_terms']) for x in out),
  'all_passed_exact_checker':True,'scope':'Exact leaf arithmetic and encoding only; no full coverage claim.'}
 args.output.write_text(json.dumps({'stats':stats,'leaves':out},ensure_ascii=False,indent=2)+'\n',encoding='utf8')
 print(json.dumps(stats,ensure_ascii=False))
if __name__=='__main__':main()
