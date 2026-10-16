"""Cell-relative codec and exact iterative thinning, independent of live search."""
from pathlib import Path
import argparse,hashlib,json,time,collections
import compact_thin as thin
import tree_flow as tree
ALPHABET=''.join(chr(c) for c in range(33,127) if c not in(34,92))
assert len(ALPHABET)==92

def text_encode(n):
 if n==0:return ALPHABET[0]
 out=[]
 while n:n,r=divmod(n,92);out.append(ALPHABET[r])
 return ''.join(reversed(out))

def pack_relative(fs,lo,hi):
 mask=sum((k!=0)<<t for t,(k,m,p,r) in enumerate(fs));word=mask;offset=39
 def put(x,b):
  nonlocal word,offset
  assert 0<=x<2**b,(x,b)
  word|=x<<offset;offset+=b
 def point(t,p):
  i,j,_=thin.g.TERMS[t];z=thin.g.LOOK[i,j];base=(lo[z]+31)//32;n=hi[z]//32-base
  assert p%32==0 and 0<=p//32-base<=n,(t,p,base,n)
  put(p//32-base,max(0,n).bit_length())
 for t,(k,m,p,r) in enumerate(fs):
  if k==0:continue
  if k==1:put(0,1);point(t,p)
  else:
   put(1,1);put(k-2,1);put(m,10);point(t,p)
   if k==3:
    delta=r-p
    if delta in(-32,32,-256):put((-32,32,-256).index(delta),2)
    else:put(3,2);point(t,r)
 return word,offset

def unpack_relative(word,lo,hi):
 mask=word%(1<<39);word>>=39
 def get(b):
  nonlocal word
  x=word%(1<<b);word>>=b;return x
 def point(t):
  i,j,_=thin.g.TERMS[t];z=thin.g.LOOK[i,j];base=(lo[z]+31)//32;n=max(0,hi[z]//32-base)
  return(base+get(n.bit_length()))*32
 fs=[]
 for t in range(39):
  if not mask>>t&1:fs.append([0,0,0,0]);continue
  if get(1)==0:fs.append([1,0,point(t),0]);continue
  k=2+get(1);m=get(10);p=point(t);r=0
  if k==3:
   tag=get(2);r=p+(-32,32,-256)[tag] if tag<3 else point(t)
  fs.append([k,m,p,r])
 return fs

def prepare(rec,rounds=3):
 rec={**rec,'multiplier':{**rec['multiplier']}}
 original_bits=thin.fs_bits(rec['FS']);lo=rec['certificate']['lower_bounds'];hi=rec['certificate']['upper_bounds']
 rounddata=[]
 for k in range(rounds):
  th=thin.leaf_thin(rec);fs=th['FS'];d=tree.recompute(fs,lo,hi)
  rounddata.append({'fs_bits':th['fs_bits'],'floor':d['after_numerator'],'removed':len(th['removed_terms']),'single':len(th['single_tangent_terms'])})
  same=fs==rec['FS'];rec['FS']=fs;rec['mcheck_numerator']=d['after_numerator'];rec['multiplier']['steps']=d['steps']
  if same:break
 word,bits=pack_relative(fs,lo,hi);assert unpack_relative(word,lo,hi)==fs
 payload=text_encode(word*10**8+d['tree_code']);decoded=0
 for ch in payload:decoded=decoded*92+ALPHABET.index(ch)
 assert decoded//10**8==word and decoded%10**8==d['tree_code']
 return {'FS':fs,'support_hex':hex(word),'support_bits':bits,'original_bits':original_bits,
  'tree_code':d['tree_code'],'text':payload,'text_source_bytes':len(payload.encode()),'after_numerator':d['after_numerator'],'rounds':rounddata}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=Path(__file__).with_name('parallel-master.json'))
 ap.add_argument('--output',type=Path,default=Path(__file__).with_name('relative-100.json'));ap.add_argument('--limit',type=int,default=100)
 ap.add_argument('--rounds',type=int,default=3);args=ap.parse_args();raw=args.input.read_bytes();doc=json.loads(raw);started=time.monotonic();out=[]
 for a in [x for x in doc['accepted'] if 'FS'in x['result']][:args.limit or None]:
  out.append({'path':a['path'],**prepare(a['result'],args.rounds)})
 stats={'input':str(args.input),'input_sha256':hashlib.sha256(raw).hexdigest(),'processed':len(out),'seconds':time.monotonic()-started,
  'original_FS_bits':sum(a['original_bits'] for a in out),'relative_FS_bits':sum(a['support_bits'] for a in out),
  'base92_source_bytes':sum(a['text_source_bytes'] for a in out),'all_passed_exact_checker':True,'rounds':args.rounds,
  'scope':'Finite leaf compression and exact integer replay only, not coverage or a new kappa proof.'}
 args.output.write_text(json.dumps({'stats':stats,'leaves':out},ensure_ascii=False,separators=(',',':'))+'\n',encoding='utf8')
 print(json.dumps(stats))
if __name__=='__main__':main()
