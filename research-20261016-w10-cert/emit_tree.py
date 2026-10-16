"""Emit the complete prefix tree and exact leaf payloads as ordinary Nat macros.

The generated Lean theorem checks every node and every leaf. This script's
arithmetic or compression is never assumed by the mathematical proof.
"""
from pathlib import Path
import argparse,hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
ABC=''.join(chr(c) for c in range(33,127) if c not in(34,92))
def encode(n):
  out=[]
  while n:n,r=divmod(n,92);out.append(ABC[r])
  return ''.join(reversed(out)) or '!'
def balanced(names,var='n',lo=0):
  if not names:return '0'
  if len(names)==1:return names[0]
  mid=len(names)//2
  return f'(if {var} < {lo+mid} then {balanced(names[:mid],var,lo)} else {balanced(names[mid:],var,lo+mid)})'

def main():
  if not __debug__:raise RuntimeError('Certificate assertions must remain enabled')
  ap=argparse.ArgumentParser();ap.add_argument('--tree',type=Path,default=HERE/'ordered-proof-input.json')
  ap.add_argument('--compact',type=Path,default=HERE/'ordered-compact.json')
  ap.add_argument('--output',type=Path,default=ROOT/'StructuralW10Cert20261016/Certificate.lean');args=ap.parse_args()
  raw=args.tree.read_bytes();data=json.loads(raw);packed_raw=args.compact.read_bytes();packed=json.loads(packed_raw)
  assert not data.get('unresolved'), 'Never emit an incomplete tree'
  assert packed['receipt']['input_closed'] and packed['receipt']['input_sha256']==hashlib.sha256(raw).hexdigest()
  branches={r['path']:r for r in data['branches']};leaves={r['path']:r for r in packed['leaves']}
  assert len(branches)==len(data['branches']) and len(leaves)==len(packed['leaves'])
  assert len(data['accepted'])==len(leaves)
  assert not set(branches)&set(leaves)
  assert set(leaves)=={r['path'] for r in data['accepted']}
  words=[];payloads=[];visits=set();maxdepth=0
  def visit(p):
    nonlocal maxdepth
    assert p not in visits;visits.add(p);maxdepth=max(maxdepth,len(p)-1)
    if p in branches:
      r=branches[p];w=128*r['cut']+2*r['axis']+1;assert 0<=r['axis']<45 and w<2**28
      words.append(w);visit(p+'0');visit(p+'1')
    else:
      r=leaves[p]
      if r['kind']=='numeric':
        n=0
        for ch in r['text']:n=92*n+ABC.index(ch)
        assert n==int(r['support_hex'],16)*10**8+r['tree_code']
        ident=46+len(payloads);payloads.append(n)
      elif r['kind']=='reflection':ident=0
      else:assert r['kind']=='empty' and 0<=r['violation_axis']<45;ident=r['violation_axis']+1
      assert 0<=2*ident<2**28
      words.append(2*ident)
  visit('r');assert visits==set(branches)|set(leaves)
  assert maxdepth<127 and len(words)==len(branches)+len(leaves)
  allpairs=[(i,i+1) for i in range(9)]+[(i,j) for i in range(10) for j in range(i+2,10)]
  slots={p:k for k,p in enumerate(allpairs)}
  sl=[slots.get((min(i,j),max(i,j)),0) for i in range(10) for j in range(10)]
  out=['''/- SPDX-License-Identifier: Apache-2.0
Generated source for the complete W10 finite certificate. Full compilation
and replay are separate and remain pending until a matching receipt passes.
Every intended leaf/split check uses ordinary kernel evaluation; no external
arithmetic audit is assumed as a theorem. -/
import StructuralW10Cert20261016.AdaptiveCoverage
import StructuralW10Cert20261016.FastPruefer
import StructuralW10Cert20261016.RootBounds
noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralW10Cert20261016.Certificate
''',f'def SL : List ℕ := {sl}\n', 'theorem hSL : SLok 9 PR SL := by decide +kernel\n']
  names=[]
  for k,start in enumerate(range(0,len(words),32)):
    value=sum(w<<(28*r) for r,w in enumerate(words[start:start+32]));name='T'+str(k);names.append(name)
    out.append(f'def {name} : ℕ := ~"{encode(value)}"\n')
  out.append(f'def treeChunk (n : ℕ) : ℕ := {balanced(names)}\n')
  out.append('def read (pos : ℕ) : ℕ := Nat.land (Nat.shiftRight (treeChunk ((pos-1)/32)) (28*((pos-1)%32))) 268435455\n')
  names=[]
  for k,start in enumerate(range(0,len(payloads),32)):
    name='D'+str(k);names.append(name)
    word=offset=0
    for n in payloads[start:start+32]:
      size=n.bit_length();assert size<2048
      word|=size<<offset;offset+=11;word|=n<<offset;offset+=size
    out.append(f'def {name} : ℕ := ~"{encode(word)}"\n')
  out.append(f'def payloadChunk (n : ℕ) : ℕ := {balanced(names)}\n')
  out.append('''def pick : ℕ → ℕ → ℕ
  | 0, w => Nat.land (Nat.shiftRight w 11) (2 ^ (Nat.land w 2047) - 1)
  | n+1, w => pick n (Nat.shiftRight w (11 + Nat.land w 2047))
def payload (n : ℕ) : ℕ := pick (n%32) (payloadChunk (n/32))
''')
  out.append('def leafCheck := FastPruefer.dispatch payload\n')
  out.append(f'''theorem checked : AdaptiveCoverage.walk SL read leafCheck 128 1 RootBounds.initialCell = {len(words)+1} := by
  decide +kernel
theorem initial_covered : CovBy 9 PR (Pg cN 9 BS TS) RootBounds.initialCell := by
  apply AdaptiveCoverage.walk_sound hSL read leafCheck (FastPruefer.dispatch_sound payload) 128 1 RootBounds.initialCell
  rw [checked]
  decide
#print axioms initial_covered
end StructuralW10Cert20261016.Certificate
end
''')
  source=''.join(out).encode('utf8')
  assert args.tree.read_bytes()==raw and args.compact.read_bytes()==packed_raw, 'Certificate inputs changed during emission'
  args.output.write_bytes(source)
  receipt={'scope':'Generated source only; compilation and replay are separate required checks',
    'tree_input':str(args.tree),'compact_input':str(args.compact),'source_output':str(args.output),
    'tree_input_sha256':hashlib.sha256(raw).hexdigest(),'compact_input_sha256':hashlib.sha256(packed_raw).hexdigest(),
    'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'branches':len(branches),'leaves':len(leaves),
    'numeric_leaves':len(payloads),'nodes':len(words),'maxdepth':maxdepth,'source_bytes':len(source),
    'source_sha256':hashlib.sha256(source).hexdigest(),'lean_complete_certificate_proven':False}
  (HERE/'emitted-tree.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8');print(json.dumps(receipt))
if __name__=='__main__':main()
