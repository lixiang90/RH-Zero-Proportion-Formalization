"""Build a small, real closed subtree for end-to-end Lean replay timing."""
from pathlib import Path
import argparse,hashlib,json,time
import ordered_generate as og
import emit_tree as emit
import relative_codec as codec
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'ordered-0.json');ap.add_argument('--maxnodes',type=int,default=63);args=ap.parse_args()
 raw=args.input.read_bytes();doc=json.loads(raw);master=json.loads((HERE/'ordered-master.json').read_text());assert not doc['unresolved']
 branches={a['path']:a for a in master['branches']+doc['branches']};leaves={a['path']:a for a in doc['accepted']}
 size={p:1 for p in leaves}
 for p in sorted(branches,key=len,reverse=True):
  if p+'0'in size and p+'1'in size:size[p]=1+size[p+'0']+size[p+'1']
 candidates=[p for p,n in size.items() if 31<=n<=args.maxnodes]
 assert candidates
 prefix=max(candidates,key=lambda p:(size[p],len(p)))
 state=doc['root'];p='r'
 for bit in prefix[1:]:
  norm,_=og.normalize(state);b=branches[p];state=og.rawsplit(norm,b['axis'],b['cut'],bit=='0');p+=bit
 initial=state;words=[];payloads=[];cells={};maxdepth=0
 def walk(p,state):
  nonlocal maxdepth
  maxdepth=max(maxdepth,len(p)-len(prefix));state,cuts=og.normalize(state);cells[p]=state
  if p in branches:
   b=branches[p];words.append(128*b['cut']+2*b['axis']+1)
   walk(p+'0',og.rawsplit(state,b['axis'],b['cut'],True));walk(p+'1',og.rawsplit(state,b['axis'],b['cut'],False))
  else:
   rec=leaves[p]['result'];cert=rec['certificate'];assert tuple(state)==(cert['lower_bounds'],cert['upper_bounds']),p
   if 'FS'in rec:
    packed=codec.prepare(rec,4);ident=46+len(payloads);payloads.append(packed['text'])
   elif rec.get('reflection'):ident=0
   else:assert rec.get('empty');ident=rec['violation_axis']+1
   words.append(2*ident)
 walk(prefix,initial);assert len(words)==size[prefix]
 allpairs=og.g.ALL;lookup={p:k for k,p in enumerate(allpairs)};sl=[lookup.get((min(i,j),max(i,j)),0) for i in range(10)for j in range(10)]
 fmt=lambda a:'['+', '.join(map(str,a))+']'
 out=['''/- A closed real subtree only. No global W10 floor is asserted. -/
import StructuralW10Cert20261016.OrderCoverage
import StructuralW10Cert20261016.LeafDispatch
noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralW10Cert20261016.ClosedTreeSmoke
''',f'-- original subtree {prefix}\n',f'def initialCell : Cl := ⟨{fmt(initial[0][:9])}, {fmt(initial[1][:9])}, {fmt(initial[0][9:])}, {fmt(initial[1][9:])}⟩\n',f'def SL : List ℕ := {sl}\n','theorem hSL : SLok 9 PR SL := by decide +kernel\n']
 names=[]
 for k,start in enumerate(range(0,len(words),32)):
  w=sum(x<<(28*j)for j,x in enumerate(words[start:start+32]));name='T'+str(k);names.append(name);out.append(f'def {name} : ℕ := ~"{emit.encode(w)}"\n')
 out.append(f'def treeChunk (n : ℕ) : ℕ := {emit.balanced(names)}\n')
 out.append('def read (pos : ℕ) : ℕ := Nat.land (Nat.shiftRight (treeChunk ((pos-1)/32)) (28*((pos-1)%32))) 268435455\n')
 names=[]
 for k,start in enumerate(range(0,len(payloads),32)):
  word=offset=0
  for text in payloads[start:start+32]:
   n=0
   for ch in text:n=92*n+emit.ABC.index(ch)
   bits=n.bit_length();assert bits<2048
   word|=bits<<offset;offset+=11;word|=n<<offset;offset+=bits
  name='D'+str(k);names.append(name);out.append(f'def {name} : ℕ := ~"{emit.encode(word)}"\n')
 out.append(f'def payloadChunk (n : ℕ) : ℕ := {emit.balanced(names)}\n')
 out.append("""def pick : ℕ → ℕ → ℕ
  | 0, w => Nat.land (Nat.shiftRight w 11) (2 ^ (Nat.land w 2047) - 1)
  | n+1, w => pick n (Nat.shiftRight w (11 + Nat.land w 2047))
def payload (n : ℕ) : ℕ := pick (n%32) (payloadChunk (n/32))
def leafCheck := LeafDispatch.check payload
""")
 out.append(f'''theorem checked : OrderCoverage.walk SL read leafCheck 128 1 initialCell = {len(words)+1} := by
  decide +kernel

theorem covered : CovBy 9 PR (Pg cN 9 BS TS) initialCell := by
  apply OrderCoverage.walk_sound hSL read leafCheck (LeafDispatch.check_sound payload) 128 1 initialCell
  rw [checked]
  decide
#print axioms covered
end StructuralW10Cert20261016.ClosedTreeSmoke
end
''')
 target=ROOT/'StructuralW10Cert20261016/ClosedTreeSmoke.lean';source=''.join(out).encode();target.write_bytes(source)
 report={'scope':'Source generation for one real closed subtree; Lean replay separate.',
  'input':str(args.input),'input_sha256':hashlib.sha256(raw).hexdigest(),'prefix':prefix,'nodes':len(words),
  'numeric_leaves':len(payloads),'max_relative_depth':maxdepth,'source_bytes':len(source),'source_sha256':hashlib.sha256(source).hexdigest()}
 (HERE/'closed-tree-smoke-generated.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
