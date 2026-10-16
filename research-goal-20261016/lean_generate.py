"""Checkpointable COMPLETE W10 proof; every emitted subtree is a kernel task.

Python constructs proof source, but neither its geometry nor its arithmetic is
trusted: the leaf interpreters and all composition equalities are checked in Lean.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, sys

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
OLD = ROOT/'research-20261016-w10-cert'
sys.path.insert(0, str(OLD))
import emit_tree as codec

PAIRS = [(i,i+1) for i in range(9)] + [(i,j) for i in range(10) for j in range(i+2,10)]
SLOTS = {p:k for k,p in enumerate(PAIRS)}
BB=1<<42

def split(state, axis, cut, upper):
    lo, hi = state
    i,j=PAIRS[axis]
    a,b,w=(i,j,cut) if upper else (j,i,-cut)
    def leg(x,y):
        return 0 if x==y else hi[SLOTS[x,y]] if x<y else -lo[SLOTS[y,x]]
    col=[max(0,BB+leg(x,a)) for x in range(10)]
    row=[max(0,BB+w+leg(b,x)) for x in range(10)]
    return ([max(v,max(0,2*BB-col[j]-row[i])) for v,(i,j) in zip(lo,PAIRS)],
            [min(v,max(0,col[i]+row[j]-2*BB)) for v,(i,j) in zip(hi,PAIRS)])

def normalize(state):
    if state[1][0] <= state[1][8] and state[0][0] <= state[0][8]:
        return state
    for _ in range(2):
        state=split(state,0,state[1][8],True)
        state=split(state,8,state[0][0],False)
    return state

def cl(state):
    fmt=lambda xs:'['+', '.join(map(str,xs))+']'
    return '⟨'+', '.join(map(fmt,[state[0][:9],state[1][:9],state[0][9:],state[1][9:]]))+'⟩'

def sha(raw):return hashlib.sha256(raw).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--max-leaves',type=int,default=1024)
    ap.add_argument('--retain-first',action='store_true',help='Keep the active first module byte-identical while subdividing all later subtrees.')
    args=ap.parse_args()
    retained=None
    if args.retain_first:
        previous=json.loads((HERE/'lean_manifest.json').read_text())
        retained=previous['modules'][0]
    tree_raw=(OLD/'ordered-proof-input.json').read_bytes()
    compact_raw=(OLD/'ordered-compact.json').read_bytes()
    assert sha(tree_raw)=='6f2bc79db4613b4130659c9e65e0a24ee07cc50fb0686878d01a8e3f73839c3e'
    assert sha(compact_raw)=='5fbb16de9f2b74d1816d7e251efb16c07c4f318a1aedf1a390f18ef6fe499463'
    tree=json.loads(tree_raw); packed=json.loads(compact_raw)
    assert not tree['unresolved'] and packed['receipt']['input_closed']
    branches={x['path']:x for x in tree['branches']}
    leaves={x['path']:x for x in packed['leaves']}
    counts={}
    def count(p):
        counts[p]=count(p+'0')+count(p+'1') if p in branches else 1
        return counts[p]
    assert count('r')==95779 and len(counts)==191557
    chunks=[];skeleton=[]
    def carve(p,state):
        if counts[p]<=args.max_leaves or (retained and p==retained['prefix']):
            chunks.append((p,state));return
        row=branches[p]; normal=normalize(state)
        left=split(normal,row['axis'],row['cut'],True)
        right=split(normal,row['axis'],row['cut'],False)
        skeleton.append((p,state,normal,left,right))
        carve(p+'0',left);carve(p+'1',right)
    carve('r',tree['root'])
    srcdir=ROOT/'StructuralGoal20261016';srcdir.mkdir(exist_ok=True)
    records=[];cover={}
    for idx,(prefix,state) in enumerate(chunks):
        name=f'LeanCoverPart{idx:03d}'
        module='StructuralGoal20261016.'+name
        words=[];payloads=[]
        def visit(p):
            if p in branches:
                row=branches[p];words.append(128*row['cut']+2*row['axis']+1)
                visit(p+'0');visit(p+'1')
            else:
                row=leaves[p]
                if row['kind']=='numeric':
                    ident=46+len(payloads)
                    payloads.append(int(row['support_hex'],16)*10**8+row['tree_code'])
                elif row['kind']=='reflection':ident=0
                else:
                    assert row['kind']=='empty';ident=row['violation_axis']+1
                words.append(2*ident)
        visit(prefix)
        head='''/- Complete frozen subtree. Only the final composition covers the full domain. -/
import StructuralGoal20261016.LeanCoverBase
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
open StructuralGoal20261016.LeanCoverBase
open StructuralW10Unconditional20261016
open StructuralW10Cert20261016
'''
        out=[head,'namespace '+module+'\n',f'-- Frozen tree path {prefix}\n',f'def initialCell : Cl := {cl(state)}\n']
        names=[]
        for k,start in enumerate(range(0,len(words),32)):
            value=sum(w<<(28*r) for r,w in enumerate(words[start:start+32]))
            names.append('T'+str(k));out.append(f'def T{k} : ℕ := ~"{codec.encode(value)}"\n')
        out.append(f'def treeChunk (n : ℕ) : ℕ := {codec.balanced(names)}\n')
        out.append('def read (pos : ℕ) : ℕ := Nat.land (Nat.shiftRight (treeChunk ((pos-1)/32)) (28*((pos-1)%32))) 268435455\n')
        names=[]
        for k,start in enumerate(range(0,len(payloads),32)):
            value=offset=0
            for payload in payloads[start:start+32]:
                bits=payload.bit_length();assert bits<2048
                value|=bits<<offset;offset+=11
                value|=payload<<offset;offset+=bits
            names.append('D'+str(k));out.append(f'def D{k} : ℕ := ~"{codec.encode(value)}"\n')
        out.append(f'def payloadChunk (n : ℕ) : ℕ := {codec.balanced(names)}\n')
        out.append('''def pick : ℕ → ℕ → ℕ
  | 0, w => Nat.land (Nat.shiftRight w 11) (2 ^ (Nat.land w 2047) - 1)
  | n+1, w => pick n (Nat.shiftRight w (11 + Nat.land w 2047))
def payload (n : ℕ) : ℕ := pick (n%32) (payloadChunk (n/32))
def leafCheck := ForcedCoverage2.dispatch payload
''')
        out.append(f'''theorem checked : FixedGeometry.walk SL read leafCheck 128 1 (FixedGeometry.Cell.ofCl initialCell) = {len(words)+1} := by
  decide +kernel
theorem covered : CovBy 9 PR (Pg cN 9 BS TS) initialCell := by
  apply FixedGeometry.walk_sound hSL cN read leafCheck (ForcedCoverage2.dispatch_sound payload) 128 1 (FixedGeometry.Cell.ofCl initialCell)
  rw [checked]
  decide
#print axioms covered
end {module}
end
''')
        path=srcdir/(name+'.lean');raw=''.join(out).encode();path.write_bytes(raw)
        if idx==0 and retained:
            assert sha(raw)==retained['source_sha256'], 'Never change the active/proved first module'
        records.append(dict(module=module,source=str(path.relative_to(ROOT)).replace('\\','/'),source_sha256=sha(raw),source_bytes=len(raw),prefix=prefix,nodes=len(words),leaves=counts[prefix],numeric_leaves=len(payloads)))
        cover[prefix]=module+'.covered'
    # The composition is separate, so terminal modules are durable checkpoints.
    out=['/- Complete domain composition, valid only after ALL imports compile. -/\n']
    out.extend('import '+r['module']+'\n' for r in records)
    out.append('import StructuralGoal20261016.LeanCoverGeometry\n')
    out.append('import StructuralW10Cert20261016.RootBounds\n')
    out.append('''set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
open StructuralGoal20261016.LeanCoverBase
namespace StructuralGoal20261016.LeanCoverComplete
''')
    for idx,(p,state,normal,left,right) in reversed(list(enumerate(skeleton))):
        row=branches[p];i,j=PAIRS[row['axis']]
        name=f'node{idx:03d}';cover[p]=name
        out.append(f'def cell{idx:03d} : Cl := {cl(state)}\n')
        out.append(f'theorem {name} : CovBy 9 PR (Pg cN 9 BS TS) cell{idx:03d} := by\n')
        # Types at child theorem applications force the three concrete equalities.
        geo=f'StructuralGoal20261016.LeanCoverGeometry.node{idx:03d}'
        out.append(f'  exact branch {i} {j} {row["cut"]} (by decide) (by decide) (normal := {cl(normal)}) {geo}.1 {geo}.2.1 {geo}.2.2 {cover[p+"0"]} {cover[p+"1"]}\n')
    out.append('theorem initial_covered : CovBy 9 PR (Pg cN 9 BS TS) StructuralW10Cert20261016.RootBounds.initialCell := '+cover['r']+'\n')
    out.append('#print axioms initial_covered\nend StructuralGoal20261016.LeanCoverComplete\nend\n')
    path=srcdir/'LeanCoverComplete.lean';path.write_text(''.join(out),encoding='utf8',newline='\n')
    # Validate every concrete top-level geometry equality before the long run
    # finishes. This module asserts no numerical floor by itself.
    geo=['''/- All concrete geometry equalities for complete composition. -/
import StructuralGoal20261016.LeanCoverBase
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
open StructuralW10Cert20261016.TreeCoverage
open StructuralGoal20261016.LeanCoverBase
namespace StructuralGoal20261016.LeanCoverGeometry
''']
    for idx,(p,state,normal,left,right) in enumerate(skeleton):
        row=branches[p];i,j=PAIRS[row['axis']];q=row['cut']
        geo.append(f'theorem node{idx:03d} : StructuralW10Cert20261016.AdaptiveCoverage.normalize SL ({cl(state)}) = ({cl(normal)}) ∧ leftChild 9 PR SL ({cl(normal)}) {i} {j} {q} = ({cl(left)}) ∧ rightChild 9 PR SL ({cl(normal)}) {i} {j} {q} = ({cl(right)}) := by\n  exact ⟨rfl, rfl, rfl⟩\n')
    geo.append('#print axioms node000\nend StructuralGoal20261016.LeanCoverGeometry\nend\n')
    (srcdir/'LeanCoverGeometry.lean').write_text(''.join(geo),encoding='utf8',newline='\n')
    manifest=dict(scope='Complete W10 partition source generation, not a proof receipt. All parts plus final composition require ordinary kernel compilation.',generator_sha256=sha(Path(__file__).read_bytes()),tree_sha256=sha(tree_raw),compact_sha256=sha(compact_raw),max_leaves=args.max_leaves,total_nodes=sum(r['nodes'] for r in records)+len(skeleton),total_numeric_leaves=sum(r['numeric_leaves'] for r in records),chunks=len(records),composition_branches=len(skeleton),modules=records,composition_source_sha256=sha(path.read_bytes()),complete_lean_proven=False)
    assert manifest['total_nodes']==191557 and manifest['total_numeric_leaves']==95615
    (HERE/'lean_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in manifest.items() if k!='modules'}),flush=True)

if __name__=='__main__':main()
