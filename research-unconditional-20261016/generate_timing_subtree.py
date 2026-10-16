"""Select a real closed subtree of the independently audited full input.

Emit a fixed-field, optionally streaming-dual smoke. No global coverage
claim is created by this script; each emitted theorem must compile.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent
OLD=ROOT/'research-20261016-w10-cert'
sys.path.insert(0,str(OLD))
import emit_tree as emit
import ordered_generate as og

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--maxnodes',type=int,default=255)
    ap.add_argument('--name',default='StreamingDual128Smoke')
    ap.add_argument('--streaming',action='store_true')
    args=ap.parse_args()
    raw=(OLD/'ordered-proof-input.json').read_bytes()
    craw=(OLD/'ordered-compact.json').read_bytes()
    doc=json.loads(raw)
    compact=json.loads(craw)
    assert not doc['unresolved'] and compact['receipt']['input_closed']
    assert compact['receipt']['input_sha256']==hashlib.sha256(raw).hexdigest()
    branches={a['path']:a for a in doc['branches']}
    leaves={a['path']:a for a in compact['leaves']}
    size={p:1 for p in leaves}
    nonnumeric={p:int(r['kind']!='numeric') for p,r in leaves.items()}
    for p in sorted(branches,key=len,reverse=True):
        size[p]=1+size[p+'0']+size[p+'1']
        nonnumeric[p]=nonnumeric[p+'0']+nonnumeric[p+'1']
    candidates=[p for p,n in size.items() if 31<=n<=args.maxnodes and nonnumeric[p]==0]
    prefix=max(candidates,key=lambda p:(size[p],len(p)))
    state=doc['root']
    path='r'
    for bit in prefix[1:]:
        normalized,_=og.normalize(state)
        b=branches[path]
        state=og.rawsplit(normalized,b['axis'],b['cut'],bit=='0')
        path+=bit
    initial=state
    words=[]
    payloads=[]
    def visit(p):
        if p in branches:
            b=branches[p]
            words.append(128*b['cut']+2*b['axis']+1)
            visit(p+'0')
            visit(p+'1')
        else:
            r=leaves[p]
            assert r['kind']=='numeric'
            words.append(2*(46+len(payloads)))
            payloads.append(int(r['support_hex'],16)*100000000+r['tree_code'])
    visit(prefix)
    assert len(words)==size[prefix]
    ns='StructuralW10Unconditional20261016.'+args.name
    template=(ROOT/'StructuralW10Unconditional20261016/FixedGeometrySmoke.lean').read_text(encoding='utf8')
    header=template[:template.index('-- original subtree')]
    header=header.replace('StructuralW10Unconditional20261016.FixedGeometrySmoke',ns)
    out=[header,'-- original subtree '+prefix+'\n']
    fmt=lambda v:'['+', '.join(map(str,v))+']'
    out.append('def initialCell : Cl := ⟨'+', '.join(fmt(v) for v in [initial[0][:9],initial[1][:9],initial[0][9:],initial[1][9:]])+'⟩\n')
    sl=[og.g.LOOK.get((min(i,j),max(i,j)),0) for i in range(10) for j in range(10)]
    out.append('def SL : List ℕ := '+str(sl)+'\ntheorem hSL : SLok 9 PR SL := by decide +kernel\n')
    for tag,values in [('T',words),('D',payloads)]:
        names=[]
        for k,start in enumerate(range(0,len(values),32)):
            if tag=='T':
                packed=sum(w<<(28*r) for r,w in enumerate(values[start:start+32]))
            else:
                packed=offset=0
                for value in values[start:start+32]:
                    n=value.bit_length()
                    assert n<2048
                    packed|=n<<offset
                    offset+=11
                    packed|=value<<offset
                    offset+=n
            name=tag+str(k)
            names.append(name)
            out.append(f'def {name} : ℕ := ~"{emit.encode(packed)}"\n')
        if tag=='T':
            out.append(f'def treeChunk (n : ℕ) : ℕ := {emit.balanced(names)}\n')
            out.append('def read (pos : ℕ) : ℕ := Nat.land (Nat.shiftRight (treeChunk ((pos-1)/32)) (28*((pos-1)%32))) 268435455\n')
        else:
            out.append(f'def payloadChunk (n : ℕ) : ℕ := {emit.balanced(names)}\n')
    tail=template[template.index('def pick :'):].replace('StructuralW10Unconditional20261016.FixedGeometrySmoke',ns)
    tail=tail.replace('= 64 := by',f'= {len(words)+1} := by')
    if args.streaming:
        out.insert(0,'import StructuralW10Unconditional20261016.StreamingDual\n')
        tail=tail.replace('ForcedCoverage2.dispatch payload','StreamingDual.dispatch cN payload').replace('ForcedCoverage2.dispatch_sound payload','StreamingDual.dispatch_sound cN payload')
    out.append(tail)
    source=''.join(out).encode('utf8')
    path=ROOT/('StructuralW10Unconditional20261016/'+args.name+'.lean')
    path.write_bytes(source)
    receipt={'scope':'Generated real subtree source only; ordinary kernel check remains required.',
             'prefix':prefix,'nodes':len(words),'numeric_leaves':len(payloads),'streaming_dual':args.streaming,
             'tree_sha256':hashlib.sha256(raw).hexdigest(),'compact_sha256':hashlib.sha256(craw).hexdigest(),
             'source':str(path.relative_to(ROOT)),'source_bytes':len(source),'source_sha256':hashlib.sha256(source).hexdigest()}
    (HERE/(args.name+'-generated.json')).write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8')
    print(json.dumps(receipt),flush=True)

if __name__=='__main__':
    main()
