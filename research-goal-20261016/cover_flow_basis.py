"""Compress exact flow witnesses to edge forests, independently decoding amounts.

The divergence is computed by the surrounding mathematical certificate, so
the witness need only select edges. Leaf elimination reconstructs every
integer amount; positivity and exact balance are checked afterwards. This
probe compares every reconstructed witness with the original audited flow.
It does not assert a complete cover, a Lean decoder proof, or a size-limit
pass for a website submission.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,time
HERE=Path(__file__).parent

def decode(divergence,edges):
    div=list(map(int,divergence));n=len(div);adj=[set() for _ in range(n)]
    assert len(set(map(tuple,edges)))==len(edges)
    for k,(i,j) in enumerate(edges):
        assert 0<=i<n and 0<=j<n and i!=j
        adj[i].add(k);adj[j].add(k)
    todo=[i for i in range(n) if len(adj[i])==1];amounts=[None]*len(edges)
    while todo:
        u=todo.pop()
        if len(adj[u])!=1:continue
        k=next(iter(adj[u]));i,j=edges[k];v=j if u==i else i
        amount=div[u] if u==i else -div[u];assert amount>=0
        amounts[k]=amount;div[v]+=div[u];div[u]=0
        adj[u].remove(k);adj[v].remove(k)
        if len(adj[v])==1:todo.append(v)
    assert all(v is not None for v in amounts),'non-forest flow support'
    assert all(v==0 for v in div),'unbalanced component'
    balance=[0]*n
    for (i,j),v in zip(edges,amounts):balance[i]+=v;balance[j]-=v
    assert balance==list(map(int,divergence))
    return amounts

def walk(value):
    if isinstance(value,dict):
        if 'nonzero_flow' in value and 'divergence' in value:yield value
        for child in value.values():yield from walk(child)
    elif isinstance(value,list):
        for child in value:yield from walk(child)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-sublevel-obbt.json')
    ap.add_argument('--output',type=Path,default=HERE/'cover-flow-basis-probe.json');args=ap.parse_args();start=time.monotonic()
    raw=args.input.read_bytes();doc=json.loads(raw);count=edges_count=old_bytes=basis_bytes=0
    old_stream=[];basis_stream=[];failures=[]
    for k,flow in enumerate(walk(doc)):
        edges=[row[:2] for row in flow['nonzero_flow']]
        try:
            amounts=decode(flow['divergence'],edges)
            assert amounts==[int(row[2]) for row in flow['nonzero_flow']]
            assert sum(v*row[3] for v,row in zip(amounts,flow['nonzero_flow']))==int(flow['cost'])
        except AssertionError as e:failures.append({'flow_index':k,'error':str(e)});continue
        old=json.dumps(flow,separators=(',',':')).encode()
        # Fixed n=10; endpoints fit one byte. No amounts or edge costs are stored.
        basis=bytes([10*i+j for i,j in edges])
        count+=1;edges_count+=len(edges);old_bytes+=len(old);basis_bytes+=len(basis)
        old_stream.append(old);basis_stream.append(bytes([len(basis)])+basis)
    out={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),
      'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'decoded_flows':count,'directed_edges':edges_count,'failures':failures,
      'old_flow_JSON_bytes':old_bytes,'edge_basis_bytes_including_lengths':basis_bytes+count,
      'old_flow_stream_gzip_bytes':len(gzip.compress(b'\n'.join(old_stream),mtime=0)),
      'basis_stream_gzip_bytes':len(gzip.compress(b''.join(basis_stream),mtime=0)),
      'all_original_amounts_and_costs_reconstructed':not failures,
      'divergence_must_be_recomputed_by_surrounding_checker':True,
      'Lean_decoder_soundness_proven':False,'complete_global_cover':False,
      'final_submission_size_limit_passed':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
