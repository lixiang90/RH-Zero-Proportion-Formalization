"""End-to-end replay of OBBT data with edge-only flow witnesses.

All divergences come from independently recomputed mixture/gradient
coefficients; edge costs come from the current cell. No recorded amounts,
divergences, edge costs or total flow cost are retained. The original scalar,
capacity, Lagrange, rounding and direction verifiers still run in full. The
expanded proof must reconstruct the original audited SHA byte for byte.
This is a finite numerical sample, not a global or Lean floor proof.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,time
import cover_flow_basis as codec
import cover_sublevel_obbt_verify as verifier
shared=verifier.shared;a=verifier.a;HERE=Path(__file__).parent
original_bound=verifier.flow_bound;original_direction=verifier.verify_direction
counts={'expanded_flows':0,'edges':0}

def shrink(value):
    if isinstance(value,dict):
        if 'nonzero_flow' in value and 'divergence' in value:
            edges=[r[:2] for r in value['nonzero_flow']]
            assert codec.decode(value['divergence'],edges)==[int(r[2]) for r in value['nonzero_flow']]
            return {'edge_basis':[10*i+j for i,j in edges]}
        return {k:shrink(v) for k,v in value.items()}
    if isinstance(value,list):return [shrink(v) for v in value]
    return value

def expand(flow,desired,state):
    assert set(flow)=={'edge_basis'}
    codes=flow['edge_basis'];assert all(isinstance(v,int) and 0<=v<100 for v in codes)
    edges=[divmod(v,10) for v in codes];amounts=codec.decode(desired,edges)
    rows=[[i,j,str(y),a.edge_value(state,i,j)] for (i,j),y in zip(edges,amounts)]
    cost=sum(int(y)*u for i,j,y,u in rows)
    flow.clear();flow.update({'divergence':list(map(str,desired)),'nonzero_flow':rows,'cost':str(cost)})
    counts['expanded_flows']+=1;counts['edges']+=len(edges)

def bound(state,coefficient,flow):
    desired=[-coefficient[0]]+[coefficient[i-1]-coefficient[i] for i in range(1,9)]+[coefficient[-1]]
    expand(flow,desired,state)
    return original_bound(state,coefficient,flow)

def direction(state,result,params,table):
    coefficient=list(map(int,result['exact_flow']['coefficient']))
    desired=[coefficient[0]]+[coefficient[i]-coefficient[i-1] for i in range(1,9)]+[-coefficient[-1]]
    expand(result['exact_flow']['flow'],desired,state)
    # The original verifier independently recomputes the coefficient vector
    # from scalar Taylor bounds and checks it against the diagnostic above.
    return original_direction(state,result,params,table)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-sublevel-obbt.json')
    ap.add_argument('--archive',type=Path,default=HERE/'cover-flow-basis-obbt');args=ap.parse_args();start=time.monotonic()
    raw=args.input.read_bytes();old=json.loads(raw)
    canonical_old=json.dumps(old,separators=(',',':')).encode()
    ending=raw[len(canonical_old):]
    assert ending in [b'',b'\n',b'\r\n'] and canonical_old+ending==raw
    compressed=shrink(old)
    packed=(json.dumps(compressed,separators=(',',':'))+'\n').encode()
    zipped=gzip.compress(packed,compresslevel=9,mtime=0);args.archive.mkdir(exist_ok=True)
    parts=[]
    for i,p in enumerate(range(0,len(zipped),4*1024*1024)):
        piece=zipped[p:p+4*1024*1024];name=f'proof.json.gz.part{i:02d}'
        (args.archive/name).write_bytes(piece);parts.append({'file':name,'bytes':len(piece),'sha256':hashlib.sha256(piece).hexdigest()})
    # Reload the stored bytes; the numerical verifier sees no original flow.
    proof=json.loads(gzip.decompress(b''.join((args.archive/p['file']).read_bytes() for p in parts)))
    verifier.flow_bound=bound;shared.flow_bound=bound;verifier.verify_direction=direction
    table=verifier.make_table(HERE/'cover_newjet.json');target=int(proof['receipt']['target_numerator'])
    result={'paths':0,'bounds':0,'closed':0}
    for row in proof['contractions']:
        r=verifier.verify(row,target,table);result['paths']+=1
        for k in ['bounds','closed']:result[k]+=r[k]
    reconstructed=json.dumps(proof,separators=(',',':')).encode()+ending
    assert reconstructed==raw,'expanded proof did not reconstruct the audited original'
    sources=[Path(__file__),Path(codec.__file__),Path(verifier.__file__),Path(shared.__file__),
      HERE/'cover_contractor_verify.py',HERE/'cover_correlated_verify.py',HERE/'cover_correlated_replay.py']
    out={'scope':__doc__,'original_proof_sha256':hashlib.sha256(raw).hexdigest(),
      'compressed_proof_sha256':hashlib.sha256(packed).hexdigest(),'gzip_sha256':hashlib.sha256(zipped).hexdigest(),
      'original_bytes':len(raw),'compressed_JSON_bytes':len(packed),'gzip_bytes':len(zipped),'parts':parts,
      'source_sha256':{str(p.relative_to(HERE.parent)).replace('\\','/'):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
      'counts':{**result,**counts},'original_proof_reconstructed_byte_exactly':True,
      'all_passed':True,'actual_analytic_Lean_bridges_complete':False,'complete_global_cover':False,
      'new_zero_proportion_proven':False,'final_submission_size_limit_passed':False,'seconds':time.monotonic()-start}
    (args.archive/'replay.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
