"""Replay the compact edge-only archive without the original large JSON.

Rebuild each witness cell from the pressure root and ancestor projection,
derive each divergence from the independently verified coefficient vector,
reconstruct all amounts/costs, and recover the original proof SHA exactly.
Only a finite sample is checked; complete global coverage remains false.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,gzip,hashlib,json,time
import cover_flow_basis_replay as basis
from cover_correlated_replay import a,SC
HERE=Path(__file__).parent;ROOT=HERE.parent
def sha(raw):return hashlib.sha256(raw).hexdigest()
def ceil(x):return -((-x.numerator)//x.denominator)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('archive',nargs='?',type=Path,default=HERE/'cover-flow-basis-pruned')
    args=ap.parse_args();start=time.monotonic();header_raw=(args.archive/'replay.json').read_bytes();header=json.loads(header_raw)
    for path,digest in header['source_sha256'].items():assert sha((ROOT/path).read_bytes())==digest,path
    chunks=[]
    for part in header['parts']:
        raw=(args.archive/part['file']).read_bytes();assert len(raw)==part['bytes']<=4*1024*1024 and sha(raw)==part['sha256']
        chunks.append(raw)
    zipped=b''.join(chunks);assert sha(zipped)==header['gzip_sha256']
    packed=gzip.decompress(zipped);assert sha(packed)==header['compressed_proof_sha256'];proof=json.loads(packed)
    # The original immutable projection pins the locations of the sampled
    # cells; its witness shards are not needed by this replay.
    oldfolder=HERE/'cover-obbt-archive';old_raw=(oldfolder/'manifest.json').read_bytes();old=json.loads(old_raw)
    for path,digest in old['sources'].items():assert sha((ROOT/path).read_bytes())==digest,path
    if proof['receipt'].get('input_sha256'):
        assert proof['receipt']['input_sha256']==old['source_proof_sha256']
    else:assert header['original_proof_sha256']==old['source_proof_sha256']
    part=old['projection'];raw=(oldfolder/part['file']).read_bytes();assert sha(raw)==part['sha256']
    packed_projection=gzip.decompress(raw);assert sha(packed_projection)==part['uncompressed_sha256'];projection=json.loads(packed_projection)
    params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes());bs=params['b_numerators'];sep=123*SC//128
    floor=F(projection['source_target']);cn=floor*10**10;assert cn.denominator==1
    budget=int(cn)*SC-sum(bs)*sep;up=[sep+ceil(F(budget,b)) for b in bs]
    root=[[(j-i)*sep for i,j in a.PAIRS],
      [min(sum(up[i:j]),(j-i)*sep+ceil(F(budget,min(bs[i:j])))) for i,j in a.PAIRS]]
    assert root==projection['source_root'];a.closure_valid(root)
    rows={r['path']:r for r in proof['contractions']};assert len(rows)==len(proof['contractions'])
    needed={p[:k] for p in rows for k in range(1,len(p)+1)}
    branches={r['path']:r for r in projection['branches']};todo=[('r',root)];seen=set();cells=0
    while todo:
        path,state=todo.pop();seen.add(path)
        if path in rows:assert rows[path]['old_cell']==state;cells+=1
        if path in branches:
            branch=branches[path];z=branch['axis'];q=branch['cut'];assert state[0][z]<q<state[1][z]
            for bit,upper in [('1',False),('0',True)]:
                if path+bit in needed:
                    child=a.child(state,z,q,upper);assert child is not None;todo.append((path+bit,child))
    assert seen==needed and cells==len(rows)
    v=basis.verifier;v.flow_bound=basis.bound;v.shared.flow_bound=basis.bound;v.verify_direction=basis.direction
    table=v.make_table(HERE/'cover_newjet.json');target=int(proof['receipt']['target_numerator']);counts={'paths':0,'bounds':0,'closed':0}
    for row in proof['contractions']:
        result=v.verify(row,target,table);counts['paths']+=1
        for k in ['bounds','closed']:counts[k]+=result[k]
    canonical=json.dumps(proof,separators=(',',':')).encode()
    endings=[end for end in [b'',b'\n',b'\r\n'] if len(canonical+end)==header['original_bytes'] and sha(canonical+end)==header['original_proof_sha256']]
    assert len(endings)==1 and counts['paths']==header['counts']['paths']
    out={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'archive_header_sha256':sha(header_raw),
      'projection_manifest_sha256':sha(old_raw),'counts':{**counts,**basis.counts},
      'witness_cells_reconstructed':cells,'ancestor_nodes_reconstructed':len(seen),
      'original_large_proof_required':False,'original_proof_reconstructed_byte_exactly':True,
      'original_proof_sha256':header['original_proof_sha256'],'all_passed':True,
      'actual_analytic_Lean_bridges_complete':False,'complete_global_cover':False,'new_zero_proportion_proven':False,
      'final_submission_size_limit_passed':False,'seconds':time.monotonic()-start}
    (args.archive/'independent-replay.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
