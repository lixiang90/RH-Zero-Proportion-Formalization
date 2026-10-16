"""Independent replay using only the compact ancestor projection archive.

Verifies correlated descent witnesses and KKT-only Newton contraction chains.
No original 41k-node discovery snapshot, optimizer, or producer is imported.
The projection is deliberately not presented as a complete global cover.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, gzip, hashlib, json, time
import cover_correlated_verify as cv
import cover_contractor_verify as nv
a=nv.a;SC=nv.SC;HERE=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def ceil(x):return -((-x.numerator)//x.denominator)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--archive',type=Path,default=HERE/'cover-compact-archive')
    ap.add_argument('--oracle',type=Path,default=HERE/'cover_newjet.json')
    ap.add_argument('--output',type=Path,default=HERE/'cover-compact-archive/replay.json')
    args=ap.parse_args();start=time.monotonic();manifest=json.loads((args.archive/'manifest.json').read_bytes());docs={}
    for name,metadata in manifest['files'].items():
        raw=(args.archive/name).read_bytes();assert len(raw)==metadata['bytes'] and sha(raw)==metadata['sha256']
        decoded=gzip.decompress(raw)
        if name=='projection.json.gz':assert sha(decoded)==manifest['projection_uncompressed_sha256']
        docs[name]=(json.loads(decoded),sha(decoded))
    projection=docs['projection.json.gz'][0];correlated=docs['correlated-witness.json.gz'][0];contractions=docs['contraction-witness.json.gz'][0]
    receipt=projection['receipt'];original=manifest['original_input_sha256']
    assert receipt['original_input_sha256']==original==correlated['receipt']['input_sha256']==contractions['receipt']['input_sha256']
    assert docs['correlated-witness.json.gz'][1]==receipt['correlated_witness_sha256']
    assert docs['contraction-witness.json.gz'][1]==receipt['contraction_witness_sha256']
    params_path=HERE.parent/'research-20261016-followup/window_reweight_rational.json';params=json.loads(params_path.read_bytes())
    oracle_doc=json.loads(args.oracle.read_bytes());assert sha(params_path.read_bytes())==oracle_doc['receipt']['parameter_sha256']
    assert sha(args.oracle.read_bytes())==correlated['receipt']['oracle_sha256']
    bs=params['b_numerators'];sep=123*SC//128;budget=88400000*SC-sum(bs)*sep;up=[sep+ceil(F(budget,b)) for b in bs]
    root=[[(j-i)*sep for i,j in a.PAIRS],[min(sum(up[i:j]),(j-i)*sep+ceil(F(budget,min(bs[i:j])))) for i,j in a.PAIRS]]
    assert projection['root']==root and projection['separation']=='123/128'
    a.closure_valid(root);table=cv.make_table(oracle_doc)
    branches={r['path']:r for r in projection['branches']};cr={r['path']:r['result'] for r in correlated['exclusions']};nr={r['path']:r for r in contractions['contractions']}
    paths=set(cr)|set(nr);needed={p[:k] for p in paths for k in range(1,len(p)+1)}
    assert set(branches)=={p[:k] for p in paths for k in range(1,len(p))}
    todo=[('r',root)];counts={'correlated_descent':0,'contraction_chains':0,'contraction_steps':0,'newly_excluded_after_contraction':0,'empty_after_contraction':0};visitedbranches=set();minmargin=None
    while todo:
        path,state=todo.pop()
        if path in cr:
            checked=cv.verify(state,cr[path],params,table);counts['correlated_descent']+=1
            margin=int(checked['strict_integer_margin']);minmargin=margin if minmargin is None else min(minmargin,margin)
        if path in nr:
            checked=nv.verify_chain(state,nr[path],params,table);counts['contraction_chains']+=1;counts['contraction_steps']+=checked['iterations']
            counts['newly_excluded_after_contraction']+=checked['newly_excluded'];counts['empty_after_contraction']+=checked['empty']
        if path in branches:
            visitedbranches.add(path);r=branches[path];z=r['axis'];cut=r['cut'];assert state[0][z]<cut<state[1][z]
            for bit,upper in [('1',False),('0',True)]:
                if path+bit in needed:
                    child=a.child(state,z,cut,upper);assert child is not None;todo.append((path+bit,child))
        if path in cr and counts['correlated_descent']%250==0:print(json.dumps({**counts,'seconds':time.monotonic()-start}),flush=True)
    assert visitedbranches==set(branches)
    assert counts['correlated_descent']==len(cr)==receipt['correlated_cells']
    assert counts['contraction_chains']==len(nr)==receipt['contraction_chains']
    result={'scope':__doc__,'passed':True,'archive_manifest_sha256':sha((args.archive/'manifest.json').read_bytes()),
      'script_sha256':sha(Path(__file__).read_bytes()),'verifier_sources':nv.source_hashes(),'oracle_sha256':sha(args.oracle.read_bytes()),
      'original_input_sha256':original,'projection_ancestor_branches_rebuilt':len(visitedbranches),'counts':counts,
      'minimum_descent_integer_margin':str(minmargin),'original_discovery_snapshot_required':False,
      'all_geometry_scalar_bounds_and_integer_flows_replayed':True,'complete_global_cover_asserted':False,
      'actual_kernel_and_KKT_Lean_connections_complete':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8');print(json.dumps(result),flush=True)
if __name__=='__main__':main()
