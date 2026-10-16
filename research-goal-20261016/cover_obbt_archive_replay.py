"""Replay all OBBT witnesses from the compact projection and gzip shards.

The full 41k-node source snapshot and raw 44.7 MB OBBT witness are unnecessary.
Root cells and all ancestor edges are reconstructed independently. All 806
cell geometries and 12,180 separate scalar-mixture/Lagrange-flow bounds are
then checked without an LP or flow optimizer. Global completion is false.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,gzip,hashlib,json,time
import cover_sublevel_obbt_verify as verifier
from cover_correlated_verify import make_table
from cover_correlated_replay import a,SC

HERE=Path(__file__).parent;ROOT=HERE.parent
def sha(raw):return hashlib.sha256(raw).hexdigest()
def ceil(x):return -((-x.numerator)//x.denominator)

def load(directory,row):
    raw=(directory/row['file']).read_bytes();assert len(raw)==row['bytes'] and sha(raw)==row['sha256']
    assert len(raw)<=4*1024*1024;decoded=gzip.decompress(raw);assert sha(decoded)==row['uncompressed_sha256'];return json.loads(decoded)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('archive',nargs='?',type=Path,default=HERE/'cover-obbt-archive')
    ap.add_argument('--output',type=Path);args=ap.parse_args();start=time.monotonic();raw=(args.archive/'manifest.json').read_bytes();manifest=json.loads(raw)
    assert manifest['format']=='OBBT-finite-witness-projection-v1' and not manifest['complete_global_cover']
    for path,digest in manifest['sources'].items():assert sha((ROOT/path).read_bytes())==digest,path
    projection=load(args.archive,manifest['projection']);rows=[]
    for shard in manifest['witness_shards']:
        piece=load(args.archive,shard);assert piece['first']==len(rows)==shard['first'] and len(piece['rows'])==shard['rows'];rows.extend(piece['rows'])
    proof={'receipt':manifest['source_receipt'],'contractions':rows}
    reconstructed=(json.dumps(proof,separators=(',',':'))+manifest['source_proof_final_newline']).encode('utf8')
    assert sha(reconstructed)==manifest['source_proof_sha256'];assert len(rows)==manifest['total_witness_paths']
    params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes());bs=params['b_numerators'];sep=123*SC//128
    floor=F(projection['source_target']);assert floor==F(221,25000);cn=floor*10**10;assert cn.denominator==1
    budget=int(cn)*SC-sum(bs)*sep;up=[sep+ceil(F(budget,b)) for b in bs]
    lo=[(j-i)*sep for i,j in a.PAIRS];hi=[min(sum(up[i:j]),(j-i)*sep+ceil(F(budget,min(bs[i:j])))) for i,j in a.PAIRS]
    root=[lo,hi];assert root==projection['source_root'];a.closure_valid(root)
    branches={b['path']:b for b in projection['branches']};witnesses={r['path']:r for r in rows}
    assert len(branches)==len(projection['branches']) and len(witnesses)==len(rows) and sorted(witnesses)==projection['witness_paths']
    needed={p[:k] for p in witnesses for k in range(1,len(p)+1)};todo=[('r',root)];seen=set();verified=0;bounds=0;closed=0;table=make_table(HERE/'cover_newjet.json')
    target=int(manifest['source_receipt']['target_numerator']);assert target==floor*int(projection['energy_denominator'])
    while todo:
        path,state=todo.pop();seen.add(path)
        if path in witnesses:
            row=witnesses[path];assert row['old_cell']==state
            result=verifier.verify(row,target,table);verified+=1;bounds+=result['bounds'];closed+=result['closed']
        if path in branches:
            branch=branches[path];z=branch['axis'];q=branch['cut'];assert state[0][z]<q<state[1][z]
            for bit,upper in [('1',False),('0',True)]:
                if path+bit in needed:
                    child=a.child(state,z,q,upper);assert child is not None;todo.append((path+bit,child))
    assert seen==needed and verified==len(rows) and bounds==manifest['total_bounds']
    result={'scope':__doc__,'manifest_sha256':sha(raw),'script_sha256':sha(Path(__file__).read_bytes()),'all_passed':True,
      'verified_witness_paths':verified,'verified_bounds':bounds,'closed_parent_cells':closed,'reconstructed_ancestor_branches':len(branches),
      'source_proof_reconstructed_byte_exactly':True,'source_proof_sha256':manifest['source_proof_sha256'],
      'full_source_snapshot_required':False,'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,
      'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    output=args.output or args.archive/'replay.json';output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8');print(json.dumps(result),flush=True)
if __name__=='__main__':main()
