"""Replay the nine new epigraph global-move chains without original large inputs."""
from pathlib import Path
from fractions import Fraction as F
import argparse,gzip,hashlib,json,time
import cover_compact_codec as codec
import cover_global_move_epigraph_verify as verifier
import cover_sublevel_obbt_verify as obbt
import cover_contractor_verify as newton
from cover_correlated_replay import SC,a
HERE=Path(__file__).parent;ROOT=HERE.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
ceil=lambda x:-((-x.numerator)//x.denominator)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('archive',nargs='?',type=Path,default=HERE/'cover-global-move-epigraph-evidence');args=ap.parse_args();start=time.monotonic()
    headerraw=(args.archive/'manifest.json').read_bytes();header=json.loads(headerraw)
    for p,digest in header['sources'].items():assert sha((ROOT/p).read_bytes())==digest,p
    zipped=(args.archive/header['file']).read_bytes();assert len(zipped)==header['bytes']<4*1024*1024 and sha(zipped)==header['sha256']
    raw=gzip.decompress(zipped);assert sha(raw)==header['uncompressed_sha256'];data=json.loads(raw)
    params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes());bs=params['b_numerators'];sep=123*SC//128
    cn=F(data['source_old_root_target'])*10**10;assert cn.denominator==1;budget=int(cn)*SC-sum(bs)*sep;up=[sep+ceil(F(budget,b)) for b in bs]
    root=[[(j-i)*sep for i,j in a.PAIRS],[min(sum(up[i:j]),(j-i)*sep+ceil(F(budget,min(bs[i:j])))) for i,j in a.PAIRS]]
    assert root==data['source_root'];a.closure_valid(root)
    cases={r['path']:r for r in data['cases']};ancestors={r['path']:r for r in data['ancestors']};descendants={r['path']:r for r in data['old_descendant_branches']}
    assert len(cases)==9 and len(descendants)==110;needed={p[:k] for p in cases for k in range(1,len(p)+1)};todo=[('r',root)];states={};seen=set()
    while todo:
        p,state=todo.pop();seen.add(p)
        if p in cases:states[p]=state;continue
        b=ancestors[p];z=b['axis'];q=b['cut'];assert state[0][z]<q<state[1][z]
        for bit,upper in [('1',False),('0',True)]:
            if p+bit in needed:
                child=a.child(state,z,q,upper);assert child is not None;todo.append((p+bit,child))
    assert seen==needed
    todo=list(states.items());oldseen=set()
    while todo:
        p,state=todo.pop()
        if p not in descendants:continue
        oldseen.add(p);b=descendants[p];z=b['axis'];q=b['cut'];assert state[0][z]<q<state[1][z]
        for bit,upper in [('1',False),('0',True)]:
            if p+bit in descendants:
                child=a.child(state,z,q,upper);assert child is not None;todo.append((p+bit,child))
    assert oldseen==set(descendants)
    previous=json.loads(gzip.decompress((HERE/'cover-global-move-evidence/proof.json.gz').read_bytes()))
    signed={r['path'] for r in previous['cases']};assert signed==set(data['previous_signed_paths'])
    assert not any(p.startswith(q) or q.startswith(p) for p in cases for q in signed)
    assert not(set(cases)&set(data['previous_joint_paths'])) and not(set(descendants)&{r['path'] for r in previous['old_descendant_branches']})
    table=verifier.scalar.ConcaveDifferenceReplay(json.loads((HERE/'cover_newjet.json').read_bytes()));target=int(data['target_numerator']);bounds=steps=nonzero=0;margins=[]
    for p,row in cases.items():
        state=states[p];step=codec.unpack_obbt(state,row['obbt'],target,obbt.shared.w);obbt.verify({**step,'result':None},target,table.scalar)
        bounds+=len(step['certificates']);state=step['new_cell']
        for packed in row['newton']:
            step=codec.unpack_newton(state,packed,obbt.shared.w);state=newton.verify_step(state,step,params,table.scalar);steps+=1
        assert codec.digest(state)==row['cell_sha256'];result=row['move'].copy()
        result['energy_minorant']=codec.unpack_minorant(state,row['energy_minorant'],obbt.shared.w) if row['energy_minorant'] else None
        assert codec.digest(result)==row['move_sha256'];out=verifier.verify(state,result,target,params,table)
        margins.append(int(out['strict_global_move_margin']));nonzero+=out['energy_multiplier_nonzero']
    out={'scope':__doc__,'manifest_sha256':sha(headerraw),'script_sha256':sha(Path(__file__).read_bytes()),'all_passed':True,
      'new_global_move_chains':9,'prior_OBBT_bounds':bounds,'prior_Newton_steps':steps,'nonzero_energy_multiplier_cases':nonzero,
      'new_reconstructed_old_branches_covered':110,'combined_topmost_global_move_chains':24,'combined_old_branches_covered':251,
      'joint7_overlap':0,'minimum_strict_margin':str(min(margins)),'original_large_OBBT_JSON_required':False,'original_41k_snapshot_required':False,
      'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (args.archive/'independent-replay.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
