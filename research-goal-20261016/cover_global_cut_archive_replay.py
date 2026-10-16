"""Replay compact finite-move hull exclusions without either large old input."""
from pathlib import Path
from fractions import Fraction as F
import argparse,gzip,hashlib,json,time
import cover_compact_codec as c
import cover_global_cut_codec as cc
import cover_global_cut_full_verify as single
import cover_global_cut_hypograph_verify as mixed
import cover_integer_move_concave_verify as scalar
import cover_sublevel_obbt_verify as obbt
import cover_sublevel_verify as energy
import cover_contractor_verify as newton
import cover_correlated_verify as directional
from cover_correlated_replay import SC,a
HERE=Path(__file__).parent;ROOT=HERE.parent
sha=lambda b:hashlib.sha256(b).hexdigest()

def main():
    start=time.monotonic();folder=HERE/'cover-global-cut-union-evidence';headerraw=(folder/'manifest.json').read_bytes();header=json.loads(headerraw)
    for name,digest in header['sources'].items():assert sha((ROOT/name).read_bytes())==digest,name
    packed=(folder/header['file']).read_bytes();assert len(packed)==header['bytes']<4*1024*1024 and sha(packed)==header['sha256']
    raw=gzip.decompress(packed);assert sha(raw)==header['uncompressed_sha256'];doc=json.loads(raw)
    params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes());bs=params['b_numerators'];sep=123*SC//128
    cn=F(doc['source_root_target'])*10**10;assert cn.denominator==1;budget=int(cn)*SC-sum(bs)*sep
    up=[sep+c.ceil(F(budget,b)) for b in bs]
    root=[[(j-i)*sep for i,j in a.PAIRS],[min(sum(up[i:j]),(j-i)*sep+c.ceil(F(budget,min(bs[i:j])))) for i,j in a.PAIRS]]
    assert root==doc['source_root'];a.closure_valid(root)
    cases={r['path']:r for r in doc['cases']};ancestors={r['path']:r for r in doc['ancestors']};descendants={r['path']:r for r in doc['old_descendant_branches']}
    assert len(cases)==header['new_closed_regions']==19 and len(ancestors)==len(doc['ancestors'])
    prior=set(doc['prior_move_paths']);joint=set(doc['prior_joint_paths']);assert len(prior)==24 and len(joint)==7
    assert not any(p.startswith(q) or q.startswith(p) for p in cases for q in prior|joint)
    assert not any(p!=q and p.startswith(q) for p in cases for q in cases)
    needed={p[:k] for p in cases for k in range(1,len(p)+1)};todo=[('r',root)];states={};seen=set()
    while todo:
        p,state=todo.pop();seen.add(p)
        if p in cases:states[p]=state;continue
        b=ancestors[p];z=b['axis'];cut=b['cut'];assert state[0][z]<cut<state[1][z]
        for bit,upper in [('1',False),('0',True)]:
            if p+bit in needed:
                child=a.child(state,z,cut,upper);assert child is not None;todo.append((p+bit,child))
    assert seen==needed and set(states)==set(cases)
    todo=list(states.items());oldseen=set()
    while todo:
        p,state=todo.pop()
        if p not in descendants:continue
        oldseen.add(p);b=descendants[p];z=b['axis'];cut=b['cut'];assert state[0][z]<cut<state[1][z]
        for bit,upper in [('1',False),('0',True)]:
            if p+bit in descendants:
                child=a.child(state,z,cut,upper);assert child is not None;todo.append((p+bit,child))
    assert oldseen==set(descendants) and len(oldseen)==header['new_old_branches_covered']
    checker=scalar.ConcaveDifferenceReplay(json.loads((HERE/'cover_newjet.json').read_bytes()));target=int(doc['target_numerator'])
    counts={'closed':0,'prior_OBBT_bounds':0,'prior_Newton_steps':0,'cut_bounds':0,'new_Newton_steps':0,'intersection_chains':0}
    def cuts(state,rows):
        for packedstep in rows:
            step=cc.unpack_step(state,packedstep,target,params,obbt.shared.w)
            checker_fn=mixed.verify_step if packedstep['kind']=='mixed' else single.verify_step
            state=checker_fn(state,step,target,params,checker);counts['cut_bounds']+=len(step['certificates'])
        return state
    for p,row in cases.items():
        state=states[p];step=c.unpack_obbt(state,row['obbt'],target,obbt.shared.w)
        obbt.verify({**step,'result':None},target,checker.scalar);counts['prior_OBBT_bounds']+=len(step['certificates']);state=step['new_cell']
        for packedstep in row['prior_newton']:
            step=c.unpack_newton(state,packedstep,obbt.shared.w);state=newton.verify_step(state,step,params,checker.scalar);counts['prior_Newton_steps']+=1
        if row['kind']=='single_chain':state=cuts(state,row['cuts'])
        else:
            assert row['kind']=='intersection_chain';s=cuts(state,row['single_cuts']);t=cuts(state,row['mixed_cuts']);assert s is not None and t is not None
            state=newton.close([[max(x,y) for x,y in zip(s[0],t[0])],[min(x,y) for x,y in zip(s[1],t[1])]]);counts['intersection_chains']+=1
            for packedstep in row['newton']:
                step=c.unpack_newton(state,packedstep,obbt.shared.w);state=newton.verify_step(state,step,params,checker.scalar);counts['new_Newton_steps']+=1
        leaf=c.unpack_leaf(state,row['leaf'],obbt.shared.w)
        if leaf['kind'].startswith('empty'):assert state is None
        elif leaf['kind']=='stationary':directional.verify(state,leaf['result'],params,checker.scalar)
        else:
            assert leaf['kind']=='value';_,_,floor=energy.minorant(state,leaf['result']['certificate']);assert floor==int(leaf['result']['floor_numerator']) and floor>=target
        counts['closed']+=1
        print(json.dumps({**counts,'seconds':time.monotonic()-start}),flush=True)
    out={'scope':__doc__,'manifest_sha256':sha(headerraw),'script_sha256':sha(Path(__file__).read_bytes()),'all_passed':True,'counts':counts,
      'ancestor_nodes':len(seen),'reconstructed_old_branches_made_unnecessary':len(oldseen),'combined_topmost_global_regions':43,'joint7_overlap':0,
      'original_large_OBBT_JSON_required':False,'original_41k_snapshot_required':False,'preserves_original_global_minima_below_target':True,
      'preserves_all_KKT_points':False,'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,
      'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (folder/'independent-replay.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
