"""Replay prior refinements, every mixed global-cut bound, and final leaves."""
from pathlib import Path
import argparse,hashlib,json,time
import cover_global_cut_hypograph_verify as cut
import cover_integer_move_concave_verify as scalar
import cover_sublevel_obbt_verify as obbt
import cover_sublevel_verify as energy
import cover_contractor_verify as newton
import cover_correlated_verify as directional
HERE=Path(__file__).parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-global-cut-hypograph.json')
    ap.add_argument('--output',type=Path,default=HERE/'cover-global-cut-hypograph-replay.json');args=ap.parse_args();start=time.monotonic()
    raw=args.input.read_bytes();doc=json.loads(raw);sourcepath=HERE/doc['receipt']['input_name'];sourcebytes=sourcepath.read_bytes();source=json.loads(sourcebytes)
    assert hashlib.sha256(sourcebytes).hexdigest()==doc['receipt']['input_sha256'];frontier=doc['receipt']['input_kind']=='frontier'
    params=json.loads((HERE.parent/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    table=(HERE/'cover_newjet.json').read_bytes();assert hashlib.sha256(table).hexdigest()=='f64ecdfb3972dd3421fe68394662f2f6d288798ab77d82b081053881ef56719c'
    checker=scalar.ConcaveDifferenceReplay(json.loads(table));target=int(doc['receipt']['target_numerator'])
    lookup={r['path']:r for r in source['rows' if frontier else 'contractions']}
    if frontier:
        before=(HERE/'cover-current-frontier-20261017.json').read_bytes();assert hashlib.sha256(before).hexdigest()==source['receipt']['input_sha256']
        original={r['path']:r for r in json.loads(before)['frontier']}
    else:
        before=(HERE/'cover-sublevel-obbt.json').read_bytes();assert hashlib.sha256(before).hexdigest()==source['receipt']['input_sha256']
        original={r['path']:r for r in json.loads(before)['contractions']}
    counts={'paths':0,'prior_OBBT_bounds':0,'prior_Newton_steps':0,'cut_steps':0,'bounds':0,'bounds_using_global_moves':0,'closed':0};seen=set()
    for row in doc['rows']:
        path=row['path'];assert path not in seen;seen.add(path);prior=lookup[path];first=original[path]
        if frontier:
            step=prior['prior_OBBT'];state=first['state'];assert step['old_cell']==state
            if step['certificates']:obbt.verify({**step,'result':None},target,checker.scalar);counts['prior_OBBT_bounds']+=len(step['certificates']);state=step['new_cell']
            else:assert step['new_cell']==state
            nsteps=prior['prior_Newton']
        else:
            assert first['result'] is None;obbt.verify(first,target,checker.scalar);counts['prior_OBBT_bounds']+=len(first['certificates']);state=first['new_cell'];nsteps=prior['prior_newton_steps']
        for step in nsteps:state=newton.verify_step(state,step,params,checker.scalar);counts['prior_Newton_steps']+=1
        assert state==row['cell']
        for step in row['steps']:
            assert state is not None;state=cut.verify_step(state,step,target,params,checker);counts['cut_steps']+=1
            counts['bounds']+=len(step['certificates']);counts['bounds_using_global_moves']+=sum(bool(c['move_models']) for c in step['certificates'])
        result=row['result']
        if result:
            if result['kind']=='empty':assert state is None
            elif result['kind']=='stationary':directional.verify(state,result['result'],params,checker.scalar)
            else:
                assert result['kind']=='value';_,_,floor=energy.minorant(state,result['result']['certificate']);assert floor==int(result['result']['floor_numerator']) and floor>=target
            counts['closed']+=1
        counts['paths']+=1
        if counts['paths']%5==0:print(json.dumps({**counts,'seconds':time.monotonic()-start}),flush=True)
    assert all(counts[k]==doc['receipt']['counts'][k] for k in ['paths','bounds','bounds_using_global_moves','closed'])
    out={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'all_passed':True,'counts':counts,'full_tree_ancestry_replayed':False,'preserves_original_global_minima_below_target':True,
      'preserves_all_KKT_points':False,'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,
      'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
