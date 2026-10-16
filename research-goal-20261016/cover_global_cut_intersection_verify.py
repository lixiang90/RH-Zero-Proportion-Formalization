"""Full arithmetic replay of two valid hull chains, intersection and Newton."""
from pathlib import Path
import hashlib,json,time
import cover_global_cut_full_verify as single
import cover_global_cut_hypograph_verify as mixed
import cover_integer_move_concave_verify as scalar
import cover_sublevel_obbt_verify as obbt
import cover_sublevel_verify as energy
import cover_contractor_verify as newton
import cover_correlated_verify as directional
HERE=Path(__file__).parent

def main():
    start=time.monotonic();path=HERE/'cover-global-cut-intersection.json';raw=path.read_bytes();doc=json.loads(raw);inputs={}
    for name,sha in doc['receipt']['inputs'].items():
        data=(HERE/name).read_bytes();assert hashlib.sha256(data).hexdigest()==sha;inputs[name]=json.loads(data)
    full=inputs['cover-global-cut-full-contractor.json'];hypo=inputs['cover-global-cut-hypograph.json'];fl={r['path']:r for r in full['contractions']};hl={r['path']:r for r in hypo['rows']}
    priorraw=(HERE/'cover-sublevel-obbt.json').read_bytes();assert hashlib.sha256(priorraw).hexdigest()==full['receipt']['input_sha256']
    prior={r['path']:r for r in json.loads(priorraw)['contractions']}
    params=json.loads((HERE.parent/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    tab=(HERE/'cover_newjet.json').read_bytes();assert hashlib.sha256(tab).hexdigest()=='f64ecdfb3972dd3421fe68394662f2f6d288798ab77d82b081053881ef56719c'
    checker=scalar.ConcaveDifferenceReplay(json.loads(tab));target=int(doc['receipt']['target_numerator']);seen=set()
    counts={'paths':0,'prior_OBBT_bounds':0,'prior_Newton_steps':0,'single_bounds':0,'mixed_bounds':0,'new_Newton_steps':0,'closed':0}
    for row in doc['rows']:
        p=row['path'];assert p not in seen;seen.add(p);f=fl[p];h=hl[p];first=prior[p];assert f['result'] is None and h['result'] is None and first['result'] is None
        obbt.verify(first,target,checker.scalar);counts['prior_OBBT_bounds']+=len(first['certificates']);state=first['new_cell']
        for step in f['prior_newton_steps']:state=newton.verify_step(state,step,params,checker.scalar);counts['prior_Newton_steps']+=1
        assert state==f['steps'][0]['old_cell']==h['cell'];s=state;t=state
        for step in f['steps']:s=single.verify_step(s,step,target,params,checker);counts['single_bounds']+=len(step['certificates'])
        for step in h['steps']:t=mixed.verify_step(t,step,target,params,checker);counts['mixed_bounds']+=len(step['certificates'])
        assert s is not None and t is not None
        intersection=[[max(x,y) for x,y in zip(s[0],t[0])],[min(x,y) for x,y in zip(s[1],t[1])]]
        assert intersection==row['intersection_raw'];state=newton.close(intersection)
        for step in row['Newton_steps']:state=newton.verify_step(state,step,params,checker.scalar);counts['new_Newton_steps']+=1
        result=row['result']
        if result:
            if result['kind'] in ['empty_intersection','empty_Newton']:assert state is None
            elif result['kind']=='stationary':directional.verify(state,result['result'],params,checker.scalar)
            else:
                assert result['kind']=='value';_,_,floor=energy.minorant(state,result['result']['certificate']);assert floor==int(result['result']['floor_numerator']) and floor>=target
            counts['closed']+=1
        counts['paths']+=1
        if counts['paths']%5==0:print(json.dumps({**counts,'seconds':time.monotonic()-start}),flush=True)
    assert counts['paths']==doc['receipt']['counts']['remaining_both'] and counts['closed']==doc['receipt']['counts']['closed']
    out={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'all_passed':True,'counts':counts,'preserves_original_global_minima_below_target':True,'preserves_all_KKT_points':False,
      'full_tree_ancestry_replayed':False,'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,
      'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (HERE/'cover-global-cut-intersection-replay.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
