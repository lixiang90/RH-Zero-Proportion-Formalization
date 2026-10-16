"""Expand the independently replayed graph8 method to the same frozen parent64."""
from pathlib import Path
import gzip,hashlib,json,time
import cover_lifted_graph_probe as engine
HERE=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()

def main():
    start=time.monotonic();raw=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes();source=json.loads(gzip.decompress(raw))
    engine_raw=Path(engine.__file__).read_bytes();oracle=engine.context.curvature.first.TaylorOracle(HERE/'cover_newjet.json');graph=engine.GraphOracle(HERE/'cover_newjet.json')
    rows=[];counts={'parents':0,'baseline_positive':0,'graph_positive':0,'baseline_exact':0,'graph_exact':0,'extra_exact':0}
    for case in source['cases']:
        state=tuple(case['before']);t=time.monotonic();baseline,bs,blp=engine.solve(state,oracle,graph,False);bt=time.monotonic()-t
        t=time.monotonic();result,gs,glp=engine.solve(state,oracle,graph,True);gt=time.monotonic()-t;counts['parents']+=1
        counts['baseline_positive']+=bool(bs['L1_residual_hint'] and bs['L1_residual_hint']>1e-10);counts['graph_positive']+=bool(gs['L1_residual_hint'] and gs['L1_residual_hint']>1e-10)
        counts['baseline_exact']+=bool(baseline);counts['graph_exact']+=bool(result);counts['extra_exact']+=bool(result and not baseline)
        rows.append({'path':case['path'],'baseline_statistics':bs,'graph_statistics':gs,'baseline':baseline,'graph':result,'baseline_seconds':bt,'graph_seconds':gt})
        if counts['parents']%8==0:print(json.dumps({**counts,'seconds':time.monotonic()-start}),flush=True)
    out={'receipt':{'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'engine_sha256':sha(engine_raw),'input_sha256':sha(raw),
      'selection':'same frozen64 nonnested depth24 parents, discovery-order sample; no new selection',
      'table_sha256':graph.sha,'target':'11/1250','counts':counts,'independent_replay_passed':False,'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start},'rows':rows}
    (HERE/'cover-lifted-graph64.json').write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(out['receipt']),flush=True)
if __name__=='__main__':main()
