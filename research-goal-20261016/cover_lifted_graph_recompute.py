"""Recompute frozen graph8/64 results into a new caller-selected output file."""
from pathlib import Path
import argparse,gzip,hashlib,json,time
import cover_lifted_graph_probe as engine
HERE=Path(__file__).parent;ROOT=HERE.parent
sha=lambda b:hashlib.sha256(b).hexdigest()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--sample',type=int,choices=[8,64],default=64);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    protected={p.resolve() for p in HERE.glob('cover-lifted-graph*.json')};assert args.output.resolve() not in protected,'choose a fresh output path'
    start=time.monotonic();packed=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes();source=json.loads(gzip.decompress(packed))
    selection=json.loads((HERE/'cover-lifted-graph-selection8.json').read_bytes());assert sha(packed)==selection['parent64_input_gzip_sha256']
    cases={r['path']:r for r in source['cases']};paths=selection['selected_paths'] if args.sample==8 else list(cases)
    expected=json.loads((HERE/f'cover-lifted-graph{args.sample}.json').read_bytes());known={r['path']:r for r in expected['rows']}
    assert set(paths)==set(known);oracle=engine.context.curvature.first.TaylorOracle(HERE/'cover_newjet.json');graph=engine.GraphOracle(HERE/'cover_newjet.json')
    rows=[];closed=0
    for path in paths:
        state=tuple(cases[path]['before']);baseline,bs,_=engine.solve(state,oracle,graph,False);result,stats,_=engine.solve(state,oracle,graph,True)
        assert baseline==known[path]['baseline'] and result==known[path]['graph'],path;closed+=bool(result)
        rows.append({'path':path,'baseline':baseline,'graph':result,'baseline_statistics':bs,'graph_statistics':stats})
    out={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'parent64_input_gzip_sha256':sha(packed),'sample':args.sample,'cases':len(paths),
      'all_original_certificates_reproduced':True,'strict_graph_certificates':closed,'rows':rows,
      'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='rows'}),flush=True)
if __name__=='__main__':main()
