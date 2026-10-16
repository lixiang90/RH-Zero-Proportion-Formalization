"""Independently check cross-reused sparse second-variation certificates."""
from pathlib import Path
import hashlib,json,time
import cover_correlated_curvature_verify as v
HERE=Path(__file__).parent
def main():
    start=time.monotonic();raw=(HERE/'cover-targeted-curvature-crossprobe.json').read_bytes();doc=json.loads(raw)
    first=(HERE/'cover-targeted-quadratic-gradient.json').read_bytes();assert hashlib.sha256(first).hexdigest()==doc['input_sha256']
    source=json.loads(first);snapraw=(HERE/'cover-current-frontier-20261017b.json').read_bytes();assert hashlib.sha256(snapraw).hexdigest()==source['snapshot_sha256']
    states={r['path']:r['state'] for r in json.loads(snapraw)['frontier']};params=json.loads((HERE.parent/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    checker=v.CurvatureReplay(json.loads((HERE/'cover_newjet.json').read_bytes()));rows=[];cases=[]
    for r in doc['rows']:
        if r['result']:
            rows.append({'path':r['path'],**v.verify(states[r['path']],r['result'],params,checker)});cases.append({'path':r['path'],'cell':states[r['path']],'curvature':r['result']})
    out={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'input_sha256':hashlib.sha256(raw).hexdigest(),
      'all_passed':True,'verified':rows,'ancestor_geometry_replayed':False,'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (HERE/'cover-targeted-curvature-cross-replay.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    (HERE/'cover-targeted-curvature-evidence/cross-extension.json').write_text(json.dumps({'scope':__doc__,'source_sha256':hashlib.sha256(raw).hexdigest(),
      'base_manifest_sha256':hashlib.sha256((HERE/'cover-targeted-curvature-evidence/manifest.json').read_bytes()).hexdigest(),'cases':cases,
      'complete_global_cover':False,'new_zero_proportion_proven':False},separators=(',',':'))+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)
if __name__=='__main__':main()
