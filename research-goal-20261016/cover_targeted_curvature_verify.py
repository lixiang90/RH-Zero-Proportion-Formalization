"""Independent exact replay of targeted whole-cell negative curvatures."""
from pathlib import Path
import hashlib,json,time
import cover_correlated_curvature_verify as v
HERE=Path(__file__).parent
def main():
    start=time.monotonic();raw=(HERE/'cover-targeted-quadratic-gradient.json').read_bytes();doc=json.loads(raw)
    snap=(HERE/'cover-current-frontier-20261017b.json').read_bytes();assert hashlib.sha256(snap).hexdigest()==doc['snapshot_sha256']
    lookup={r['path']:r['state'] for r in json.loads(snap)['frontier']}
    params=json.loads((HERE.parent/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    checker=v.CurvatureReplay(json.loads((HERE/'cover_newjet.json').read_bytes()));rows=[]
    for r in doc['results']:
        if r['uniform_negative_curvature_certificate']:
            rows.append({'path':r['path'],**v.verify(lookup[r['path']],r['uniform_negative_curvature_certificate'],params,checker)})
    out={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'input_sha256':hashlib.sha256(raw).hexdigest(),
      'all_passed':True,'verified':rows,'ancestor_geometry_replayed':False,'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (HERE/'cover-targeted-curvature-replay.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
