"""Archive a self-contained partial compact cover and its independent receipt."""
from pathlib import Path
import argparse,gzip,hashlib,json
HERE=Path(__file__).parent;ROOT=HERE.parent
sha=lambda raw:hashlib.sha256(raw).hexdigest()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'window-compact-obbt-resume-pilot.json')
    ap.add_argument('--receipt',type=Path,default=HERE/'window-compact-obbt-resume-pilot-replay.json')
    ap.add_argument('--archive',type=Path,default=HERE/'cover-compact-runtime-evidence');args=ap.parse_args()
    raw=args.input.read_bytes();data=json.loads(raw);receipt_raw=args.receipt.read_bytes();receipt=json.loads(receipt_raw)
    assert receipt['input_sha256']==sha(raw) and receipt['checked_nodes']==data['checked']
    assert not receipt['complete_finite_minimizer_partition'] and not receipt['new_zero_proportion_proven']
    zipped=gzip.compress(raw,compresslevel=9,mtime=0);assert len(zipped)<4*1024*1024
    args.archive.mkdir(exist_ok=True);(args.archive/'pilot.json.gz').write_bytes(zipped)
    (args.archive/'discovery-replay.json').write_bytes(receipt_raw)
    files=['cover_compact_codec.py','window_compact_obbt_replay.py','cover_flow_basis.py','cover_contractor_verify.py',
      'cover_sublevel_obbt_verify_api.py','cover_sublevel_obbt_verify.py','cover_sublevel_verify.py','cover_correlated_verify.py',
      'cover_correlated_replay.py','cover_gram_basin_api.py','cover_compact_runtime_archive_replay.py']
    pins={name.replace('\\','/'):digest for name,digest in data['input_sha256'].items()}
    for name in files:
        p=HERE/name;pins[str(p.relative_to(ROOT)).replace('\\','/')]=sha(p.read_bytes())
    for name,digest in pins.items():assert sha((ROOT/name).read_bytes())==digest,name
    out={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'sources':pins,
      'file':'pilot.json.gz','bytes':len(zipped),'sha256':sha(zipped),'uncompressed_bytes':len(raw),'uncompressed_sha256':sha(raw),
      'discovery_replay_sha256':sha(receipt_raw),'checked_nodes':data['checked'],'frontier':data['unresolved_count'],
      'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False,
      'website_size_limit_passed':False}
    (args.archive/'manifest.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out))
if __name__=='__main__':main()
