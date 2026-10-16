"""Replay a compressed runtime cover without its original uncompressed JSON."""
from pathlib import Path
import argparse,gzip,hashlib,json,time
import window_compact_obbt_replay as verifier
HERE=Path(__file__).parent;ROOT=HERE.parent
sha=lambda raw:hashlib.sha256(raw).hexdigest()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('archive',nargs='?',type=Path,default=HERE/'cover-compact-runtime-evidence');args=ap.parse_args();start=time.monotonic()
    manifest_raw=(args.archive/'manifest.json').read_bytes();manifest=json.loads(manifest_raw)
    for path,digest in manifest['sources'].items():assert sha((ROOT/path).read_bytes())==digest,path
    raw=(args.archive/manifest['file']).read_bytes();assert len(raw)==manifest['bytes']<4*1024*1024 and sha(raw)==manifest['sha256']
    expanded=gzip.decompress(raw);assert len(expanded)==manifest['uncompressed_bytes'] and sha(expanded)==manifest['uncompressed_sha256']
    data=json.loads(expanded)
    # The original Windows checkpoint hashes the same repository files with
    # native separators. Normalize path spelling for cross-platform replay.
    data['input_sha256']={path.replace('\\','/'):digest for path,digest in data['input_sha256'].items()}
    result=verifier.replay(data);assert result['checked_nodes']==manifest['checked_nodes']
    assert result['counts']['frontier']==manifest['frontier'] and not result['complete_finite_minimizer_partition']
    out={'scope':__doc__,'manifest_sha256':sha(manifest_raw),'script_sha256':sha(Path(__file__).read_bytes()),
      'compressed_bytes':len(raw),'original_uncompressed_JSON_required':False,'independent_replay':result,'all_passed':True,
      'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False,
      'website_size_limit_passed':False,'seconds':time.monotonic()-start}
    (args.archive/'independent-replay.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
