"""Pin the finite and arbitrary-block old-certificate transfer limitation."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent

def row(path):
    raw=path.read_bytes()
    return {'path':str(path.relative_to(ROOT)).replace('\\','/'),
        'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}

def main():
    path=HERE/'window-large-embedding-files.json';assert not path.exists()
    pilot=json.loads((HERE/'window-large-embedding-pilot.json').read_bytes())
    replay=json.loads((HERE/'window-large-embedding-replay.json').read_bytes())
    assert replay['passed'] and replay['arbitrary_larger_block_size'] and replay['mixed_old_ledgers_allowed']
    assert not replay['uses_numerical_solver'] and not pilot['exact_candidate_exceeds_target']
    dependencies={**pilot['inputs_sha256'],**replay['inputs_sha256']}
    for name,digest in dependencies.items():assert row(ROOT/name)['sha256']==digest
    names=['window_large_embedding_pilot.py','window-large-embedding-pilot.json',
        'window_large_embedding_replay.py','window-large-embedding-replay.json',
        'window_large_embedding_note.txt','window_large_embedding_manifest.py']
    package=[row(HERE/name) for name in names];package_paths={r['path'] for r in package}
    dep=[row(ROOT/name) for name in dependencies if str(Path(name)).replace('\\','/') not in package_paths]
    out={'scope':__doc__,'files':package,'dependencies':dep,'finite_columns_verified':25740,
         'arbitrary_larger_block_size':True,'two_old_ledgers_nonnegative_mixtures':True,
         'new_zero_proportion_proven':False,'complete_global_cover':False,'website_submission_ready':False}
    raw=(json.dumps(out,indent=2)+'\n').encode();path.write_bytes(raw)
    print(json.dumps({'manifest_sha256':hashlib.sha256(raw).hexdigest(),'files':len(package),'dependencies':len(dep)}))

if __name__=='__main__':main()
