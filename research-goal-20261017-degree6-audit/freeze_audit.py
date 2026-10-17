"""Freeze the completed independent factored degree-six decode; do not rerun it."""
from pathlib import Path
import hashlib,json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent


def row(p):
    b=p.read_bytes()
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}


def main():
    r=json.loads((HERE/'independent-replay.json').read_bytes())
    assert r['source_sha256_start']==r['source_sha256_end']
    dependencies=[]
    for p,h in r['source_sha256_start'].items():
        entry=row(ROOT/p);assert entry['sha256']==h;dependencies.append(entry)
    assert r['block_entries_checked']==96580 and r['old_exact_principal_forms_preserved']==4070
    assert r['unique_plans_checked']==39325 and r['target_references_checked']==1416525
    assert r['all_plan_target_maps_injective'] and r['all_target_and_entry_streams_fully_consumed']
    assert not r['producer_imported'] and not r['expanded_large_Fraction_matrix_created']
    files=[row(p) for p in [HERE/'independent_decode.py',HERE/'independent-replay.json',HERE/'README.md',Path(__file__)]]
    out={'scope':__doc__,'files':files,'dependency_files':dependencies,
         'independent_representation_replay_passed':True,'new_points':0,'solver_calls':0,'Lean_invocations':0,
         'old_exact714_extension_decided':False,'strict_projection_shrink_proved':False,
         'new_exclusion':False,'new_zero_proportion_proven':False}
    p=HERE/'degree6-audit-files.json';raw=(json.dumps(out,indent=2,allow_nan=False)+'\n').encode()
    if p.exists():assert p.read_bytes()==raw,'Frozen file differs; choose a new path.'
    else:p.write_bytes(raw)
    print(json.dumps({'pin':row(p),'receipt':row(HERE/'independent-replay.json'),
                      'retained_files':len(files),'retained_bytes':sum(x['bytes'] for x in files)}))


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
