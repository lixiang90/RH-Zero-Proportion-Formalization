"""Root-reviewed metadata-only setup authorization; no proof/solver/tool main."""
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p): return json.loads(Path(p).read_text(encoding='utf-8'))
pkg=ROOT/'research-goal-20261020-w9a2-runtime-closure-v1'
manifest=pkg/'prepared-files.json'
assert sha(manifest)=='ab5615a50731f84ae92608eafbdce9b2932c5f0e3865384c9e600877bc8a7d4a'
for row in load(manifest)['files']:
    p=pkg/row['path'];assert p.is_relative_to(pkg) and sha(p)==row['sha256'],row['path']
gate=load(pkg/'gate-template.json')
assert gate['authorized'] is False and not gate['allow_compiler_main'] and not gate['allow_export_or_kernel_main']
assert gate['script_sha256']=={'assemble.py':'2133f9b96d711032549b03eeafa5d52508eca1fd3cbddada15b3ee674aa3c306',
                              'cache_binding.py':'76d5d5add51c61bfa21a7d51bb4ef912dbe1e95a6eac681cc239ffd947c9cd62'}
for row in gate['metadata_inputs']+gate['candidate_import_source_files']:
    assert sha(ROOT/row['path'])==row['sha256'],row['path']
gate.update(authorized=True,sole_owner='/root',automatic_repairs_or_retries=0,
    root_reviewed_prepared_manifest={'path':manifest.relative_to(ROOT).as_posix(),'sha256':sha(manifest)},
    root_reviewed_borrowed_API_scope='Only lean_string_hash and lean_byte_array_hash on caller-owned buffers, after actual SDK DLL and lean.h match the fixed official archive. No Lean environment, imports, compiler main, exporter, kernel replay or solver.',
    root_reviewed_data_scope='Read fixed source/cache provenance and prepare fresh clean trusted data overlays; no candidate olean or old ChallengeDeps copied.',
    mathematical_source_changes=0,main_round_counter_changes=0,
    root_fullcode_reviewed=True,
    actual_setup_pass_claimed_before_execution=False)
out=ROOT/'research-goal-20261016/gates/w9a2-runtime-closure-v1-20261020.json'
with out.open('x',encoding='utf-8',newline='\n') as f:
    json.dump(gate,f,indent=2);f.write('\n')
print(json.dumps({'gate':out.relative_to(ROOT).as_posix(),'sha256':sha(out),'proof_runs_authorized':0}))
