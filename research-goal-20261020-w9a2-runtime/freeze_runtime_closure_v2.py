"""Root freeze for explicit SDK Lake source-path repair, metadata only."""
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
pkg=ROOT/'research-goal-20261020-w9a2-runtime-closure-v2';manifest=pkg/'prepared-files.json'
assert sha(manifest)=='868fc97c702f8918d7b7fb8506334af7cad3b06050cb017521021ffc26d6b545'
for row in load(manifest)['files']:
    p=pkg/row['path'];assert p.is_relative_to(pkg) and sha(p)==row['sha256']
gate=load(pkg/'gate-template.json');assert gate['authorized'] is False
assert gate['script_sha256']=={'assemble.py':'276107a5c4baecb8e8dccc94e0bd127132ede9cf2b879054c4a1d19da6c30158',
                              'cache_binding.py':'76d5d5add51c61bfa21a7d51bb4ef912dbe1e95a6eac681cc239ffd947c9cd62'}
for row in gate['metadata_inputs']+gate['candidate_import_source_files']:assert sha(ROOT/row['path'])==row['sha256']
gate.update(authorized=True,sole_owner='/root',automatic_repairs_or_retries=0,
    root_reviewed_prepared_manifest={'path':manifest.relative_to(ROOT).as_posix(),'sha256':sha(manifest)},
    root_reviewed_borrowed_API_scope='Only caller-owned constant buffers after official SDK archive member verification; no compiler/import/environment/kernel main.',
    root_fullcode_reviewed=True,mathematical_source_changes=0,main_round_counter_changes=0,
    previous_actual_session=85897,previous_actual_exit_code=1,
    previous_failure='Source-import-closure SDK Lake.Util.Casing path; before SDK archive or borrowed API. Exact original running source preserved in v1/archive-pre-review-v1.',
    actual_setup_pass_claimed_before_execution=False)
out=ROOT/'research-goal-20261016/gates/w9a2-runtime-closure-v2-20261020.json'
with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(gate,f,indent=2);f.write('\n')
print(json.dumps({'gate':out.relative_to(ROOT).as_posix(),'sha256':sha(out),'proof_runs_authorized':0}))
