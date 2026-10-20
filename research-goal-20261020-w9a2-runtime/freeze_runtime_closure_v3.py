"""Authorize only the verified SDK C-export location repair and cache checks."""
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
pkg=ROOT/'research-goal-20261020-w9a2-runtime-closure-v3';manifest=pkg/'prepared-files.json'
assert sha(manifest)=='be1227fe2606b4a8cb22a9bbeecec93fcc39eac10df96a856d804b61b6c70613'
for row in load(manifest)['files']:
    p=pkg/row['path'];assert p.is_relative_to(pkg) and sha(p)==row['sha256']
gate=load(pkg/'gate-template.json');assert gate['authorized'] is False
assert gate['script_sha256']=={'assemble.py':'cc7ca38250d42c74ef25f3d68dabc536d75e3f2c8557fda482375005b29ddaa3',
                              'cache_binding.py':'6b4ff6cde5c64c0d12a37a51728c04a31acc5779ad8d0a4050f09ce52c18edf5'}
for row in gate['metadata_inputs']+gate['candidate_import_source_files']:assert sha(ROOT/row['path'])==row['sha256']
prior=gate['reuse_previous_sdk_archive_check'];p=ROOT/prior['path']
assert sha(p)==prior['sha256'];r=load(p)
assert r['all_selected_members_identical'] and len(r['selected_members'])==13951
assert r['archive_sha256']=='022576004ed8a4fc81ee8d375419064b54d4475931429d989519fd847ee053f6'
oldterminal=ROOT/'tmp/w9a2-20261020/trusted-runtime-closure-v2/terminal.json'
assert load(oldterminal)['exit_code']==1
gate.update(authorized=True,sole_owner='/root',automatic_repairs_or_retries=0,
    previous_sdk_archive_component_accepted=True,
    root_reviewed_prepared_manifest={'path':manifest.relative_to(ROOT).as_posix(),'sha256':sha(manifest)},
    root_reviewed_borrowed_API_scope='Only exact direct C hash exports statically located in official libInit_shared.dll, on caller-owned buffers; no compiler/import/environment/proof main.',
    root_fullcode_reviewed=True,mathematical_source_changes=0,main_round_counter_changes=0,
    previous_actual_session=44009,previous_actual_exit_code=1,
    previous_failure='After actual13951-member official SDK archive PASS, wrong DLL had no lean_byte_array_hash export; zero hash calls before lookup failure. Entire runtime setup did not PASS.',
    source_mutation_prohibited_until_actual_terminal_and_all_pin_recheck=True,
    actual_setup_pass_claimed_before_execution=False)
out=ROOT/'research-goal-20261016/gates/w9a2-runtime-closure-v3-20261020.json'
with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(gate,f,indent=2);f.write('\n')
print(json.dumps({'gate':out.relative_to(ROOT).as_posix(),'sha256':sha(out),'proof_runs_authorized':0}))
