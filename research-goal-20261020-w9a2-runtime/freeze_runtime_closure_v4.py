"""Authorize the one diagnosed metadata type correction; no proof execution."""
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
pkg=ROOT/'research-goal-20261020-w9a2-runtime-closure-v4'
manifest=pkg/'prepared-files.json'
assert sha(manifest)=='6ade9ee950fd62e63caa85f0096cb448318a219ce0b242fce987aa17e23328dc'
for row in load(manifest)['files']:
    p=pkg/row['path'];assert p.resolve().is_relative_to(pkg) and sha(p)==row['sha256']
old=(ROOT/'research-goal-20261020-w9a2-runtime-closure-v3/assemble.py').read_bytes()
new=(pkg/'assemble.py').read_bytes()
before=b'        assert inputs[7]==[\'Package.id?: (some Zeta23)\',f\'{mix(1723,mix(name_hash("Zeta23"),13)):016x}\']'
after=b'        # Lake.Package.id? : Option Lean.PkgId, and Lean.PkgId is String.\n        # Package.origName.toString is hashed here, not the Name itself.\n        assert inputs[7]==[\'Package.id?: (some Zeta23)\',f\'{mix(1723,mix(self.sdk_hash.string("Zeta23"),13)):016x}\']'
assert old.count(before)==1 and old.replace(before,after)==new
assert sha(ROOT/'research-goal-20261020-w9a2-runtime-v3-terminal/files.json')=='3db331acf1b3242042ec86b4fb7e0106301057505c712dba36d0d42f9e1bb367'
gate=load(pkg/'gate-template.json');assert gate['authorized'] is False
assert gate['script_sha256']['assemble.py']=='e4837c7131fe3c5b9533bb8d321b10be23e8ab29d627301294f07fd3fa5f7ac9'
for row in gate['metadata_inputs']+gate['candidate_import_source_files']:assert sha(ROOT/row['path'])==row['sha256']
prior=gate['reuse_previous_sdk_archive_check'];r=load(ROOT/prior['path'])
assert sha(ROOT/prior['path'])==prior['sha256']=='94e6691b32060442a87162acc9ec94d711e69c5231f876e42935db1880f00029'
assert r['all_selected_members_identical'] and len(r['selected_members'])==13951
assert load(ROOT/'tmp/w9a2-20261020/trusted-runtime-closure-v3/terminal.json')['exit_code']==1
gate.update(authorized=True,sole_owner='/root',automatic_repairs_or_retries=0,
    previous_sdk_archive_component_accepted=True,root_fullcode_reviewed=True,
    root_reviewed_prepared_manifest=dict(path=manifest.relative_to(ROOT).as_posix(),sha256=sha(manifest)),
    previous_actual_session=66541,previous_actual_exit_code=1,
    previous_failure='Metadata checker confused Option String package id with Option Name; exact one-leaf correction only.',
    mathematical_source_changes=0,main_round_counter_changes=0,
    source_mutation_prohibited_until_actual_terminal_and_all_pin_recheck=True,
    actual_setup_pass_claimed_before_execution=False)
out=ROOT/'research-goal-20261016/gates/w9a2-runtime-closure-v4-20261020.json'
with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(gate,f,indent=2);f.write('\n')
print(json.dumps(dict(gate=out.relative_to(ROOT).as_posix(),sha256=sha(out),proof_runs_authorized=0)))
