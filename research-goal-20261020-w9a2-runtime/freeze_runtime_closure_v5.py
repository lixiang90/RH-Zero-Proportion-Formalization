"""Authorize reviewed modern/legacy metadata coverage, not a proof run."""
from pathlib import Path
import hashlib
import json
ROOT=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def manifest(p,expected):
    assert sha(p)==expected
    for r in load(p)['files']:
        target=(p.parent/r['path']).resolve()
        assert target.is_relative_to(p.parent) and sha(target)==r['sha256']
        assert target.stat().st_size==r['bytes']
pkg=ROOT/'research-goal-20261020-w9a2-runtime-closure-v5'
prep=pkg/'prepared-files.json'
manifest(prep,'6409c13165eee868c41af4030a77a902efa465198181c2a334bb2fe765a37930')
review=ROOT/'research-goal-20261020-w9a2-verification-independent/modern-zeta-source-review/files.json'
manifest(review,'de0c72420e4075b37995d7399a3252fe1d566ecda5f0b0a5bf74079869093ac2')
gate=load(pkg/'gate-template.json');assert gate['authorized'] is False
assert gate['script_sha256']=={
    'assemble.py':'b284373e8e7856ba2541f2f2e1ab9801b51ea78e5754165f55256b066743c36e',
    'cache_binding.py':'a767f49ebb83f2e75b9a7fa0f11fcfddc671ff18de92afa0215103ca1403fc85'}
for r in gate['metadata_inputs']+gate['candidate_import_source_files']:assert sha(ROOT/r['path'])==r['sha256']
prior=gate['reuse_previous_sdk_archive_check'];r=load(ROOT/prior['path'])
assert sha(ROOT/prior['path'])==prior['sha256']=='805ca515a55710e13378061d0a7c09d3797221aa4d6edc1d99d75e2175300fe3'
assert r['all_selected_members_identical'] and len(r['selected_members'])==13951
assert load(ROOT/'tmp/w9a2-20261020/trusted-runtime-closure-v4/terminal.json')['exit_code']==1
gate.update(authorized=True,sole_owner='/root',automatic_repairs_or_retries=0,
    previous_sdk_archive_component_accepted=True,root_fullcode_reviewed=True,
    root_reviewed_prepared_manifest=dict(path=prep.relative_to(ROOT).as_posix(),sha256=sha(prep)),
    independent_modern_and_legacy_trace_review=dict(path=review.relative_to(ROOT).as_posix(),sha256=sha(review)),
    previous_actual_session=89749,previous_actual_exit_code=1,
    previous_failure='Legacy-only checker rejected the one modern Zeta module; complete four-facet trace rules reviewed on all140 modules before execution.',
    root_actual_escalated_UNC_checks=dict(files=17,matching_sha256=17,tool_chunk='4f3122',proof_runs=0),
    mathematical_source_changes=0,main_round_counter_changes=0,
    source_mutation_prohibited_until_actual_terminal_and_all_pin_recheck=True,
    actual_setup_pass_claimed_before_execution=False)
out=ROOT/'research-goal-20261016/gates/w9a2-runtime-closure-v5-20261020.json'
with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(gate,f,indent=2);f.write('\n')
print(json.dumps(dict(gate=out.relative_to(ROOT).as_posix(),sha256=sha(out),proof_runs_authorized=0)))
