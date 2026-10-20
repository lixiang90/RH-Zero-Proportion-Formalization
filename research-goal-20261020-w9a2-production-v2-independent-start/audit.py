"""Read JSON/source/hash bindings only. Never imports or runs project helpers."""
from datetime import datetime,timezone
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
seen={}
def path(value):
    p=Path(value);return p if p.is_absolute() else ROOT/p
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def pin(p):
    p=path(p);row=dict(path=str(p),resolved_path=str(p.resolve()),bytes=p.stat().st_size,sha256=sha(p))
    if str(p) in seen:assert seen[str(p)]==row
    seen[str(p)]=row;return row
def bind(row):
    p=path(row['path']);actual=pin(p);assert actual['sha256']==row['sha256'],str(p)
    if 'bytes' in row:assert actual['bytes']==row['bytes'],str(p)
    if 'resolved_path' in row:assert actual['resolved_path']==row['resolved_path'],str(p)
    return p
def load(p):p=path(p);pin(p);return json.loads(p.read_text(encoding='utf-8'))
def rational(x):return Fraction(int(x['numerator']),int(x['denominator']))

gatepath=ROOT/'research-goal-20261016/gates/w9a2-fullchain-v2-20261020.json'
gate=load(gatepath);assert sha(gatepath)=='3ebcc3b75ee2a75775281a2a0e9321f7610baddcab5965fcf002fd51e2d763fd'
assert gate['allow_verification_execution'] is True and gate['proposal_only'] is False and gate['sole_owner']=='/root'
assert gate['total_budget_seconds']==3200 and gate['automatic_retries']==gate['automatic_repairs']==0
assert gate['cached_user_oleans'] is False and gate['production_candidate_oleans_reused'] is False
runner=ROOT/'research-goal-20261020-w9a2-verification-preparation-v1/run_verification.py'
assert pin(runner)['sha256']==gate['runner_sha256']=='92cc8dcf3e3c46e76490ba7bfe8d93bc10e331131eaab3b4c3ae500f80ac66a8'
bound=load(bind(gate['prepared_manifest']));assert len(bound['files'])==262
for row in bound['files']:bind(row)
proposal=load(bind(gate['root_reviewed_disabled_proposal']))
assert proposal['allow_verification_execution'] is False and proposal['proposal_only'] is True
assert proposal['runtime']['root_reviewed_complete_runtime_closure'] is False
assembly=load(ROOT/'tmp/w9a2-20261020/fullchain-proposal-v2/assembly-receipt.json')
assert assembly['assembler_pid']==34720 and assembly['allow_verification_execution'] is False
assert assembly['proof_runs']==0 and assembly['source_body_generated_or_copied'] is False
assert assembly['proposal_sha256']==sha(path(gate['root_reviewed_disabled_proposal']['path']))
assert assembly['bound_manifest_sha256']==gate['prepared_manifest']['sha256']
assembler=ROOT/'research-goal-20261020-w9a2-fullchain-gate-preparation-v1/assemble_gate.py'
assert pin(assembler)['sha256']==assembly['assembler_sha256']
outer=gate['root_observed_disabled_assembler'];assert outer['original_session']==49850 and outer['actual_exit_code']==0
raw=load(bind(outer['raw_tool_result']));assert raw['exit_code']==0
rawbody=json.loads(raw['output']);assert rawbody['proposal_sha256']==assembly['proposal_sha256']
assert rawbody['allow_verification_execution'] is False and rawbody['proof_runs']==0
archive=load(ROOT/'research-goal-20261020-w9a2-fullchain-proposal-v2-evidence/files.json')
assert archive['actual_original_session']==49850 and archive['actual_exit_code']==0 and archive['proof_runs']==0
for row in archive['files']:
    bind({**row,'path':str(ROOT/'research-goal-20261020-w9a2-fullchain-proposal-v2-evidence'/row['path'])})

draft=path(gate['frozen_draft']['directory']);draftmanifest=load(draft/'files.json')
assert sha(draft/'files.json')==gate['frozen_draft']['manifest_sha256']
for row in draftmanifest['files']:bind({**row,'path':str(draft/row['path'])})
solution=draft/'Solution.lean';source=solution.read_bytes()
assert len(source)==gate['frozen_draft']['solution_bytes']==1830052<=2000000
assert pin(solution)['sha256']==gate['frozen_draft']['solution_sha256']=='a517df6aebde6d136f8b83e06c8be10b3413b8430390f52bd47f04e06f0dce26'
oldsource=ROOT/'tmp/w9a2-20261020/fullchain-v1/source/Solution/Candidate.lean';pin(oldsource)
original=oldsource.read_bytes();mark=b'/- BEGIN FLATTENED MODULE StructuralW9A220261020.Counting -/'
finish=b'/- BEGIN FLATTENED MODULE StructuralW9A220261020.Final -/'
def split(value):
    i=value.index(mark);j=value.index(finish);return value[:i],value[i:j],value[j:]
a,b,c=split(source);oa,ob,oc=split(original)
assert a==oa and c==oc and b.replace(b'Zeta23Ext.Bridge.wfun',b'wfun')==ob
assert b.count(b'Zeta23Ext.Bridge.wfun')==3 and len(source)-len(original)==51
plan=load(draft/'candidate-parameters.json')
assert plan['score']==gate['score'] and plan['solution_sha256']==sha(solution)
assert rational(gate['score'])>rational(gate['expected_current_record'])
assert gate['mathematical_source_changes_since_ordinary_proof']==0
roots=gate['development_preflight']['observed_printed_axioms'];allowed={'propext','Classical.choice','Quot.sound'}
assert len(roots)==12 and all(set(ax)<=allowed for ax in roots.values())
ordinary=load(ROOT/'tmp/w9a2-20261020/candidate-ordinary-v6/terminal.json')
ostart=load(ROOT/'tmp/w9a2-20261020/candidate-ordinary-v6/started.json')
assert ordinary['passed'] is True and ordinary['modules_completed']==2 and ostart['pid']==50232

runtime=gate['runtime'];closurepath=bind(runtime['closure_manifest'])
# Only the small top-level fields before the very large files table are parsed.
# The complete closure bytes are hash-bound above; its runtime files are being
# checked by the sole running frozen runner, not walked again by this review.
with closurepath.open('r',encoding='utf-8') as f:prefix=f.read(131072)
cut=prefix.index('\n  "files": [')
closure=json.loads(prefix[:cut]+'\n  "files": []\n}')
assert closure['complete_source_bound_runtime_closure_verified'] is True
assert closure['user_proofs_compiled_or_reused_in_setup'] is False and closure['official_runtime_equivalence_claimed'] is False
assert runtime['root_confirmed_setup_terminal_exit_code']==0 and runtime['root_reviewed_complete_runtime_closure'] is True
setup=load(bind(closure['trusted_setup_receipt']));assert setup['assembler_pid']==40712
assert setup['source_and_data_checks_passed'] is True and setup['proof_runs']==0
assert setup['user_proofs_compiled_or_reused_in_setup'] is False
request=load(ROOT/'research-goal-20261020-w9a2-fullchain-request-v2/request.json')
setupouter=load(bind(request['setup_outer_observation']))
assert setupouter['actual_exit_code']==0 and setupouter['parent_pid']==40712 and setupouter['exec_session_id']==35077
assert runtime['package_libs']==closure['candidate_package_libs'] and runtime['interpreted_tool_libs']==closure['interpreted_tool_libs']
for lib in runtime['package_libs']:
    p=path(lib);assert p.is_dir() and p.is_relative_to(path(runtime['package_root']))
    for name in ['ChallengeDeps.olean','ChallengeDeps/CandidateSpec.olean','Challenge/Candidate.olean','Solution/Candidate.olean']+[f'StructuralW9A220261020/{n}.olean' for n in ['Prefix','Core','Graph','Localization','Counting','Final']]:
        assert not (p/name).exists()
tool=path(runtime['interpreted_tool_libs'][0])
assert {p.relative_to(tool).as_posix() for p in tool.rglob('*.olean')}=={'Comparator.olean','Comparator/Axioms.olean','Comparator/Compare.olean','Comparator/Util.olean','Export/Parse.olean'}
fresh=gate['fresh_record'];receipt=load(bind(dict(path=fresh['receipt_path'],sha256=fresh['receipt_sha256'])))
bind(dict(path=fresh['body_path'],sha256=fresh['body_sha256']));assert receipt['status']==200 and receipt['sha256']==fresh['body_sha256']
assert gate['root_fresh_record_refreshed_after_completed_immutable_preflight'] is True

work=path(gate['work_directory']);started=load(work/'started.json')
assert started['pid']==49320 and started['gate_sha256']==sha(gatepath)
assert started['monotonic_t0']==11264.218 and started['budget_seconds']==3200
generation=None
if (work/'generation.json').is_file():
    generation=load(work/'generation.json')
    assert generation['fresh_source_generation'] is True and generation['cached_user_oleans'] is False
    generated=work/'source/Solution/Candidate.lean';assert pin(generated)['sha256']==sha(solution)
result=dict(scope='Bound plan and startup compliance only; no production PASS claim',
  read_at_utc=datetime.now(timezone.utc).isoformat(),project_helpers_run=0,compiler_export_kernel_runs=0,
  production_original_session_root_reported=68962,production_started=started,
  disabled_preflight_actual_outer_session=49850,disabled_preflight_pid=34720,disabled_preflight_exit_code=0,
  bound_manifest_entries_rehashed=262,bound_plan_checks='PASS',source_bytes=len(source),source_sha256=sha(solution),
  exact_repair_delta='Only three Bridge.wfun qualifications; 51 bytes added to old flat source',
  ordinary_v6_outer_session_root_reported=51666,ordinary_v6_pid=50232,ordinary_printed_roots=12,
  reused_runtime_scope=closure['reviewed_scope'],runtime_reuse_is_trusted_data_only=True,
  runtime_complete_file_table_rewalked_by_this_review=False,
  generation_observed=generation,production_result='PENDING ORIGINAL ROOT HANDLE',files=list(seen.values()))
with (HERE/'audit.json').open('x',encoding='utf-8',newline='\n') as f:
    json.dump(result,f,indent=2);f.write('\n')
print(json.dumps(dict(bound_plan_checks='PASS',bound_manifest_entries_rehashed=262,source_sha256=sha(solution),generation_observed=generation is not None,production_result='PENDING ORIGINAL ROOT HANDLE')))
