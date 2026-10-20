"""Root authorizes exactly one reviewed production check, never a PASS."""
from pathlib import Path
from datetime import datetime, timezone
import copy
import hashlib
import json
from fractions import Fraction
ROOT=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text(encoding='utf-8'))
proposal=ROOT/'tmp/w9a2-20261020/fullchain-proposal-v2/gate-proposal.json'
receipt=load(proposal.parent/'assembly-receipt.json')
raw_path=ROOT/'research-goal-20261020-w9a2-fullchain-proposal-v2-evidence/raw-root-tool-result.json'
raw=load(raw_path)
assert raw['exit_code']==0 and raw.get('session_id') in [None,49850]
assert receipt['allow_verification_execution'] is False and receipt['proof_runs']==0
assert receipt['proposal_sha256']==sha(proposal)
gate=copy.deepcopy(load(proposal))
assert gate['allow_verification_execution'] is False and gate['proposal_only'] is True
assert gate['sole_owner']=='/root' and gate['total_budget_seconds']==3200
assert gate['automatic_retries']==gate['automatic_repairs']==0 and gate['cached_user_oleans'] is False
assert gate['frozen_draft']['solution_sha256']=='a517df6aebde6d136f8b83e06c8be10b3413b8430390f52bd47f04e06f0dce26'
assert gate['frozen_draft']['solution_bytes']==1830052
assert gate['runtime']['closure_manifest']['sha256']=='4d295c059a87faad191c34d1c221bbb744f04f98e226c4a5d0d08f3c01c2d67a'
assert gate['runtime']['root_confirmed_setup_terminal_exit_code']==0
assert gate['runtime']['root_reviewed_complete_runtime_closure'] is False
assert gate['runtime']['coreaudit']['mode']=='interpreted' and gate['runtime']['coreaudit']['binary'] is None
assert gate['runner_sha256']=='92cc8dcf3e3c46e76490ba7bfe8d93bc10e331131eaab3b4c3ae500f80ac66a8'
assert not Path(gate['work_directory']).exists()
roots=gate['development_preflight']['observed_printed_axioms']
assert len(roots)==12 and all(set(v)<={'propext','Quot.sound','Classical.choice'} for v in roots.values())
fresh=ROOT/'research-goal-20261020-w9a2-runtime/before-fullchain-start-v2'
body=fresh/'leaderboard.json';fresh_receipt=fresh/'leaderboard-receipt.json'
retrieval=load(fresh_receipt)
assert retrieval['status']==200 and retrieval['sha256']==sha(body)
assert retrieval['bytes']==body.stat().st_size
assert 0 <= (datetime.now(timezone.utc)-datetime.fromisoformat(retrieval['retrievedAt'])).total_seconds() <= 120
records=load(body)['records']
values=[r['exactRational'] for r in records if r['track']=='critical-line' and r['status']=='kernel-verified' and r.get('exactRational')]
value=lambda r:Fraction(int(r['numerator']),int(r['denominator']))
assert max(values,key=value)==gate['expected_current_record']
assert value(gate['score'])>value(gate['expected_current_record'])
# Preserve the completed proposal and its old fresh inputs unchanged. Bind a
# new, still-identical official baseline immediately before production starts.
gate['fresh_record']=dict(receipt_path=str(fresh_receipt),receipt_sha256=sha(fresh_receipt),
    body_path=str(body),body_sha256=sha(body),maximum_age_seconds=900)
gate.update(allow_verification_execution=True,proposal_only=False,
    root_reviewed_at_utc=datetime.now(timezone.utc).isoformat(),
    root_reviewed_disabled_proposal=dict(path=str(proposal),sha256=sha(proposal)),
    root_observed_disabled_assembler=dict(original_session=49850,actual_exit_code=0,
        raw_tool_result=dict(path=str(raw_path),sha256=sha(raw_path))),
    root_fresh_record_refreshed_after_completed_immutable_preflight=True,
    mathematical_source_changes_since_ordinary_proof=0,
    official_submission_authorized_by_user_after_verification=True,
    actual_production_pass_claimed_before_execution=False)
gate['runtime']['root_reviewed_complete_runtime_closure']=True
out=ROOT/'research-goal-20261016/gates/w9a2-fullchain-v2-20261020.json'
with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(gate,f,indent=2);f.write('\n')
print(json.dumps(dict(gate=out.relative_to(ROOT).as_posix(),sha256=sha(out),
    allow_verification_execution=True,total_budget_seconds=3200,production_passed=False)))
