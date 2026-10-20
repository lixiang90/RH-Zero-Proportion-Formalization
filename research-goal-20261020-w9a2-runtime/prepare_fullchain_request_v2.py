"""Prepare a disabled v2 request after the qualification-only repair passes."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text(encoding='utf-8'))
def pin(p):return dict(path=p.relative_to(ROOT).as_posix(),bytes=p.stat().st_size,sha256=sha(p))
old=ROOT/'research-goal-20261020-w9a2-fullchain-request-v1/request.json'
assert sha(old)=='fa646c7a107de89619bd5ce42c323107d3f5409eec82d44a6844c158f65bdac1'
request=load(old);draft=ROOT/'research-goal-20261020-w9a2-delivery/draft-v6'
plan=load(draft/'candidate-parameters.json');source=draft/'Solution.lean'
assert sha(source)==plan['solution_sha256'] and source.stat().st_size==plan['solution_bytes']==1830052
assert plan['source_modules'][3]['sha256']==sha(ROOT/'research-goal-20261020-w9a2-counting-repair-v1/StructuralW9A220261020/Counting.lean')
request['frozen_draft']=dict(directory=draft.relative_to(ROOT).as_posix(),manifest_sha256=sha(draft/'files.json'),solution_bytes=source.stat().st_size,solution_sha256=sha(source))
archive=ROOT/'research-goal-20261020-w9a2-ordinary-v6-terminal'
assert load(archive/'terminal.json')['passed'] and load(archive/'root-parent-exit-attestation.json')['actual_parent_exit_code']==0
request['ordinary_stages'].append(dict(gate=pin(ROOT/'research-goal-20261016/gates/w9a2-ordinary-v6-20261020.json'),archive_manifest=pin(archive/'files.json'),archived_job_directory=archive.relative_to(ROOT).as_posix(),root_attestation=pin(archive/'root-parent-exit-attestation.json')))
assert len(request['ordinary_stages'])==7
for r in request['selected_development_modules']:
    if r['module'].split('.')[-1] in ['Counting','Final']:r['stage_index']=6
fresh=ROOT/'research-goal-20261020-w9a2-runtime/before-production-v2'
request['fresh_record']=dict(receipt=pin(fresh/'leaderboard-receipt.json'),body=pin(fresh/'leaderboard.json'),maximum_age_seconds=900)
request['proposal_directory']='tmp/w9a2-20261020/fullchain-proposal-v2'
request['production_work_directory']='tmp/w9a2-20261020/fullchain-v2'
assert not (ROOT/request['proposal_directory']).exists() and not (ROOT/request['production_work_directory']).exists()
out=ROOT/'research-goal-20261020-w9a2-fullchain-request-v2/request.json';out.parent.mkdir(exist_ok=False)
with out.open('xb') as f:f.write((json.dumps(request,indent=2)+'\n').encode())
print(json.dumps(dict(path=out.relative_to(ROOT).as_posix(),sha256=sha(out),proof_runs=0,allow_verification_execution=False)))
