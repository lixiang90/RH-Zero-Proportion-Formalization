"""Fill a new production preflight request from actual completed evidence only."""
from pathlib import Path
import argparse
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser()
ap.add_argument('--draft',required=True)
ap.add_argument('--runtime',required=True)
ap.add_argument('--outer',required=True)
ap.add_argument('--fresh',required=True)
ap.add_argument('--output',required=True)
args=ap.parse_args()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text(encoding='utf-8'))
def path(s):
    p=(ROOT/s).resolve();assert p.is_relative_to(ROOT);return p
def row(p):return dict(path=p.relative_to(ROOT).as_posix(),bytes=p.stat().st_size,sha256=sha(p))
template=ROOT/'research-goal-20261020-w9a2-fullchain-request-preparation/request-proposal.json'
assert sha(template)=='02ec0bc362f17cd5f6a7fe53516f4d20306770bc1f20d4b31958b5fd66f88ff9'
request=load(template)
draft=path(args.draft);runtime=path(args.runtime);outer=path(args.outer);fresh=path(args.fresh)
assert draft.parent==ROOT/'research-goal-20261020-w9a2-delivery'
plan=load(draft/'candidate-parameters.json');source=draft/'Solution.lean'
assert sha(source)==plan['solution_sha256'] and source.stat().st_size==plan['solution_bytes']
request['frozen_draft']=dict(directory=draft.relative_to(ROOT).as_posix(),
    manifest_sha256=sha(draft/'files.json'),solution_bytes=source.stat().st_size,solution_sha256=sha(source))
closure=load(runtime/'closure.json');terminal=load(runtime/'terminal.json');observation=load(outer)
assert terminal['exit_code']==observation['actual_exit_code']==0
assert terminal['assembler_pid']==observation['parent_pid']
assert observation['observed_scope']=='completed-outer-parent-handle'
assert load(path(observation['raw_tool_terminal']['path']))['exit_code']==0
assert closure['complete_source_bound_runtime_closure_verified']
assert closure['user_proofs_compiled_or_reused_in_setup'] is False
request['runtime_closure']=row(runtime/'closure.json')
request['setup_runner']=observation['runner']
request['setup_outer_observation']=row(outer)
stage=request['ordinary_stages'][1]
assert stage['gate']['sha256']=='92def59e80c77b461e3cc301bff748f65e44d53b4c031d745098b156882a3bc5'
stage['gate']['path']='research-goal-20261016/gates/w9a2-ordinary-v1b-20261020.json'
assert sha(path(stage['gate']['path']))==stage['gate']['sha256']
request['fresh_record']=dict(receipt=row(fresh/'leaderboard-receipt.json'),
    body=row(fresh/'leaderboard.json'),maximum_age_seconds=900)
request['proposal_directory']='tmp/w9a2-20261020/fullchain-proposal-v1'
request['production_work_directory']='tmp/w9a2-20261020/fullchain-v1'
assert not path(request['proposal_directory']).exists() and not path(request['production_work_directory']).exists()
out=path(args.output);out.parent.mkdir(parents=True,exist_ok=True)
with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(request,f,indent=2);f.write('\n')
print(json.dumps(dict(path=out.relative_to(ROOT).as_posix(),sha256=sha(out),proof_runs=0,
    allow_verification_execution=False,solution_sha256=sha(source))))
