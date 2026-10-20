"""Root-only small-file RSS gate freeze. Does not execute a compiler."""
from pathlib import Path
import argparse
import hashlib
import json

root = Path(__file__).resolve().parents[1]
here = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--preparation-sha256', required=True)
parser.add_argument('--runner-sha256', required=True)
parser.add_argument('--runner-review-sha256', required=True)
args = parser.parse_args()
def digest(raw):
    return hashlib.sha256(raw).hexdigest()
def pin(name, expected):
    p = root/name
    raw = p.read_bytes()
    assert digest(raw) == expected, name
    return {'path':name,'bytes':len(raw),'sha256':expected}
pins = [
 pin('research-goal-20261016/macro-reviews/011-20261020.zh.md','9b12107dcb046c6aa624667c5cf81641e61ec23f5a867dc33c3d42af6c496411'),
 pin('research-goal-20261020-w9a2-v8-resource-failure-v1/files.json','8317a845b841313d4042ae0664a9d38039e96fe05adedee868355636a13a0cf1'),
 pin('research-goal-20261020-w9a2-v8-stack-static-review/files.json','b50f02b52b1f40ffd7df5f408596137b2cc16511169c0cd2a52b08e06f6c4121'),
 pin('research-goal-20261020-w9a2-v8-import-memory-static-independent/files.json','c3db7c1c33ec2fcb6639680032a002f37534dab26076a759d02283b8d0a2e3c7'),
 pin('research-goal-20261020-w9a2-delivery/draft-v8/files.json','7f449697314ee04088f1874a6cfdd609c02bb322995feb1197406133ded2a776'),
 pin('research-goal-20261020-w9a2-v8-independent-static/files.json','dc3adb86ab1c16e4b0ba39135c924c9a01e390b98b8e909dd318bd24d27ceacf'),
 pin('research-goal-20261020-w9a2-v8-resource-preparation-v3/files.json',args.preparation_sha256),
 pin('research-goal-20261020-w9a2-v8-resource-runner-v3-static-review/files.json',args.runner_review_sha256),
]
source = pin('research-goal-20261020-w9a2-delivery/draft-v8/Solution.lean','5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b')
assert source['bytes'] == 1829382
runner = pin('research-goal-20261020-w9a2-v8-resource-preparation-v3/run_resource.py',args.runner_sha256)
for row in pins:
    p = root/row['path']
    if p.name == 'files.json':
        for item in json.loads(p.read_bytes())['files']:
            q = root/item['path'] if item['path'].startswith(p.parent.relative_to(root).as_posix()+'/') else p.parent/item['path']
            raw = q.read_bytes()
            assert len(raw) == item['bytes'] and digest(raw) == item['sha256'], str(q)
raw_path = here/'root-process-observation.raw.json'
observed = json.loads(raw_path.read_text(encoding='utf-8-sig'))
assert observed['ProjectLean433ProcessCount'] == 0 and observed['Lean433ProcessCount'] == 0
assert observed['UnknownExecutablePathCount'] == 0
ownership = {'schema':'root-v8-current-project-process-ownership-v2',
 'observed_at_UTC':observed['ObservedUTC'],'sole_owner':'/root',
 'scope':'this W9A2 workspace/Lean4.33 pipeline only','no_other_W9A2_compiler_processes':True,
 'Lean433ProcessCount':observed['Lean433ProcessCount'],
 'ProjectLean433ProcessCount':observed['ProjectLean433ProcessCount'],
 'otherLeanCount':observed['OtherLeanProcessCount'],
 'allLeanProcessCount':observed['LeanProcessCount'],
 'lookup_method':'Actual root Get-CimInstance Win32_Process read-only result; unrelated command lines were not emitted',
 'whole_machine_idle_or_exclusive_claimed':False,'other_processes_terminated':False}
ownership_path = here/'root-ownership-observation.json'
assert not ownership_path.exists()
ownership_path.write_bytes((json.dumps(ownership,indent=2)+'\n').encode())
template = root/'research-goal-20261020-w9a2-v8-resource-preparation-v3/gate-template.json'
gate = json.loads(template.read_bytes())
assert gate['allow_compiler_execution'] is False and gate['proposal_only'] is True
assert gate['schema'] == 'w9a2-v8-resource-gate-v2'
assert gate['metric'] == 'PeakWorkingSetSize' and gate['commit_diagnostic_only'] is True
assert gate['observed_peak_stop_bytes'] == 7*1024**3 and gate['total_budget_seconds'] == 3200
gate.update({'allow_compiler_execution':True,'proposal_only':False,'runner_sha256':runner['sha256'],
 'root_authorized_narrow_historical_cache_reuse':True,
 'root_ownership_observation':{'path':ownership_path.relative_to(root).as_posix(),'bytes':ownership_path.stat().st_size,'sha256':digest(ownership_path.read_bytes())},
 'root_review_evidence':pins,
 'resource_gate_scope_clarification':'Fixed v8 compiler and C/ilean output only. No old exporter, separate Comparator/CoreAudit/default-kernel replay or nanoda. Ordinary elaboration inherently typechecks declarations. RSS metric is not official Linux whole-pipeline cgroup equivalence.',
 'commit_stop_change':'Macro011 selects working-set diagnosis after exact FILE_MAP_COPY primary evidence; process commit still measured, not compared to Linux resident budget. Old v1 remains a failed own-runner abort.',
 'new_numerical_family':False})
work = root/gate['work_directory']
assert not work.exists() and not work.with_suffix('.owner.json').exists()
state = json.loads((root/'research-goal-20261016/direction-state.json').read_bytes())
assert state['last_review_number'] == 11 and state['main_rounds_since_review'] == 0
out = here/'gate.json'
assert not out.exists()
out.write_bytes((json.dumps(gate,ensure_ascii=False,indent=2)+'\n').encode())
print(json.dumps({'gate_sha256':digest(out.read_bytes()),'runner_sha256':runner['sha256'],
    'source_sha256':source['sha256'],'root_ownership':ownership}))
