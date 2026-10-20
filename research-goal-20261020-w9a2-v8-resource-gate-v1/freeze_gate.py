"""Root-only small-file gate freeze; this does not execute the resource runner."""
from pathlib import Path
import argparse
import hashlib
import json

root = Path(__file__).resolve().parents[1]
here = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--incremental-review-sha256', required=True)
args = parser.parse_args()
def digest(b):
    return hashlib.sha256(b).hexdigest()
def pin(name, expected):
    p = root / name
    raw = p.read_bytes()
    assert digest(raw) == expected, name
    return {'path':name,'bytes':len(raw),'sha256':expected}
pins = [
 pin('research-goal-20261016/macro-reviews/010-20261020.zh.md','979a3a33f9ecee2716284c7cdd6e9301ebc1b4ca0ea7e456809289eada7c249c'),
 pin('research-goal-20261020-w9a2-delivery/draft-v8/files.json','7f449697314ee04088f1874a6cfdd609c02bb322995feb1197406133ded2a776'),
 pin('research-goal-20261020-w9a2-v8-independent-static/files.json','dc3adb86ab1c16e4b0ba39135c924c9a01e390b98b8e909dd318bd24d27ceacf'),
 pin('research-goal-20261020-w9a2-v8-resource-preparation/files.json','8bc3c83af29405e6a87b2fcd2d1cc8f91a2b19487fc2758f2d6e02c578fdc6b5'),
 pin('research-goal-20261020-w9a2-v8-resource-preparation-v2/files.json','787a7c690834f6bece9070a7ddb61ae14ce4fe3bf8f221ed891953033753d2e5'),
 pin('research-goal-20261020-w9a2-v8-resource-runner-static-review/files.json','fb49dc193ca7bb6b516331c10312c399cebf307af0f670eedcf1266f3c4628c8'),
 pin('research-goal-20261020-w9a2-v8-resource-runner-v2-static-review/files.json',args.incremental_review_sha256),
 pin('research-goal-20261020-w9a2-v8-monitor-api-observation/files.json','d377745478dcd442193f74cfc02e83e0e798ee644155e4ff7df76211b35ed48b'),
]
source = pin('research-goal-20261020-w9a2-delivery/draft-v8/Solution.lean','5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b')
assert source['bytes'] == 1829382
runner = pin('research-goal-20261020-w9a2-v8-resource-preparation-v2/run_resource.py','0f9b38cbe7e1591048431975f66613803e7131b95fa7bc8ddeb848b6de09b662')
for row in pins:
    p = root / row['path']
    if p.name == 'files.json':
        for item in json.loads(p.read_bytes())['files']:
            f = root / item['path'] if item['path'].startswith(p.parent.relative_to(root).as_posix()+'/') else p.parent/item['path']
            raw = f.read_bytes()
            assert len(raw)==item['bytes'] and digest(raw)==item['sha256'],str(f)
raw_path = here/'root-process-observation.raw.json'
observed = json.loads(raw_path.read_text(encoding='utf-8-sig'))
assert observed['ProjectLean433ProcessCount']==0 and observed['Lean433ProcessCount']==0
ownership = {'schema':'root-v8-current-project-process-ownership-v1',
 'observed_at_UTC':observed['ObservedUTC'],
 'sole_owner':'/root','scope':'this W9A2 workspace/Lean4.33 pipeline only',
 'no_other_W9A2_compiler_processes':True,
 'Lean433ProcessCount':observed['Lean433ProcessCount'],
 'ProjectLean433ProcessCount':observed['ProjectLean433ProcessCount'],
 'otherLeanCount':observed['OtherLeanProcessCount'],
 'allLeanProcessCount':observed['LeanProcessCount'],
 'lookup_method':'Actual root Get-CimInstance Win32_Process read-only result; unrelated process command lines were not emitted',
 'whole_machine_idle_or_exclusive_claimed':False,
 'other_processes_terminated':False}
ownership_path=here/'root-ownership-observation.json'
assert not ownership_path.exists()
ownership_path.write_bytes((json.dumps(ownership,indent=2)+'\n').encode())
template=root/'research-goal-20261020-w9a2-v8-resource-preparation-v2/gate-template.json'
gate=json.loads(template.read_bytes())
assert gate['allow_compiler_execution'] is False and gate['proposal_only'] is True
gate.update({'allow_compiler_execution':True,'proposal_only':False,
 'runner_sha256':runner['sha256'],'root_authorized_narrow_historical_cache_reuse':True,
 'root_ownership_observation':{'path':ownership_path.relative_to(root).as_posix(),'bytes':ownership_path.stat().st_size,'sha256':digest(ownership_path.read_bytes())},
 'root_review_evidence':pins,
 'resource_gate_scope_clarification':'Ordinary Lean elaboration includes inherent kernel type checking. This gate runs no separate Comparator/CoreAudit/default-kernel replay, exporter or nanoda. Its Windows own-child resource bounds do not establish Linux whole-pipeline equivalence.',
 'v2_necessary_repairs':'Exact runner hash remembered and rechecked after compilation; process ownership explicitly concerns this W9A2/Lean4.33 pipeline, with other Lean processes counted and preserved.',
 'source_checkpoint_commit_prefix':'f2b6d83','new_numerical_family':False})
work=root/gate['work_directory']
assert not work.exists() and not work.with_suffix('.owner.json').exists()
state=json.loads((root/'research-goal-20261016/direction-state.json').read_text(encoding='utf-8'))
assert state['last_review_number']==10 and state['main_rounds_since_review']==0
out=here/'gate.json'
assert not out.exists()
out.write_bytes((json.dumps(gate,ensure_ascii=False,indent=2)+'\n').encode())
print(json.dumps({'gate_sha256':digest(out.read_bytes()),'runner_sha256':runner['sha256'],'source_sha256':source['sha256'],'root_ownership':ownership}))
