from pathlib import Path
import hashlib
import json
from datetime import datetime, timezone

root = Path(__file__).resolve().parents[1]
here = Path(__file__).resolve().parent
pins = {
 'research-goal-20261016/macro-reviews/009-20261020.zh.md': '01eee267729dca524c5fa4ea07b8565ecf3185cf31323d395aee72e9509412ff',
 'research-goal-20261020-w9a2-official-timeout-v1/files.json': 'e9c2443548b40091b5bd319b065c2e65b08e2e384dc40f93c966a85aba337efd',
 'research-goal-20261020-w9a2-static-build-cost-formal/files.json': 'c42347e3222396f65c27d47195696c645013433b67ed583ae008dda24dae6d4b',
 'research-goal-20261020-w9a2-unused-dependency-static/files.json': 'cb17ce3e4b495f484dd36b152b30785cada29275f85cfc0e7ecc7a30b5628efc',
 'research-goal-20261020-w9a2-delivery/draft-v7/files.json': '08844b98778d5197ad39cd6afe0c796f94e1808f04f17a348f18c8f2bd4efab1',
 'research-goal-20261020-w9a2-v7-independent-static/files.json': '1c899d859afaa01f8f422a1dca14cfc61be38f9e9ba6b984cabca5e38300ed4a',
 'research-goal-20261020-w9a2-submission-materials-v7-preparation/files.json': '83c18d0fc19040497d893538abf43d4c7f79f8aae375c8cd32fe00b6ec34f298',
 'submission/w9a2-weighted-potential-20261020-prepared-v7/files.json': '91c5e7c812e92dddfcf9c4d26fe5061c0fd1d8bb8d50aa69aa29c021cfcc724a',
 'submission/w9a2-weighted-potential-20261020-expected-wire-v7/files.json': '6ea94c6f7d2a02ed64de70a4a349ffa210d61e5a77098aec255aef32cc265a46',
}
def sha(raw):
    return hashlib.sha256(raw).hexdigest()
checked = []
for name, digest in pins.items():
    p = root / name
    raw = p.read_bytes()
    assert sha(raw) == digest, name
    checked.append({'path': name, 'bytes': len(raw), 'sha256': digest})
    if p.name == 'files.json':
        for item in json.loads(raw)['files']:
            f = root / item['path'] if item['path'].startswith(p.parent.relative_to(root).as_posix() + '/') else p.parent / item['path']
            b = f.read_bytes()
            assert len(b) == item['bytes'] and sha(b) == item['sha256'], str(f)

source_path = 'submission/w9a2-weighted-potential-20261020-prepared-v7/proof/Solution.lean'
source = (root / source_path).read_bytes()
assert len(source) == 1829242
assert sha(source) == 'dae01f6844642d7f9ee8180616c1f57aefc18ab8616bc8a4a46a14bf8e9fefc6'
assert source == (root / 'research-goal-20261020-w9a2-delivery/draft-v7/Solution.lean').read_bytes()
wire = root / 'submission/w9a2-weighted-potential-20261020-expected-wire-v7/expected-server-submission.json'
manifest = wire.read_bytes()
m = json.loads(manifest)
assert sha(manifest) == '7d78afb3d25847b89bd0d4daae06daec52e55e8a39524f82431599bbf21d70f6'
bundle = sha(b'submission.json\0' + manifest + b'proof/Solution.lean\0' + source)
assert bundle == '1f28020dcda27176a97f8c48e9c9d3f9dc00107ce904f1a1f6706b1f43309771'
state = json.loads((root / 'research-goal-20261016/direction-state.json').read_text(encoding='utf-8'))
assert state['last_review_number'] == 9 and state['main_rounds_since_review'] == 0
gate = {
 'schema': 'root-w9a2-v7-one-official-submission-gate-v1',
 'created_UTC': datetime.now(timezone.utc).isoformat(),
 'review': checked[0],
 'scope': 'Static minimal source edit, exact submission materials and existing human authorization. Not a compiler, kernel or official acceptance result.',
 'source': {'path': source_path, 'bytes': len(source), 'sha256': sha(source)},
 'expected_bundle_digest': bundle,
 'expected_server_manifest_sha256': sha(manifest),
 'submission_id': 'lixiang90-w9a2-weighted-potential-v7-20261020',
 'author': 'Li Xiang',
 'source_edit_count': 23,
 'source_change': '8 explicit noncomputable modifiers and 15 independent diagnostic print deletions; all other raw source bytes preserved',
 'existing_human_authorization': 'Submit to riemannzeta.fun as Li Xiang, no repeated local verification; human also explicitly agreed to indefinite encrypted maintainer-only retention and Apache-2.0 permanent public evidence if accepted. Same proof, destination and terms; no material legal/data/risk scope change.',
 'prerequisites_before_click': ['Successful normal GitHub push of exact new source and materials', 'Fixed pushed-commit source bytes match this source digest', 'Current website formal record still strictly below K', 'Visible form metadata, byte count and agreement match this gate'],
 'allowed_execution': 'Exactly one new official competitive upload of this v7, then observe same job and its exact digest/result. No local compiler/export/kernel/old collector run.',
 'official_slots_observed_before_attempt': {'used': 1, 'remaining': 2, 'reset_UTC': '2026-10-21T00:00:00Z'},
 'v7_local_compile_pass': False,
 'v7_kernel_pass': False,
 'v7_official_acceptance': False,
 'speedup_measured': False,
 'full_3200_guarantee': False,
 'stop_conditions': ['Any source/metadata/digest mismatch', 'Latest R >= K', 'Actual compile/comparison/axiom/kernel rejection', 'Another timeout: preserve and review; no automatic retry'],
 'goal_status': 'active',
 'checked_input_manifests': checked,
}
out = here / 'gate.json'
assert not out.exists()
out.write_text(json.dumps(gate, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print(json.dumps({'gate_sha256': sha(out.read_bytes()), 'source_sha256': sha(source), 'bundle': bundle, 'checked_manifests': len(checked)}))
