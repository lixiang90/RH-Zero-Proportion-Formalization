"""Root-reviewed candidate gate after a real trusted-definition setup PASS."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


proposal = ROOT / 'research-goal-20261020-w9a2-formal-static-review/candidate-ordinary-gate-proposal.json'
assert sha(proposal) == '4486a57c7a4cbd2e4f4f305c32c692c9c4e8aabf8f8c07a6da567aa7e17a7d37'
gate = json.loads(proposal.read_text(encoding='utf-8'))
trusted = ROOT / 'tmp/w9a2-20261020/trusted-v1'
terminal = json.loads((trusted / 'terminal.json').read_text(encoding='utf-8'))
receipt = json.loads((trusted / 'ChallengeDeps.receipt.json').read_text(encoding='utf-8'))
assert terminal['passed'] and terminal['modules_completed'] == 1
assert receipt['ordinary_compile_passed'] and receipt['exit_code'] == 0
assert receipt['source_sha256'] == 'f05666d0745edbf2dac6ce2a4de675abd1bba3c336fe24aebb80f27d1365ebbd'
assert receipt['source_unchanged'] and receipt['olean_sha256'] == sha(trusted / 'lib/ChallengeDeps.olean')
assert not (trusted / 'failure.json').exists()
gate['reused_oleans'][0]['sha256'] = receipt['olean_sha256']
extra = [proposal, trusted / 'terminal.json', trusted / 'ChallengeDeps.receipt.json',
         ROOT / 'research-goal-20261020-w9a2-runtime/before-ordinary-v0/leaderboard.json',
         ROOT / 'research-goal-20261020-w9a2-runtime/before-ordinary-v0/leaderboard-receipt.json',
         ROOT / 'research-goal-20261020-w9a2-independent-static/files.json']
gate['source_files'] += [{'path': p.relative_to(ROOT).as_posix(), 'sha256': sha(p)} for p in extra]
for row in gate['source_files'] + gate['reused_oleans']:
    assert sha(ROOT / row['path']) == row['sha256'], row['path']
gate.update(authorized=True, proposal_only=False, sole_candidate_compiler_owner='/root',
            root_observed_trusted_parent_actual_exit_code=0,
            runtime_scope='Windows native development only; no fullchain/cold/Comparator/Nano claim',
            candidate_compiler_runs_before_this_gate=0,
            report_point_seconds_per_module=1200,
            stop='First nonzero exit, failed finite check, changed input or unexpected axiom stops the batch. No automatic repair/retry.',
            pending_before_root_freeze=[])
out = ROOT / 'research-goal-20261016/gates/w9a2-ordinary-v0-20261020.json'
with out.open('x', encoding='utf-8', newline='\n') as stream:
    json.dump(gate, stream, indent=2)
    stream.write('\n')
print(json.dumps({'gate': out.relative_to(ROOT).as_posix(), 'sha256': sha(out),
                  'verified_source_and_artifact_pins': len(gate['source_files']) + len(gate['reused_oleans'])}))
