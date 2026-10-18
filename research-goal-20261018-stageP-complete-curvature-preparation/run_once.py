"""P sole-child launcher; immutable root gate required, no implicit resume."""
from pathlib import Path
from hashlib import sha256
import argparse
import json
import os
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
THREAD_ENV = {name: '1' for name in ['OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS',
    'NUMEXPR_NUM_THREADS', 'VECLIB_MAXIMUM_THREADS', 'BLIS_NUM_THREADS']}

def pin(path):
    h = sha256()
    with path.open('rb') as handle:
        for block in iter(lambda: handle.read(1048576), b''): h.update(block)
    return h.hexdigest()
def load(path): return json.loads(path.read_text(encoding='utf-8'))
def write(path, value):
    with path.open('x', encoding='utf-8', newline='\n') as handle:
        json.dump(value, handle, indent=2); handle.write('\n'); handle.flush(); os.fsync(handle.fileno())
def size(): return sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--launch-authorized-complete-curvature-P', action='store_true')
    ap.add_argument('--gate'); ap.add_argument('--gate-sha256'); args = ap.parse_args()
    assert args.launch_authorized_complete_curvature_P and args.gate and args.gate_sha256
    for name in ['launch.json', 'child.json', 'started.json', 'result.json', 'failure.json', 'terminal.json', 'inconclusive.json']:
        assert not (HERE / name).exists(), ('single_attempt_no_retry', name)
    path = (ROOT / args.gate).resolve(); assert path.is_relative_to(ROOT) and pin(path) == args.gate_sha256
    gate = load(path); assert gate['same_model_complete_curvature_passes_authorized'] == 1
    assert gate['maximum_new_LP_calls'] == 13002 and gate['previous_LP_calls'] == 2374
    assert gate['auxiliary_or_retry_calls_authorized'] == 0
    hard, soft = gate['resource_limits'], gate['work_limits']
    assert 0 < soft['elapsed_seconds'] < hard['elapsed_seconds']
    assert 0 < soft['closed_output_bytes'] < hard['closed_output_bytes']
    command = [sys.executable, '-B', '-X', 'utf8', str(HERE / 'continue_once.py'),
        '--execute-authorized-complete-curvature-P', '--gate', args.gate, '--gate-sha256', args.gate_sha256]
    env = dict(os.environ); env.update(THREAD_ENV); env['PYTHONDONTWRITEBYTECODE'] = '1'
    identity = {'argv': command, 'cwd': str(ROOT), 'thread_env_override': THREAD_ENV}
    write(HERE / 'launch.json', {'schema': 'P-one-child-launch-v1', 'parent_pid': os.getpid(), 'command': identity,
        'command_sha256': sha256(json.dumps(identity, sort_keys=True, separators=(',', ':')).encode()).hexdigest(),
        'producer_sha256': pin(HERE / 'continue_once.py'), 'launcher_sha256': pin(Path(__file__)),
        'gate_path': args.gate, 'gate_sha256': args.gate_sha256, 'maximum_launches': 1, 'hard_limits': hard})
    start = time.monotonic(); reason = None
    with (HERE / 'stdout.log').open('xb') as out, (HERE / 'stderr.log').open('xb') as err:
        proc = subprocess.Popen(command, cwd=ROOT, env=env, stdout=out, stderr=err)
        write(HERE / 'child.json', {'child_pid': proc.pid, 'parent_pid': os.getpid(), 'time_unix': time.time(), 'launches': 1})
        print(json.dumps({'stage': 'P_child_live', 'child_pid': proc.pid, 'parent_pid': os.getpid()}), flush=True)
        while proc.poll() is None:
            if time.monotonic() - start > hard['elapsed_seconds']: reason = 'hard_elapsed_limit_inconclusive'
            elif size() > hard['closed_output_bytes']: reason = 'hard_output_limit_inconclusive'
            if reason: proc.terminate(); break
            time.sleep(.2)
        code = proc.wait()
        for handle in [out, err]: handle.flush(); os.fsync(handle.fileno())
    started = load(HERE / 'started.json') if (HERE / 'started.json').exists() else {}
    after = {name: pin(ROOT / name) for name in started.get('inputs_sha256', {})}
    external = {name: pin(Path(name)) for name in started.get('external_runtime_sha256_start', {})}
    terminal = {'schema': 'P-one-child-terminal-v1', 'child_pid': proc.pid, 'parent_pid': os.getpid(),
        'exit_code': code, 'seconds': time.monotonic() - start, 'limit_stop': reason, 'child_launches': 1,
        'automatic_retry': False, 'closed_output_bytes': size(), 'result_present': (HERE / 'result.json').exists(),
        'failure_present': (HERE / 'failure.json').exists(), 'inconclusive_present': (HERE / 'inconclusive.json').exists(),
        'journal_sha256': pin(HERE / 'progress-commits.jsonl') if (HERE / 'progress-commits.jsonl').exists() else None,
        'inputs_sha256_end_after_terminal': after, 'external_runtime_sha256_end_after_terminal': external,
        'inputs_unchanged_after_terminal': after == started.get('inputs_sha256', {}),
        'external_runtime_unchanged_after_terminal': external == started.get('external_runtime_sha256_start', {})}
    write(HERE / 'terminal.json', terminal)
    print(json.dumps({key: value for key, value in terminal.items() if 'sha256_end' not in key}), flush=True)
    if code or reason or not terminal['inputs_unchanged_after_terminal'] or not terminal['external_runtime_unchanged_after_terminal']:
        raise SystemExit(1)

if __name__ == '__main__': main()
