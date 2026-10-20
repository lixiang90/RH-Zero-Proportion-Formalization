"""One inert-JSON diagnostic invocation; no Lean, compiler or proof validation."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
RUNNER = ROOT / 'research-goal-20261020-w9a2-export-cost-plan-formal/run_stream.py'
SHA = '643c444d659d280f13068d2cde597acd467900e8b0264258363c1e9efcedc122'
OUTER = ROOT / 'research-goal-20261020-w9a2-export-cost-scan-v1'

def main():
    started = time.monotonic()
    if sys.flags.optimize:
        raise RuntimeError('Optimized Python is forbidden: assertion guards must remain enabled')
    assert len(sys.argv) == 2 and sys.argv[1] == '--authorize-once'
    assert hashlib.sha256(RUNNER.read_bytes()).hexdigest() == SHA
    # Exclusive fresh result directory is the one-use marker, including on failure.
    OUTER.mkdir()
    argv = [sys.executable, str(RUNNER), '--authorize-once', '--runner-sha256', SHA,
            '--output-directory', str(OUTER / 'scan')]
    timeout = False
    try:
        child = subprocess.run(argv, cwd=ROOT, stdin=subprocess.DEVNULL,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               timeout=max(.1, 115 - (time.monotonic() - started)))
        code, stdout, stderr = child.returncode, child.stdout, child.stderr
    except subprocess.TimeoutExpired as error:
        # subprocess.run kills and waits for its own direct child before raising.
        timeout, code = True, None
        stdout, stderr = error.stdout or b'', error.stderr or b''
    elapsed = time.monotonic() - started
    assert len(stdout) + len(stderr) <= (1 << 20)
    result_path = OUTER / 'scan/result.json'
    result_raw = result_path.read_bytes() if result_path.exists() else b''
    result = json.loads(result_raw) if result_raw else None
    observed_success = bool(code == 0 and not timeout and elapsed < 120 and result
                            and result.get('complete') is True and result.get('success') is True
                            and result.get('bytes') == 677296932
                            and result.get('sha256') == '1cc0f929919e0d4f58d947223c75a82450df57da11a9fe43fd93a90d8c8433d7'
                            and result.get('observed_peak_RSS_bytes', 1 << 60) < 256 << 20)
    terminal = dict(schema='one-static-export-scan-outer-v1', child_argv=argv,
                    actual_child_exit_code=code, timeout=timeout,
                    elapsed_seconds=elapsed, observed_structural_scan_complete=observed_success,
                    mathematical_validation=False, compiler_or_kernel_invocations=0,
                    fullchain_or_official_acceptance=False,
                    scope='Historical v6 serialization only; own child RSS is sampled, not an OS allocator cap.',
                    runner_sha256=SHA, result_exists=result_path.exists(),
                    result_sha256=hashlib.sha256(result_raw).hexdigest() if result_raw else None)
    raw = (json.dumps(terminal, ensure_ascii=False, indent=2)+'\n').encode()
    assert len(result_raw) + len(stdout) + len(stderr) + len(raw) <= (2 << 20)
    (OUTER / 'stdout.txt').write_bytes(stdout)
    (OUTER / 'stderr.txt').write_bytes(stderr)
    with (OUTER / 'outer-observation.json').open('xb') as stream:
        stream.write(raw)
    print(json.dumps({'outer': str(OUTER / 'outer-observation.json'), 'complete': observed_success,
                      'elapsed_seconds': elapsed, 'child_exit': code, 'timeout': timeout}), flush=True)
    # Acceptance includes result parsing, receipt writes and stdout finalization.
    return 0 if observed_success and time.monotonic() - started < 120 else 1

if __name__ == '__main__':
    raise SystemExit(main())
