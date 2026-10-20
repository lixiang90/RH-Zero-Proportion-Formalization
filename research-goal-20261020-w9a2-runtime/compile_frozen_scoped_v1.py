"""One source-pinned ordinary Lean batch in the relocated Windows workspace.

No solver, automatic source repair, Lake build, exporter or kernel replay.
Every call has a fresh work directory and an explicit hashed root gate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import traceback

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            h.update(block)
    return h.hexdigest()


def write(path, data):
    with Path(path).open('x', encoding='utf-8', newline='\n') as stream:
        json.dump(data, stream, ensure_ascii=True, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--gate', required=True)
    ap.add_argument('--gate-sha256', required=True)
    args = ap.parse_args()
    gate_path = (ROOT / args.gate).resolve()
    assert gate_path.is_relative_to(ROOT) and sha(gate_path) == args.gate_sha256
    gate = json.loads(gate_path.read_text(encoding='utf-8'))
    assert gate['authorized'] is True and gate['task'] == 'w9a2-ordinary-source-pinned'
    assert gate['automatic_repairs_or_retries'] == 0
    assert sha(__file__) == gate['runner_sha256']
    lean = Path(gate['lean']['path'])
    assert sha(lean) == gate['lean']['sha256']
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    assert version == gate['lean']['version']
    pins = gate['source_files'] + gate.get('reused_oleans', [])
    for row in pins:
        assert sha(ROOT / row['path']) == row['sha256'], row['path']
    for row in gate['packages']:
        actual = subprocess.check_output(['git', '-C', str(ROOT / row['path']),
                                          'rev-parse', 'HEAD'], text=True).strip()
        assert actual == row['commit'], row['path']
    # Exclude this exact pinned compiler, not unrelated user projects on other SDKs.
    # No untrusted input is interpolated into shell text; compiler path is read via env.
    probe_env = os.environ.copy()
    probe_env['W9A2_PINNED_LEAN'] = str(lean.resolve())
    probe_script = "@((Get-CimInstance Win32_Process -Filter \"Name='lean.exe'\") | Where-Object { $_.ExecutablePath -eq $env:W9A2_PINNED_LEAN }).Count"
    ps = subprocess.run(['powershell.exe', '-NoProfile', '-Command', probe_script],
                        capture_output=True, text=True, check=True, env=probe_env)
    assert ps.stdout.strip() == '0', 'Another pinned 4.33.0-rc2 Lean process is active'
    job = (ROOT / gate['work_directory']).resolve()
    assert job.is_relative_to(ROOT / 'tmp')
    job.mkdir(parents=True, exist_ok=False)
    lib = job / 'lib'
    lib.mkdir()
    for row in gate.get('reused_oleans', []):
        dest = lib / row['module_path']
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes((ROOT / row['path']).read_bytes())
        assert sha(dest) == row['sha256']
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join([str(lib), *[str(ROOT / p) for p in gate['package_libs']]])
    write(job / 'started.json', {'gate_sha256': args.gate_sha256, 'pid': os.getpid(),
                                'time_unix': time.time(), 'version': version,
                                'ordinary_only': True, 'automatic_repairs_or_retries': 0})
    receipts = []
    try:
        for target in gate['targets']:
            source = ROOT / target['source']
            module = target['module']
            assert re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*', module)
            output = lib.joinpath(*module.split('.')).with_suffix('.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            name = module.replace('.', '_')
            log = job / (name + '.log')
            initial_sha = sha(source)
            (job / (name + '.lean')).write_bytes(source.read_bytes())
            command = [str(lean), '-j1', '-M13500', '--tstack=262144',
                       '-DrelaxedAutoImplicit=false', '-DElab.async=false',
                       '-R', str(ROOT / target.get('source_root', '.')),
                       '-o', str(output), str(source)]
            write(job / (name + '.command.json'), {'argv': command,
                                                 'LEAN_PATH': env['LEAN_PATH']})
            start = time.monotonic()
            with log.open('xb') as stream:
                child = subprocess.Popen(command, cwd=ROOT, env=env,
                                         stdout=stream, stderr=subprocess.STDOUT)
                write(job / (name + '.child.json'), {'pid': child.pid, 'time_unix': time.time()})
                print(json.dumps({'module': module, 'pid': child.pid}), flush=True)
                code = child.wait()
                stream.flush()
                os.fsync(stream.fileno())
            text = log.read_text(encoding='utf-8', errors='replace')
            observed = {}
            for root, raw in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S):
                observed[root] = [x.strip() for x in raw.split(',') if x.strip()]
            for root in re.findall(r"'([^']+)' does not depend on any axioms", text):
                observed[root] = []
            expected = target.get('printed_roots', [])
            axiom_ok = (set(observed) == set(expected) and
                        all(set(v) <= ALLOWED for v in observed.values())) if expected else None
            unchanged = sha(source) == initial_sha
            passed = code == 0 and output.exists() and unchanged and axiom_ok is not False
            receipt = {'module': module, 'exit_code': code,
                       'elapsed_seconds': time.monotonic() - start,
                       'source_sha256': initial_sha, 'source_unchanged': unchanged,
                       'log_sha256': sha(log), 'olean_sha256': sha(output) if output.exists() else None,
                       'expected_roots': expected, 'observed_axioms': observed,
                       'axiom_audit_passed': axiom_ok, 'ordinary_compile_passed': passed,
                       'Comparator_passed': False, 'independent_kernel_passed': False,
                       'website_submission_ready': False}
            write(job / (name + '.receipt.json'), receipt)
            receipts.append(receipt)
            print(json.dumps(receipt), flush=True)
            if not passed:
                break
        for row in pins:
            assert sha(ROOT / row['path']) == row['sha256'], row['path']
        passed = len(receipts) == len(gate['targets']) and all(r['ordinary_compile_passed'] for r in receipts)
        write(job / 'terminal.json', {'passed': passed, 'modules_completed': len(receipts),
                                     'time_unix': time.time(), 'ordinary_only': True})
        return 0 if passed else 1
    except BaseException as error:
        write(job / 'failure.json', {'type': type(error).__name__, 'message': str(error),
                                    'traceback': traceback.format_exc(), 'time_unix': time.time()})
        raise


if __name__ == '__main__':
    raise SystemExit(main())
