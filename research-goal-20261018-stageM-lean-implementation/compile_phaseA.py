"""Gate-only serial ordinary Lean compilation; importing this file runs nothing."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
LINUX = '/mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization'
MODULES = ['CurrentPrefix', 'QuantizedComponent', 'Sparse78']
LEAN = '/var/tmp/rh-zero-20261015/lean-4.33.0-rc2-linux/bin/lean'
LEAN_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
DEPENDENCY_LIB = '/var/tmp/rh-zero-20261015/record-verification/modular/lib'
PINS = {
    LEAN: LEAN_SHA,
    DEPENDENCY_LIB + '/ChallengeDeps.olean':
        'a9127aa6c9a70793124b7b08c16baac0b205c4d717a44a313de812534aa01542',
    DEPENDENCY_LIB + '/ChallengeDeps/CandidateSpec.olean':
        '670b554a94297575edfeb26036162247539f2168c5f5c1ee657c65d305f3866b',
}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save_new(path, value):
    with Path(path).open('x', encoding='utf-8', newline='\n') as f:
        json.dump(value, f, ensure_ascii=False, indent=2)
        f.write('\n')
        f.flush()
        os.fsync(f.fileno())


def wsl(*args):
    return ['wsl.exe', '--distribution', 'Ubuntu', '--exec', *args]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--gate', required=True)
    ap.add_argument('--gate-sha256', required=True)
    ap.add_argument('--version', type=int, default=0, choices=range(4))
    ap.add_argument('--targets', nargs='+', choices=MODULES, default=MODULES)
    ap.add_argument('--repair-manifest')
    ns = ap.parse_args()
    gp = ROOT / ns.gate
    assert sha(gp) == ns.gate_sha256
    gate = json.loads(gp.read_text(encoding='utf-8'))
    assert gate['authorized'] is True
    assert gate['task'] == 'stageM-actual-Lean-phaseA'
    assert gate['prepared_manifest_sha256'] == sha(HERE / 'compiler-prepared.json')
    prepared = json.loads((HERE / 'compiler-prepared.json').read_text(encoding='utf-8'))
    for entry in prepared['files'] + prepared['dependencies']:
        assert sha(ROOT / entry['path']) == entry['sha256'], entry['path']
    assert sha(sys.executable) == prepared['Python_executable']['sha256']
    assert gate['ordinary_Lean_only'] is True
    assert gate['max_same_theorem_repairs'] <= 3
    assert ns.version <= gate['max_same_theorem_repairs']
    assert ns.targets == [m for m in MODULES if m in ns.targets]
    baseline = json.loads((HERE / 'phaseA-prepared.json').read_text(encoding='utf-8'))
    expected = {x['path']: x['sha256'] for x in baseline['files']}
    if ns.version:
        assert ns.repair_manifest
        rp = ROOT / ns.repair_manifest
        repair = json.loads(rp.read_text(encoding='utf-8'))
        assert repair['version'] == ns.version
        assert repair['same_mathematical_theorems'] is True
        assert repair['original_manifest_sha256'] == sha(HERE / 'phaseA-prepared.json')
        assert repair['repair_kind'] in ['syntax', 'API', 'tactic']
        expected.update({x['path']: x['sha256'] for x in repair['sources']})
    else:
        assert not ns.repair_manifest
    source_paths = ['StructuralS1RM20261018/' + m + '.lean' for m in ns.targets]
    for rel in source_paths:
        assert sha(ROOT / rel) == expected[rel], rel
    runtime_path = ROOT / 'tmp/setup-20261015/runtime.json'
    runtime = json.loads(runtime_path.read_text(encoding='utf-8'))
    assert runtime['lean'] == LEAN and runtime['lean_sha256'] == LEAN_SHA
    # One observational check, never launch a duplicate compiler.
    ps = subprocess.run(wsl('/usr/bin/pgrep', '-a', '-x', 'lean'), capture_output=True)
    assert ps.returncode == 1 and not ps.stdout, 'another Lean process is active'
    pin_result = subprocess.run(wsl('/usr/bin/sha256sum', *PINS),
                                capture_output=True, check=True)
    found = dict((line.split(maxsplit=1)[1].strip(), line.split()[0])
                 for line in pin_result.stdout.decode('utf-8').splitlines())
    assert found == PINS
    job = ROOT / 'tmp/current-s1r-M-20261018' / ('v' + str(ns.version))
    job.mkdir(parents=True, exist_ok=False)
    lib = ROOT / 'tmp/current-s1r-M-20261018/lib' if ns.version == 0 else job / 'lib'
    lib.mkdir(parents=True, exist_ok=True)
    lib_linux = LINUX + '/' + lib.relative_to(ROOT).as_posix()
    earlier = []
    for v in range(ns.version - 1, -1, -1):
        rel = 'tmp/current-s1r-M-20261018/' + ('lib' if v == 0 else 'v' + str(v) + '/lib')
        if (ROOT / rel).is_dir():
            earlier.append(LINUX + '/' + rel)
    leanpath = ':'.join([lib_linux, *earlier, DEPENDENCY_LIB, runtime['lean_path']])
    snapshot = {}
    for rel in source_paths:
        content = (ROOT / rel).read_bytes()
        (job / Path(rel).name).write_bytes(content)
        snapshot[rel] = hashlib.sha256(content).hexdigest()
    save_new(job / 'started.json', {
        'gate_sha256': ns.gate_sha256, 'runner_sha256': sha(__file__),
        'version': ns.version, 'targets': ns.targets, 'source_sha256': snapshot,
        'runtime_json_sha256': sha(runtime_path), 'external_pins': PINS,
        'Lean_path': leanpath, 'started_unix': time.time(), 'pid': os.getpid(),
        'scope': 'ordinary compilation only; no Nano/global-cover claim',
    })
    passed = True
    for mod in ns.targets:
        rel = 'StructuralS1RM20261018/' + mod
        output = lib / (rel + '.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        assert not output.exists(), 'never overwrite an existing olean'
        log = job / (mod + '.log')
        resources = job / (mod + '.resources.log')
        args = wsl('/usr/bin/time', '-v', '-o',
            LINUX + '/' + resources.relative_to(ROOT).as_posix(),
            '/usr/bin/prlimit', '--stack=268435456:268435456', '--',
            'env', 'LEAN_PATH=' + leanpath, LEAN, '-j1', '-M13500',
            '--tstack=262144', '-DrelaxedAutoImplicit=false',
            '-DElab.async=false', '-R', LINUX, '-o',
            lib_linux + '/' + rel + '.olean', LINUX + '/' + rel + '.lean')
        save_new(job / (mod + '.command.json'), {'argv': args})
        t0 = time.time()
        with log.open('xb') as f:
            p = subprocess.Popen(args, stdout=f, stderr=subprocess.STDOUT)
            save_new(job / (mod + '.child.json'), {'pid': p.pid, 'start_unix': t0})
            print(json.dumps({'module': mod, 'child_pid': p.pid}), flush=True)
            code = p.wait()
            f.flush()
            os.fsync(f.fileno())
        unchanged = sha(ROOT / (rel + '.lean')) == snapshot[rel + '.lean']
        receipt = {'module': mod, 'exit_code': code, 'elapsed_seconds': time.time()-t0,
            'source_unchanged': unchanged, 'source_sha256': snapshot[rel + '.lean'],
            'log_sha256': sha(log), 'resource_sha256': sha(resources),
            'olean_sha256': sha(output) if output.exists() else None,
            'ordinary_compile_passed': code == 0 and unchanged and output.exists(),
            'axiom_audit_pending': mod == 'CurrentPrefix',
            'Nano_replayed': False, 'global_cover_proved': False}
        save_new(job / (mod + '.receipt.json'), receipt)
        print(json.dumps(receipt), flush=True)
        if not receipt['ordinary_compile_passed']:
            passed = False
            break  # no import-failure cascade, no automatic repair or retry
    save_new(job / 'terminal.json', {'passed': passed, 'finished_unix': time.time()})
    return 0 if passed else 1


if __name__ == '__main__':
    raise SystemExit(main())
