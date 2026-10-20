"""Linux-only, one-gate, source-pinned ordinary import/compile runner.

Prepared only. No exporter, Comparator, nanoda, cache, optimizer, Lake build,
dependency rebuild, source repair, or retry. An independently authorized root
gate and fresh Windows/Linux exclusivity are mandatory at execution time.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import platform
import re
import signal
import subprocess
import time
import traceback

REPO = Path(__file__).resolve().parents[1]
RUNTIME_ROOT = Path('/var/tmp/rh-zero-w9a2-20261020/runtime-v0')
DEV_ROOT = Path('/var/tmp/rh-zero-w9a2-20261020/dev')
ALLOWED_AXIOMS = {'propext', 'Quot.sound', 'Classical.choice'}
STAGES = {
    'trusted': ['TrustedImport', 'ChallengeDeps'],
    'candidate': ['StructuralW9A220261020.' + s for s in
                  ['Prefix', 'Core', 'Graph', 'Localization', 'Counting', 'Final']],
}
POWERSHELL = '/mnt/c/Windows/System32/WindowsPowerShell/v1.0/powershell.exe'


def sha(path):
    value = hashlib.sha256()
    with Path(path).open('rb') as source:
        for block in iter(lambda: source.read(1048576), b''):
            value.update(block)
    return value.hexdigest()


def json_bytes(data):
    return (json.dumps(data, ensure_ascii=True, indent=2) + '\n').encode()


def create(path, raw):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as out:
        out.write(raw)
        out.flush()
        os.fsync(out.fileno())


def repo_path(relative):
    path = (REPO / relative).resolve()
    assert path.is_relative_to(REPO)
    return path


def proc(pid):
    base = Path('/proc') / str(pid)
    stat = (base / 'stat').read_text()
    tail = stat[stat.rindex(')') + 2:].split()
    status = (base / 'status').read_text()
    cmd = (base / 'cmdline').read_bytes().split(b'\0')
    return {'pid': pid, 'state': tail[0], 'ppid': int(tail[1]),
            'start_ticks': int(tail[19]), 'user_ticks': int(tail[11]),
            'system_ticks': int(tail[12]),
            'rss_kib': int(re.search(r'^VmRSS:\s*(\d+)', status, re.M).group(1))
                       if re.search(r'^VmRSS:\s*(\d+)', status, re.M) else 0,
            'argv': [x.decode(errors='replace') for x in cmd if x]}


def exclusivity():
    linux = subprocess.run(['pgrep', '-a', '-x', 'lean'], capture_output=True, text=True)
    assert linux.returncode in [0, 1], linux.stderr
    assert linux.returncode == 1, 'Another Linux Lean is live: ' + linux.stdout
    win = subprocess.run([POWERSHELL, '-NoLogo', '-NoProfile', '-NonInteractive', '-Command',
        '@(Get-Process lean -ErrorAction SilentlyContinue).Count'],
        capture_output=True, text=True, check=True)
    assert win.stdout.strip() == '0', 'Another Windows Lean is live: ' + win.stdout
    return {'linux_pgrep_returncode': linux.returncode, 'linux_lean_processes': [],
            'windows_lean_count': 0, 'observed_unix': time.time()}


def check_source_pins(rows):
    for row in rows:
        path = repo_path(row['path'])
        assert path.is_file() and sha(path) == row['sha256'], row['path']


def check_runtime(runtime, gate):
    assert runtime['status'] == 'SETUP_ONLY_PORTABILITY_UNTESTED'
    assert runtime['runtime_root'] == str(RUNTIME_ROOT)
    assert runtime['compiler_invocations'] == runtime['cache_invocations'] == runtime['proof_invocations'] == 0
    assert runtime['native_windows_binaries_copied'] is False
    assert runtime['lake_or_setup_plugins_used'] is False
    assert runtime['compiler_archive_sha256'] == gate['compiler_archive_sha256']
    assert runtime['lean_sha256'] == gate['lean']['sha256']
    lean = Path(runtime['lean'])
    assert lean.is_relative_to(RUNTIME_ROOT) and sha(lean) == gate['lean']['sha256']
    manifest = Path(runtime['mirror_manifest'])
    assert manifest.is_relative_to(RUNTIME_ROOT)
    assert sha(manifest) == gate['runtime_mirror_manifest_sha256'] == runtime['mirror_manifest_sha256']
    assert {e['name']: e['commit'] for e in runtime['package_source_pins']} == gate['package_commits']
    counted = {'source': 0, 'library_data': 0}
    with manifest.open(encoding='utf-8') as source:
        for line in source:
            row = json.loads(line)
            path = Path(row['destination'])
            assert path.is_relative_to(RUNTIME_ROOT / '.lake/packages')
            assert path.is_file() and not path.is_symlink()
            assert path.stat().st_size == row['bytes'] and sha(path) == row['destination_sha256'], str(path)
            assert row['kind'] in counted
            counted[row['kind']] += 1
    assert counted['source'] == runtime['totals']['sources']
    assert counted['library_data'] == runtime['totals']['library_data']
    libs = [Path(p) for p in runtime['lean_path'].split(':')]
    assert len(libs) == len(gate['package_commits'])
    assert all(p.is_relative_to(RUNTIME_ROOT / '.lake/packages') and p.is_dir() for p in libs)
    return lean, libs, counted


def audit_axioms(text, expected):
    found = {}
    for root, values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S):
        assert root not in found, 'Duplicate axiom output: ' + root
        found[root] = [v.strip() for v in values.split(',') if v.strip()]
    for root in re.findall(r"'([^']+)' does not depend on any axioms", text):
        assert root not in found, 'Duplicate axiom output: ' + root
        found[root] = []
    passed = set(found) == set(expected) and all(set(v) <= ALLOWED_AXIOMS for v in found.values())
    return found, passed


def main():
    assert os.name == 'posix' and platform.machine() == 'x86_64'
    assert str(REPO) == '/mnt/e/codex-build/RH-Zero-Proportion-Formalization'
    parser = argparse.ArgumentParser()
    parser.add_argument('--gate', required=True)
    parser.add_argument('--gate-sha256', required=True)
    args = parser.parse_args()
    gate_path = repo_path(args.gate)
    assert sha(gate_path) == args.gate_sha256
    gate = json.loads(gate_path.read_text(encoding='utf-8'))
    assert gate['authorized'] is True and gate['proposal_only'] is False
    assert gate['task'] == 'w9a2-linux-ordinary-source-pinned'
    assert gate['automatic_repairs_or_retries'] == 0 and gate['max_parallel_compilers'] == 1
    assert gate['stage'] in STAGES
    assert [t['module'] for t in gate['targets']] == STAGES[gate['stage']]
    assert sha(__file__) == gate['runner_sha256']
    assert gate['root_confirmed_original_windows_handle_terminal'] is True
    evidence = repo_path(gate['windows_terminal_evidence']['path'])
    assert sha(evidence) == gate['windows_terminal_evidence']['sha256']
    check_source_pins(gate['source_files'])
    runtime_path = Path(gate['runtime_manifest'])
    assert runtime_path == RUNTIME_ROOT / 'runtime.json'
    assert sha(runtime_path) == gate['runtime_manifest_sha256']
    runtime = json.loads(runtime_path.read_text())
    lean, package_libs, runtime_checked = check_runtime(runtime, gate)
    initial_exclusive = exclusivity()
    job = Path(gate['work_directory'])
    assert job.parent == DEV_ROOT and re.fullmatch(r'[A-Za-z0-9_-]+', job.name)
    mirror = repo_path(gate['metadata_mirror'])
    assert mirror.parent == REPO / 'tmp/w9a2-20261020'
    assert not job.exists() and not mirror.exists()
    DEV_ROOT.mkdir(parents=True, exist_ok=True)
    lock = DEV_ROOT / 'ordinary-active.lock'
    lock_bytes = json_bytes({'owner': proc(os.getpid()), 'gate_sha256': args.gate_sha256,
                             'work_directory': str(job), 'started_unix': time.time()})
    create(lock, lock_bytes)  # An old lock requires an explicit root audit; never auto-clear it.
    child = None
    child_start = None
    job.mkdir()
    mirror.mkdir(parents=True)
    lib = job / 'lib'
    sources = job / 'sources'
    lib.mkdir()
    sources.mkdir()

    def emit(name, value):
        data = json_bytes(value)
        create(job / name, data)
        create(mirror / name, data)

    def mirror_log(path):
        create(mirror / path.relative_to(job), path.read_bytes())

    def stop_own_child():
        nonlocal child
        if child is not None and child.poll() is None:
            try:
                current = proc(child.pid)
            except FileNotFoundError:
                child.wait(timeout=10)
                return
            assert current['start_ticks'] == child_start['start_ticks']
            try:
                child.terminate()
            except ProcessLookupError:
                child.wait(timeout=10)
                return
            try:
                child.wait(timeout=10)
            except subprocess.TimeoutExpired:
                current = proc(child.pid)
                assert current['start_ticks'] == child_start['start_ticks']
                child.kill()
                child.wait()

    def interrupted(signum, frame):
        raise InterruptedError('Runner received signal ' + str(signum))

    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    batch_start = time.monotonic()
    receipts = []
    try:
        exclusivity()  # Repeat after acquiring the shared owner lock.
        if gate['stage'] == 'candidate':
            prior = repo_path(gate['trusted_terminal']['path'])
            assert sha(prior) == gate['trusted_terminal']['sha256']
            terminal = json.loads(prior.read_text())
            assert terminal['passed'] and terminal['stage'] == 'trusted' and terminal['modules_completed'] == 2
            trusted_receipt_path = repo_path(gate['trusted_module_receipt']['path'])
            assert sha(trusted_receipt_path) == gate['trusted_module_receipt']['sha256']
            trusted_receipt = json.loads(trusted_receipt_path.read_text())
            assert trusted_receipt['module'] == 'ChallengeDeps'
            assert trusted_receipt['ordinary_compile_passed'] and trusted_receipt['axiom_audit_passed']
            assert trusted_receipt['source_unchanged'] and trusted_receipt['exit_code'] == 0
            assert trusted_receipt['source_sha256'] == gate['trusted_source_sha256']
        for reuse in gate.get('reused_oleans', []):
            artifact = Path(reuse['path'])
            assert artifact.is_relative_to(DEV_ROOT)
            assert sha(artifact) == reuse['sha256']
            destination = lib / reuse['module_path']
            assert destination.is_relative_to(lib)
            create(destination, artifact.read_bytes())
            assert sha(destination) == reuse['sha256']
        if gate['stage'] == 'candidate':
            assert [r['module_path'] for r in gate['reused_oleans']] == ['ChallengeDeps.olean']
            assert gate['reused_oleans'][0]['path'] == trusted_receipt['olean_path']
            assert gate['reused_oleans'][0]['sha256'] == trusted_receipt['olean_sha256']
        else:
            assert not gate.get('reused_oleans')
        version = subprocess.check_output([str(lean), '--version'], text=True).strip()
        assert version == gate['lean']['version']
        env = dict(os.environ)
        env.pop('LEAN_SYSROOT', None)
        env['LEAN_PATH'] = ':'.join([str(lib), *map(str, package_libs)])
        env['LEAN_SRC_PATH'] = ':'.join([str(sources), *[str(p.parents[3]) for p in package_libs]])
        env['PATH'] = str(lean.parent) + ':/usr/bin:/bin'
        env['LD_LIBRARY_PATH'] = ':'.join([str(lean.parent.parent / 'lib/lean'), str(lean.parent.parent / 'lib')])
        emit('started.json', {'gate_sha256': args.gate_sha256, 'stage': gate['stage'],
            'owner': proc(os.getpid()), 'version': version, 'exclusive_observation': initial_exclusive,
            'runtime_files_rehashed': runtime_checked, 'ordinary_only': True,
            'compiler_max_parallel': 1, 'automatic_repairs_or_retries': 0, 'started_unix': time.time()})
        for target in gate['targets']:
            exclusivity()
            module = target['module']
            assert re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*', module)
            original = repo_path(target['source'])
            pinned = next(p for p in gate['source_files'] if p['path'] == target['source'])
            assert sha(original) == pinned['sha256']
            source = sources.joinpath(*module.split('.')).with_suffix('.lean')
            create(source, original.read_bytes())
            assert sha(source) == pinned['sha256']
            observed_prints = re.findall(r'^#print axioms (\S+)\s*$', source.read_text(), re.M)
            assert observed_prints == target['printed_roots']
            output = lib.joinpath(*module.split('.')).with_suffix('.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            name = module.replace('.', '_')
            log = job / (name + '.log')
            command = [str(lean), '-j1', '-M13500', '--tstack=262144',
                '-DrelaxedAutoImplicit=false', '-DElab.async=false', '-R', str(sources),
                '-o', str(output), str(source)]
            emit(name + '.command.json', {'argv': command, 'LEAN_PATH': env['LEAN_PATH'],
                'source_original': str(original), 'source_snapshot': str(source),
                'source_sha256': pinned['sha256'], 'expected_axiom_roots': target['printed_roots']})
            started = time.monotonic()
            timed_out = False
            with log.open('xb') as stream:
                child = subprocess.Popen(command, cwd=sources, env=env, stdout=stream,
                    stderr=subprocess.STDOUT, start_new_session=True)
                try:
                    child_start = proc(child.pid)
                except FileNotFoundError:
                    assert child.poll() is not None
                    child_start = {'pid': child.pid, 'start_ticks': None,
                                   'exited_before_proc_snapshot': True, 'popen_poll': child.poll()}
                emit(name + '.child.json', {'handle': child_start, 'launched_unix': time.time()})
                print(json.dumps({'module': module, 'handle': child_start}), flush=True)
                observation = 0
                next_observation = started
                while child.poll() is None:
                    now = time.monotonic()
                    if now - started > gate['hard_seconds_per_target'] or now - batch_start > gate['hard_seconds_per_batch']:
                        timed_out = True
                        stop_own_child()
                        break
                    if now >= next_observation:
                        try:
                            live = proc(child.pid)
                            assert live['start_ticks'] == child_start['start_ticks']
                        except FileNotFoundError:
                            # poll the same Popen handle; an observation race is
                            # not a terminal claim or permission to restart.
                            live = {'pid': child.pid, 'proc_observation_race': True}
                        emit('observations/' + name + f'-{observation:05d}.json', {
                            'module': module, 'handle': live, 'popen_poll': child.poll(),
                            'elapsed_seconds': now - started, 'log_bytes': log.stat().st_size,
                            'observed_unix': time.time()})
                        observation += 1
                        next_observation = now + 20
                    time.sleep(2)
                code = child.wait()
                stream.flush()
                os.fsync(stream.fileno())
            mirror_log(log)
            text = log.read_text(encoding='utf-8', errors='replace')
            observed, axiom_ok = audit_axioms(text, target['printed_roots'])
            unchanged = sha(original) == sha(source) == pinned['sha256']
            passed = code == 0 and not timed_out and output.is_file() and unchanged and axiom_ok
            receipt = {'module': module, 'exit_code': code, 'timed_out': timed_out,
                'elapsed_seconds': time.monotonic() - started, 'source_sha256': pinned['sha256'],
                'source_unchanged': unchanged, 'log_sha256': sha(log),
                'olean_path': str(output), 'olean_sha256': sha(output) if output.exists() else None,
                'expected_roots': target['printed_roots'], 'observed_axioms': observed,
                'axiom_audit_passed': axiom_ok, 'ordinary_compile_passed': passed,
                'Compiler_handle': child_start, 'Comparator_passed': False,
                'independent_kernel_passed': False, 'website_submission_ready': False}
            emit(name + '.receipt.json', receipt)
            receipts.append(receipt)
            print(json.dumps(receipt), flush=True)
            child = None
            if not passed:
                break
        check_source_pins(gate['source_files'])
        assert sha(runtime_path) == gate['runtime_manifest_sha256']
        check_runtime(runtime, gate)  # No imported source/data pin audit is skipped.
        passed = len(receipts) == len(gate['targets']) and all(r['ordinary_compile_passed'] for r in receipts)
        emit('terminal.json', {'passed': passed, 'stage': gate['stage'],
            'modules_completed': len(receipts), 'gate_sha256': args.gate_sha256,
            'owner': proc(os.getpid()), 'elapsed_seconds': time.monotonic() - batch_start,
            'time_unix': time.time(), 'ordinary_only': True, 'active_child': None})
        return 0 if passed else 1
    except BaseException as error:
        stop_own_child()
        emit('failure.json', {'type': type(error).__name__, 'message': str(error),
            'traceback': traceback.format_exc(), 'time_unix': time.time(),
            'owner_pid': os.getpid(), 'active_child': None, 'automatic_retry': False})
        raise
    finally:
        stop_own_child()
        # Preserve the owner record in immutable started/terminal/failure files;
        # clear only this exact live owner's shared lock after its child exits.
        if lock.exists() and lock.read_bytes() == lock_bytes:
            lock.unlink()


if __name__ == '__main__':
    raise SystemExit(main())
