"""Gated, isolated trusted native-tool installation. PREPARED, NOT EXECUTED.

Only pinned Export/Comparator plus the existing exact CoreAudit driver are
built. No user solution, mathematical experiment, export or proof replay is
run. This setup is prior to a future proof timer, as official template tools.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import tarfile
import time
import tomllib

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SDK = Path('/var/tmp/rh-zero-20261015/lean-4.33.0-rc2-linux')
WORK = Path('/var/tmp/rh-zero-20261015/tiny-native-tools-v0')
MIRROR = ROOT / 'tmp/current-s1r-tiny-20261018/native-tools-v0'
PREPARED = HERE / 'prepared-files.json'
ARCHIVES = {'lean4export': 'e1a22bb11b1fff7bcf36fd1546c11d36ca0a72601d81b08e65673469d54e0003',
            'Comparator': '73649fb6a9d4ff5efed8d5bc5b73f243398f9d95ac81a8dc24f6f51d513be94e'}
SOURCE_FILES = {'lean4export': ['Export.lean', 'Export/Parse.lean', 'Main.lean'],
                'Comparator': ['Comparator.lean', 'Comparator/Axioms.lean',
                               'Comparator/Compare.lean', 'Comparator/Util.lean', 'Main.lean']}
EXPECTED_MODULES = {'Export', 'Export.Parse', 'ExporterMain', 'Comparator',
                    'Comparator.Axioms', 'Comparator.Compare', 'Comparator.Util', 'ComparatorMain', 'CoreAudit'}

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda: f.read(1048576), b''):
            h.update(b)
    return h.hexdigest()

def load(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))

def write_new(path, obj):
    with Path(path).open('x', encoding='utf-8', newline='\n') as f:
        json.dump(obj, f, ensure_ascii=False, indent=2); f.write('\n')
        f.flush(); os.fsync(f.fileno())

def file_pin(path):
    p = Path(path)
    assert p.is_file()
    return {'path': str(p), 'resolved_path': str(p.resolve()),
            'bytes': p.stat().st_size, 'sha256': sha(p)}

def pins(paths):
    """Pin paths, symlink resolutions and content; hash duplicate targets once."""
    cache, rows = {}, []
    for p in sorted(set(map(Path, paths))):
        assert p.is_file()
        resolved = p.resolve()
        if str(resolved) not in cache:
            cache[str(resolved)] = sha(resolved)
        rows.append({'path': str(p), 'resolved_path': str(resolved),
                     'bytes': p.stat().st_size, 'sha256': cache[str(resolved)]})
    return rows

def verify_pins(rows):
    cache = {}
    for row in rows:
        p = Path(row['path'])
        assert str(p.resolve()) == row['resolved_path'] and p.stat().st_size == row['bytes']
        if row['resolved_path'] not in cache:
            cache[row['resolved_path']] = sha(p)
        assert cache[row['resolved_path']] == row['sha256'], str(p)

def archive_blob(package, member):
    path = ROOT / 'tmp/setup-20261015' / (package + '.tar.gz')
    assert sha(path) == ARCHIVES[package]
    with tarfile.open(path, 'r:gz') as f:
        matches = [m for m in f.getmembers() if m.isfile() and '/'.join(Path(m.name).parts[1:]) == member]
        assert len(matches) == 1
        return f.extractfile(matches[0]).read()

def main():
    setup_started = time.monotonic()
    assert os.name == 'posix' and __debug__
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gate', required=True)
    parser.add_argument('--gate-sha256', required=True)
    args = parser.parse_args()
    gate_path = Path(args.gate).resolve()
    assert gate_path.is_relative_to(ROOT / 'research-goal-20261016/gates')
    assert sha(gate_path) == args.gate_sha256
    gate = load(gate_path)
    assert gate['allow_trusted_native_tools_setup'] is True
    assert gate['all_compiler_and_proof_handles_terminal_confirmed_by_root'] is True
    assert gate['sole_owner'] == '/root' and gate['automatic_retries'] == 0
    assert gate['job_directory'] == str(WORK)
    assert 1 <= gate['setup_timeout_seconds'] <= 3600
    assert sha(PREPARED) == gate['prepared_sha256']
    prepared = load(PREPARED)
    for row in prepared['files'] + prepared['dependencies'] + prepared['external_read_dependencies_not_for_Git']:
        p = ROOT / row['path']
        assert p.stat().st_size == row['bytes'] and sha(p) == row['sha256']
    assert not WORK.exists() and not MIRROR.exists()
    sdk_files = [p for top in ['bin','include','lib'] for p in (SDK/top).rglob('*') if p.is_file()]
    assert sdk_files
    assert sha(SDK / 'bin/lean') == 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
    assert (SDK / '.extracted').read_text().strip() == '48010c7d6264dc992574e9b0e09ece1f9c648e8f5106066b2cdb6834a6a60a6c'
    for n in ['bin/lake','bin/leanc','bin/clang','bin/ld.lld','include/lean/lean.h',
              'lib/lean/libLean.a','lib/lean/libInit.a','lib/lean/libStd.a','lib/lean/libleanrt.a']:
        assert (SDK/n).is_file(), n
    # Installation input closure is pinned independently of later proof timings.
    # It includes the complete SDK bin/include/lib tree, compiler-driver/linker
    # tools, system C headers and GCC support objects potentially read by clang.
    host_roots = [Path('/usr/include'), Path('/usr/lib/gcc')]
    host_files = [p for top in host_roots if top.exists() for p in top.rglob('*') if p.is_file()]
    crt_files = [p for top in [Path('/usr/lib/x86_64-linux-gnu'), Path('/lib/x86_64-linux-gnu')]
                 if top.exists() for pattern in ['crt*.o','Scrt*.o','rcrt*.o'] for p in top.glob(pattern) if p.is_file()]
    binaries = [SDK/'bin'/n for n in ['lean','lake','leanc','clang','ld.lld']]
    binaries += [Path(n) for n in ['/usr/bin/ar','/usr/bin/ld','/usr/bin/cc','/usr/bin/ldd'] if Path(n).is_file()]
    input_pins = pins([*sdk_files, *host_files, *crt_files, *binaries])
    t0 = setup_started; deadline = t0 + gate['setup_timeout_seconds']
    WORK.mkdir(); MIRROR.mkdir(parents=True); (WORK/'source').mkdir(); (WORK/'logs').mkdir(); (WORK/'home').mkdir()
    receipt = {'schema': 'trusted-native-tool-installation-v1', 'started_at_utc': datetime.now(timezone.utc).isoformat(),
        'scope': 'Trusted setup before any new proof timer; no candidate compilation/export/replay',
        'gate_sha256': args.gate_sha256, 'prepared_sha256': gate['prepared_sha256'],
        'SDK_and_C_toolchain_input_pins': input_pins, 'source_provenance': {},
        'setup_timeout_seconds': gate['setup_timeout_seconds'], 'automatic_retries': 0,
        'passed': False, 'proof_runs': 0, 'official_website_acceptance': False}
    def remaining():
        left = deadline - time.monotonic()
        if left <= 0:
            raise TimeoutError('Trusted setup deadline expired')
        return left
    env = {'PATH': str(SDK/'bin') + ':/usr/bin:/bin', 'HOME': str(WORK/'home'),
           'LEAN_SYSROOT': str(SDK), 'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8'}
    def command(label, argv):
        remaining()
        log = WORK/'logs'/(label+'.log')
        start = time.monotonic()
        with log.open('xb') as out:
            proc = subprocess.Popen(argv, cwd=WORK, env=env, stdout=out, stderr=subprocess.STDOUT, start_new_session=True)
            try:
                code = proc.wait(timeout=remaining())
            except BaseException:
                try:
                    os.killpg(proc.pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
                try:
                    proc.wait(timeout=15)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL); proc.wait(timeout=5)
                raise
        item = {'command': argv, 'exit_code': code, 'elapsed_seconds': time.monotonic()-start,
                'log': str(log), 'log_sha256': sha(log)}
        receipt.setdefault('commands', []).append(item)
        write_new(WORK/'logs'/(label+'.json'), item)
        assert code == 0, (label, code)
        return log
    try:
        for package, names in SOURCE_FILES.items():
            for name in names:
                data = archive_blob(package, name)
                output = ('ExporterMain.lean' if package == 'lean4export' else 'ComparatorMain.lean') if name == 'Main.lean' else name
                target = WORK/'source'/output; target.parent.mkdir(parents=True, exist_ok=True)
                with target.open('xb') as f:
                    f.write(data)
                receipt['source_provenance'][output] = {'package': package, 'archive_member': name,
                    'archive_sha256': ARCHIVES[package], 'source_sha256': hashlib.sha256(data).hexdigest()}
            license_data = archive_blob(package, 'LICENSE')
            (WORK/'licenses').mkdir(exist_ok=True)
            with (WORK/'licenses'/(package+'-LICENSE')).open('xb') as f:
                f.write(license_data)
        audit = ROOT/'tools/ComparatorCoreAudit.lean'
        assert sha(audit) == '7e88e84d1d35d5f3115c97a574cc64dd089ef713ef6f9bccb2303fbd41e07ff2'
        with (WORK/'source/CoreAudit.lean').open('xb') as f:
            f.write(audit.read_bytes())
        receipt['source_provenance']['CoreAudit.lean'] = {'path': str(audit), 'source_sha256': sha(audit)}
        actual_modules = {'.'.join(p.relative_to(WORK/'source').with_suffix('').parts) for p in (WORK/'source').rglob('*.lean')}
        assert actual_modules == EXPECTED_MODULES
        for p in (WORK/'source').rglob('*.lean'):
            imported = set(re.findall(r'^import\s+(\S+)', p.read_text(encoding='utf-8'), re.M))
            assert imported <= EXPECTED_MODULES | {'Lean'}
        lakefile = (HERE/'lakefile.toml.in').read_bytes()
        config = tomllib.loads(lakefile.decode())
        assert 'require' not in config and len(config['lean_exe']) == 2
        assert config['lean_exe'][0]['supportInterpreter'] is True
        assert config['lean_exe'][1]['supportInterpreter'] is False
        with (WORK/'lakefile.toml').open('xb') as f:
            f.write(lakefile)
        with (WORK/'lean-toolchain').open('x') as f:
            f.write('leanprover/lean4:v4.33.0-rc2\n')
        write_new(WORK/'lake-manifest.json', {'version': '1.1.0', 'packagesDir': '.lake/packages',
            'packages': [], 'name': 'TinyTrustedNativeTools', 'lakeDir': '.lake'})
        source_pins = pins([*(WORK/'source').rglob('*.lean'), WORK/'lakefile.toml', WORK/'lean-toolchain'])
        write_new(WORK/'setup-started.json', receipt)
        # Exact absolute SDK lake; no elan proxy, require, update, Git checkout,
        # source cache, inherited LEAN_PATH/CC/CFLAGS/LD_PRELOAD or user modules.
        command('sdk-lake-version', [str(SDK/'bin/lake'), '--version'])
        command('sdk-clang-version', [str(SDK/'bin/clang'), '--version'])
        command('lake-build-native', [str(SDK/'bin/lake'), '-v', 'build', 'lean4export', 'coreaudit'])
        assert load(WORK/'lake-manifest.json')['packages'] == []
        package_dir = WORK/'.lake/packages'
        assert not package_dir.exists() or not any(package_dir.iterdir())
        outputs = [WORK/'.lake/build/bin/lean4export', WORK/'.lake/build/bin/coreaudit']
        for p in outputs:
            with p.open('rb') as f:
                assert f.read(4) == b'\x7fELF' and os.access(p, os.X_OK)
        closure_paths = [*outputs]
        ldd_logs = []
        for n, p in enumerate([*outputs, *binaries]):
            with p.open('rb') as f:
                if f.read(4) != b'\x7fELF':
                    continue  # ldd itself can be a script; its bytes are already bound.
            log = command('ldd-'+str(n), ['/usr/bin/ldd', str(p)])
            text = log.read_text(encoding='utf-8', errors='replace')
            assert 'not found' not in text
            for line in text.splitlines():
                match = re.search(r'(?:=>\s*)?(/[^\s]+)', line)
                if match:
                    dependency = Path(match[1])
                    assert dependency.is_file()
                    closure_paths.append(dependency)
            ldd_logs.append(str(log))
        runtime_pins = pins(closure_paths)
        artifacts = pins([p for p in (WORK/'.lake/build').rglob('*') if p.is_file()])
        assert any(Path(r['path']).suffix == '.c' for r in artifacts)
        assert any(Path(r['path']).suffix in {'.o','.export'} for r in artifacts)
        verify_pins(source_pins); verify_pins(input_pins); verify_pins(runtime_pins)
        receipt.update({'passed': True, 'source_pins': source_pins,
            'native_executables': {'lean4export': file_pin(outputs[0]), 'coreaudit': file_pin(outputs[1])},
            'native_runtime_closure_pins': runtime_pins, 'ldd_logs': ldd_logs,
            'all_generated_C_objects_oleans_and_native_artifact_pins': artifacts,
            'complete_source_and_SDK_C_toolchain_unchanged': True,
            'no_external_Lake_packages_or_network_fetch_configured': True,
            'user_oleans_compiled_or_reused': False,
            'elapsed_setup_seconds': time.monotonic()-t0,
            'future_proof_timer_must_include_native_binary_and_closure_hash_checks': True})
        remaining(); write_new(WORK/'installation.json', receipt)
        write_new(MIRROR/'installation.json', receipt)
        print(json.dumps({'trusted_native_tools_installed': True,
            'installation_receipt': str(WORK/'installation.json'),
            'installation_sha256': sha(WORK/'installation.json'), 'proof_runs': 0}), flush=True)
    except BaseException as error:
        receipt.update({'passed': False, 'error_type': type(error).__name__, 'error': str(error),
                        'elapsed_setup_seconds': time.monotonic()-t0})
        write_new(WORK/'failure.json', receipt); write_new(MIRROR/'failure.json', receipt)
        raise

if __name__ == '__main__':
    main()
