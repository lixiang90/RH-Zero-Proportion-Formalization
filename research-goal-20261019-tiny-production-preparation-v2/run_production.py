"""Fail-closed cold tiny verification. PREPARED ONLY; requires a new root gate.

Run under Linux/WSL Python. A single monotonic deadline begins before any input
checks and before the one Windows-Python source-generation call. No resume,
cached user olean, retry, repair, website request or submission is implemented.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import sys
import tarfile
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PREPARED = HERE / 'prepared-files.json'
CONFIG = HERE / 'configuration.json'
BUDGET = 3200.0
FILE_LIMIT = 8 * 1024 ** 3
ROOTS = ['candidate_strict_improvement', 'candidate_critical_line_bound',
         'candidate_critical_line_bound_cumulative']
ALLOWED = ['propext', 'Quot.sound', 'Classical.choice']
PRIMITIVES = ['Nat', 'String', 'String.mk', 'Char', 'Quot', 'Quot.mk', 'Quot.lift',
              'Quot.ind', *ALLOWED, 'Nat.add', 'Nat.sub', 'Nat.mul', 'Nat.pow',
              'Nat.gcd', 'Nat.div', 'Nat.mod', 'Nat.beq', 'Nat.ble', 'Nat.land',
              'Nat.lor', 'Nat.xor', 'Nat.shiftLeft', 'Nat.shiftRight', 'String.ofList',
              'Char.ofNat', 'List', 'eagerReduce']

def load(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))

def write_new(path, obj):
    path = Path(path)
    with path.open('x', encoding='utf-8', newline='\n') as f:
        json.dump(obj, f, ensure_ascii=False, indent=2); f.write('\n')
        f.flush(); os.fsync(f.fileno())

def raw_sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''):
            h.update(block)
    return h.hexdigest()

class Attempt:
    def __init__(self, args):
        self.t0 = time.monotonic()
        self.deadline = self.t0 + BUDGET
        self.args = args
        self.work = Path('/var/tmp/rh-zero-20261015/tiny-production-v2')
        self.mirror = ROOT / 'tmp/current-s1r-tiny-20261018/production-v2'
        self.receipt = {'schema': 'tiny-cold-production-result-v3',
            'started_at_utc': datetime.now(timezone.utc).isoformat(),
            'monotonic_t0': self.t0, 'budget_seconds': BUDGET,
            'timer_scope': 'Before all pin checks and generation through final hashes and fsynced receipts',
            'official_website_acceptance': False, 'submitted': False,
            'local_single_file_verified': False, 'failed': False,
            'retry_count': 0, 'cached_user_oleans_used': False,
            'stages': [], 'stage': 'gate-and-pins'}
        self.bound = {}
        self.active = None
        self.setup_done = False
        self.native_resolutions = {}
        self.native_binaries = {}

    def remaining(self):
        left = self.deadline - time.monotonic()
        if left <= 0:
            raise TimeoutError('The single generation-through-receipt 3200 second deadline expired')
        return left

    def sha(self, path):
        h = hashlib.sha256()
        with Path(path).open('rb') as f:
            for block in iter(lambda: f.read(1048576), b''):
                self.remaining(); h.update(block)
        return h.hexdigest()

    def bind(self, path, expected):
        path = Path(path).resolve()
        assert self.sha(path) == expected, str(path)
        self.bound[str(path)] = expected

    def immutable(self):
        for original, resolved in self.native_resolutions.items():
            assert str(Path(original).resolve()) == resolved, 'A native runtime symlink changed'
        for name, expected in self.bound.items():
            assert self.sha(name) == expected, 'A bound input/artifact changed: ' + name

    def limits(self):
        resource.setrlimit(resource.RLIMIT_FSIZE, (FILE_LIMIT, FILE_LIMIT))
        resource.setrlimit(resource.RLIMIT_STACK, (256 * 1024 ** 2, 256 * 1024 ** 2))

    def windows_cleanup(self):
        pidfile = self.mirror / 'windows-generator.pid.json'
        if not pidfile.exists():
            return
        pid = load(pidfile)['pid']
        assert isinstance(pid, int) and pid > 0
        # Only the PID emitted by our exclusive helper is addressed.
        subprocess.run(['/mnt/c/Windows/System32/taskkill.exe', '/PID', str(pid), '/T', '/F'],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=15)

    def stop_tree(self, proc, windows=False):
        started = time.monotonic()
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        if windows:
            try:
                self.windows_cleanup()
            except (OSError, subprocess.SubprocessError, AssertionError) as e:
                self.receipt['windows_cleanup_error'] = repr(e)
        try:
            proc.wait(timeout=max(0.01, 15 - (time.monotonic() - started)))
        except subprocess.TimeoutExpired:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.wait(timeout=5)
        self.receipt['cleanup_seconds_outside_proof_budget'] = time.monotonic() - started

    def run(self, label, command, *, env=None, stdin=None, output=None, windows=False):
        left = self.remaining()
        log = self.work / 'logs' / (label + '.log')
        stats = self.work / 'logs' / (label + '.resources.txt')
        record = {'label': label, 'command': command, 'cwd': str(self.work),
                  'timeout_seconds_remaining_from_total': left,
                  'started_monotonic': time.monotonic(), 'log': str(log),
                  'resources': str(stats)}
        self.receipt['stage'] = label
        self.receipt['stages'].append(record)
        print(json.dumps({'starting': label, 'remaining_seconds': round(left, 3)}), flush=True)
        inp = Path(stdin).open('rb') if stdin else subprocess.DEVNULL
        out = Path(output).open('xb') if output else log.open('xb')
        err = log.open('xb') if output else out
        proc = None
        try:
            proc = subprocess.Popen(['/usr/bin/time', '-v', '-o', str(stats), *command],
                cwd=self.work, env=env, stdin=inp, stdout=out, stderr=err,
                start_new_session=True, preexec_fn=self.limits)
            self.active = proc
            record['pid'] = proc.pid
            write_new(self.work / 'logs' / (label + '.started.json'), record)
            code = proc.wait(timeout=self.remaining())
            record['exit_code'] = code
        except BaseException:
            if proc is not None:
                self.stop_tree(proc, windows=windows)
                record['exit_code'] = proc.returncode
            raise
        finally:
            self.active = None
            if stdin:
                inp.close()
            out.close()
            if err is not out:
                err.close()
            record['elapsed_seconds'] = time.monotonic() - record['started_monotonic']
            if proc is not None:
                write_new(self.work / 'logs' / (label + '.terminal.json'), record)
        self.remaining()
        record['log_sha256'] = self.sha(log)
        text = stats.read_text(encoding='utf-8', errors='replace')
        match = re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)', text)
        record['max_rss_kib'] = int(match[1]) if match else None
        if output:
            record.update({'output': str(output), 'output_bytes': Path(output).stat().st_size,
                           'output_sha256': self.sha(output)})
        assert code == 0, f'{label} failed with exit {code}; no retry or source repair'
        return record

    def lean_command(self, *arguments):
        return [self.lean, '-j1', '--tstack=32768', '-DrelaxedAutoImplicit=false', *map(str, arguments)]

    def environment(self, paths):
        return {'PATH': str(Path(self.lean).parent) + ':/usr/bin:/bin',
                'LEAN_PATH': ':'.join(map(str, paths)), 'HOME': '/var/tmp/rh-zero-20261015',
                'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8',
                'LEAN_SYSROOT': str(Path(self.lean).parent.parent)}

    def archive_blob(self, package, name):
        archive = ROOT / 'tmp/setup-20261015' / (package + '.tar.gz')
        with tarfile.open(archive, 'r:gz') as stream:
            members = [m for m in stream.getmembers() if m.isfile()
                       and '/'.join(Path(m.name).parts[1:]) == name]
            assert len(members) == 1, (package, name)
            return stream.extractfile(members[0]).read()

    def bind_native_tools(self, gate, config):
        """Bind a root-confirmed successful preinstalled native setup under t0."""
        selected = gate['trusted_native_tools']
        assert selected['root_confirmed_setup_terminal_exit_code'] == 0
        install_path = Path(selected['installation_path']).resolve()
        native_root = install_path.parent
        assert install_path.name == 'installation.json'
        assert native_root.parent == Path('/var/tmp/rh-zero-20261015')
        assert re.fullmatch(r'tiny-native-tools-v[0-9]+', native_root.name)
        setup_prepared = (ROOT / selected['setup_prepared_path']).resolve()
        assert setup_prepared.is_relative_to(ROOT) and setup_prepared.name == 'prepared-files.json'
        self.bind(setup_prepared, selected['setup_prepared_sha256'])
        self.bind(install_path, selected['installation_sha256'])
        install = load(install_path)
        assert install['schema'] == 'trusted-native-tool-installation-v1'
        assert install['prepared_sha256'] == selected['setup_prepared_sha256']
        assert install['passed'] is True and install['proof_runs'] == 0
        assert install['automatic_retries'] == 0
        assert install['complete_source_and_SDK_C_toolchain_unchanged'] is True
        assert install['no_external_Lake_packages_or_network_fetch_configured'] is True
        assert install['user_oleans_compiled_or_reused'] is False
        assert install['official_website_acceptance'] is False
        native_mirror = ROOT / 'tmp/current-s1r-tiny-20261018' / native_root.name.removeprefix('tiny-')
        assert not (native_root / 'failure.json').exists() and not (native_mirror / 'failure.json').exists()
        self.bind(native_mirror / 'installation.json', selected['installation_sha256'])
        expected = {}
        for package, names in {
            'lean4export': ['Export.lean', 'Export/Parse.lean', 'Main.lean'],
            'Comparator': ['Comparator.lean', 'Comparator/Axioms.lean', 'Comparator/Compare.lean',
                           'Comparator/Util.lean', 'Main.lean']}.items():
            for name in names:
                dest = ('ExporterMain.lean' if package == 'lean4export' else 'ComparatorMain.lean') if name == 'Main.lean' else name
                expected[dest] = hashlib.sha256(self.archive_blob(package, name)).hexdigest()
        expected['CoreAudit.lean'] = '7e88e84d1d35d5f3115c97a574cc64dd089ef713ef6f9bccb2303fbd41e07ff2'
        assert set(install['source_provenance']) == set(expected)
        for name, digest in expected.items():
            assert install['source_provenance'][name]['source_sha256'] == digest
        source_paths = {str(native_root / 'source' / p) for p in expected}
        source_paths |= {str(native_root / 'lakefile.toml'), str(native_root / 'lean-toolchain')}
        assert {r['path'] for r in install['source_pins']} == source_paths
        for row in install['source_pins']:
            path = Path(row['path'])
            assert str(path.resolve()) == row['resolved_path']
            assert path.stat().st_size == row['bytes']
            self.bind(path, row['sha256'])
            self.native_resolutions[str(path)] = row['resolved_path']
        assert self.sha(native_root / 'lakefile.toml') == self.sha(ROOT / config['native_lakefile_template'])
        assert (native_root / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.0-rc2'
        assert set(install['native_executables']) == {'lean4export', 'coreaudit'}
        self.native_binaries = {}
        for name in ['lean4export', 'coreaudit']:
            row = install['native_executables'][name]
            path = native_root / '.lake/build/bin' / name
            assert row['path'] == str(path) and str(path.resolve()) == row['resolved_path']
            assert path.stat().st_size == row['bytes'] and os.access(path, os.X_OK)
            with path.open('rb') as f:
                assert f.read(4) == b'\x7fELF'
            self.bind(path, row['sha256'])
            self.native_resolutions[str(path)] = row['resolved_path']
            self.native_binaries[name] = str(path)
        runtime_paths = {r['path'] for r in install['native_runtime_closure_pins']}
        assert set(self.native_binaries.values()) <= runtime_paths
        for row in install['native_runtime_closure_pins']:
            path = Path(row['path'])
            assert str(path.resolve()) == row['resolved_path'] and path.stat().st_size == row['bytes']
            self.bind(path, row['sha256'])
            self.native_resolutions[str(path)] = row['resolved_path']
        for cmd in install['commands']:
            assert cmd['exit_code'] == 0
        self.receipt['trusted_native_tools'] = {
            'installation_path': str(install_path), 'installation_sha256': selected['installation_sha256'],
            'setup_prepared_path': str(setup_prepared), 'setup_prepared_sha256': selected['setup_prepared_sha256'],
            'native_executables': install['native_executables'],
            'native_runtime_closure_pins': install['native_runtime_closure_pins'],
            'source_provenance': install['source_provenance'],
            'runtime_symlink_resolutions': self.native_resolutions,
            'setup_was_prior_to_this_proof_timer': True,
            'trusted_tools_recompiled_in_this_proof_attempt': False,
            'user_oleans_reused': False}
        self.receipt['tool_compiled_modules'] = []


    def source(self, folder, relative, data):
        target = folder / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as f:
            f.write(data)
        self.bind(target, hashlib.sha256(data).hexdigest())

    def compile(self, folder, module, paths, prefix):
        rel = Path(*module.split('.'))
        source = (folder / 'source' / rel).with_suffix('.lean')
        output = (folder / 'lib' / rel).with_suffix('.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        record = self.run(prefix + module, self.lean_command('-R', folder / 'source',
                          '-o', output, '-i', output.with_suffix('.ilean'), source),
                          env=self.environment(paths))
        record.update({'module': module, 'source_sha256': self.sha(source),
                       'olean_sha256': self.sha(output)})
        self.bind(output, record['olean_sha256'])
        return record

    def execute(self):
        assert os.name == 'posix' and __debug__
        assert ROOT == Path('/mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization')
        gate_path = Path(self.args.gate).resolve()
        assert gate_path.is_relative_to(ROOT / 'research-goal-20261016/gates')
        gate = load(gate_path)
        assert self.sha(gate_path) == self.args.gate_sha256
        assert gate['allow_production_execution'] is True
        assert gate['total_budget_seconds'] == 3200 and gate['automatic_retries'] == 0
        assert gate['job_directory'] == str(self.work)
        assert gate['original_ordinary_final_all_six_roots_passed'] is True
        assert gate['sole_owner']
        self.bind(PREPARED, gate['prepared_sha256'])
        prepared = load(PREPARED)
        for row in prepared['files'] + prepared['dependencies']:
            self.bind(ROOT / row['path'], row['sha256'])
        config = load(CONFIG)
        assert gate['flatten_prepared_sha256'] == config['flatten_prepared_sha256']
        assert gate['production_source_prepared_sha256'] == config['production_source_prepared_sha256']
        recheck = gate['fresh_record_recheck']
        recheck_path = (ROOT / recheck['path']).resolve()
        assert recheck_path.is_relative_to(ROOT)
        self.bind(recheck_path, recheck['sha256'])
        fresh_recheck = load(recheck_path)
        assert fresh_recheck['status'] == 200
        assert fresh_recheck['current']['exactRational'] == config['expected_current_record']
        previous_failure = load(ROOT / config['previous_failure_receipt'])
        assert previous_failure['failed'] is True and previous_failure['local_single_file_verified'] is False
        assert previous_failure['stage'] == 'nanoda'
        self.receipt['fresh_record_recheck'] = recheck
        self.receipt['previous_failed_attempt_sha256'] = config['previous_failure_receipt_sha256']
        self.receipt['deduplicated_production_source_prepared_sha256'] = config['production_source_prepared_sha256']
        self.receipt['local_nanoda_threads'] = 0
        self.receipt['locked_official_Comparator_default_nanoda_is_serial'] = True
        self.receipt['official_runtime_equivalence_claimed'] = False
        assert not self.work.exists() and not self.mirror.exists()
        self.work.mkdir(); self.mirror.mkdir(parents=True)
        (self.work / 'logs').mkdir(); (self.work / 'lib').mkdir()
        self.setup_done = True
        self.receipt.update({'gate_path': str(gate_path), 'gate_sha256': self.args.gate_sha256,
            'prepared_sha256': gate['prepared_sha256'], 'sole_owner': gate['sole_owner'],
            'RLIMIT_FSIZE_bytes': FILE_LIMIT, 'RAM_limit_claimed': False})
        self.bind(gate_path, self.args.gate_sha256)
        self.lean = config['lean']
        self.bind(self.lean, config['lean_sha256'])
        self.bind(config['nanoda'], config['nanoda_sha256'])
        self.bind(config['Windows_Python_Linux_path'], config['Windows_Python_sha256'])
        self.bind(config['Windows_Python_DLL_Linux_path'], config['Windows_Python_DLL_sha256'])
        self.bind_native_tools(gate, config)
        runtime = load(ROOT / 'tmp/setup-20261015/runtime.json')
        assert runtime['lean'] == self.lean
        self.packages = runtime['lean_path'].split(':')
        package_root = Path(runtime['package_root'])
        assert self.packages and all(Path(p).resolve().is_relative_to(package_root)
                                    and Path(p).is_dir() for p in self.packages)
        for row in config['external_dependency_cache_pins']:
            self.bind(row['path'], row['sha256'])
        forbidden = ['ChallengeDeps.olean', 'ChallengeDeps/CandidateSpec.olean',
                     'Challenge/Candidate.olean', 'Solution/Candidate.olean']
        assert not any((Path(p) / name).exists() for p in self.packages for name in forbidden)
        self.run('compiler-version', [self.lean, '--version'], env=self.environment(self.packages))
        version = (self.work / 'logs/compiler-version.log').read_text()
        assert config['lean_version'] in version
        # This is the only source-generator execution, under the already-running total timer.
        self.run('generation', [config['Windows_Python_Linux_path'], '-B', '-X', 'utf8',
            config['Windows_helper_path'], '--gated-generator-once', config['flatten_prepared_sha256']],
            env=os.environ.copy(), windows=True)
        flatten = ROOT / config['flatten_directory']
        solution = flatten / 'draft/Solution.lean'
        generated = load(flatten / 'draft/candidate-metadata.json')
        assert solution.stat().st_size == generated['solution_bytes'] <= 2_000_000
        assert generated['prepared_manifest_sha256'] == config['flatten_prepared_sha256']
        self.bind(solution, generated['solution_sha256'])
        for p in [flatten / 'draft/generation.json', flatten / 'draft/candidate-metadata.json']:
            self.bind(p, self.sha(p))
        rows = load(ROOT / config['current_record_ledger'])
        current = [r for r in rows if r['status'] == 'kernel-verified' and r['track'] == 'critical-line'][-1]
        assert current['exactRational'] == config['expected_current_record']
        fresh = load(ROOT / config['latest_record_receipt'])
        assert fresh['status'] == 200 and fresh['current']['exactRational'] == current['exactRational']
        ordinary = load(ROOT / 'tmp/current-s1r-tiny-20261018/phase4-v0/Final.receipt.json')
        assert ordinary['ordinary_compile_passed'] and ordinary['axiom_audit_passed']
        assert ordinary['source_sha256'] == 'd477fd3181e0d4d5a3c89bcbcb987dd6cad00fbdde1946d01c26ac0c279489ed'
        assert len(ordinary['printed_roots']) == 6
        assert all(set(r['axioms']) <= set(ALLOWED) for r in ordinary['printed_roots'])
        plan = load(flatten / 'candidate-parameters.json')
        assert plan['score'] == config['score']
        p, q = map(int, (plan['score']['numerator'], plan['score']['denominator']))
        a, b = map(int, (current['exactRational']['numerator'], current['exactRational']['denominator']))
        assert 0 < Fraction(a, b) < Fraction(p, q) <= 1
        spec = (ROOT / config['candidate_template']).read_text(encoding='utf-8')
        assert spec.count('{{CURRENT_EXPRESSION}}') == spec.count('{{NUMERATOR}}') == spec.count('{{DENOMINATOR}}') == 1
        spec = spec.replace('{{CURRENT_EXPRESSION}}', current['exactExpression'])
        spec = spec.replace('{{NUMERATOR}}', str(p)).replace('{{DENOMINATOR}}', str(q))
        self.source(self.work / 'source', 'ChallengeDeps.lean', self.archive_blob('Zeta23', 'comparator/ChallengeDeps.lean'))
        self.source(self.work / 'source', 'ChallengeDeps/CandidateSpec.lean', spec.encode('utf-8'))
        self.source(self.work / 'source', 'Challenge/Candidate.lean', (ROOT / config['challenge_template']).read_bytes())
        self.source(self.work / 'source', 'Solution/Candidate.lean', solution.read_bytes())
        modules = ['ChallengeDeps', 'ChallengeDeps.CandidateSpec', 'Challenge.Candidate', 'Solution.Candidate']
        assert {str(x.relative_to(self.work / 'source')) for x in (self.work / 'source').rglob('*.lean')} == {
            str(Path(*m.split('.')).with_suffix('.lean')) for m in modules}
        assert not list((self.work / 'lib').rglob('*'))
        paths = [self.work / 'lib', *self.packages]
        self.receipt['compiled_modules'] = [self.compile(self.work, m, paths, 'ordinary-') for m in modules]
        self.receipt['ordinary_single_file_lean_passed'] = True
        toolpaths = paths  # Native tools need no trusted-tool/user olean overlay.
        self.immutable()
        exports = {}
        for label, module in [('challenge', 'Challenge.Candidate'), ('solution', 'Solution.Candidate')]:
            target = self.work / (label + '.ndjson')
            exports[label] = self.run(label + '-export',
                [self.native_binaries['lean4export'], module, '--', *ROOTS, *PRIMITIVES],
                env=self.environment(toolpaths), output=target)
            self.bind(target, exports[label]['output_sha256'])
        self.receipt['exports'] = exports
        self.run('comparator-default-kernel',
            [self.native_binaries['coreaudit'], str(self.work / 'challenge.ndjson'),
             str(self.work / 'solution.ndjson'), *ROOTS], env=self.environment(toolpaths))
        text = (self.work / 'logs/comparator-default-kernel.log').read_text(encoding='utf-8', errors='replace')
        for sentence in ['Pinned Comparator statement, dependency and primitive comparison passed',
                         'Pinned Comparator transitive axiom check passed', 'Lean default kernel replay passed']:
            assert sentence in text
        self.receipt.update({'statement_equality_proved': True, 'permitted_axioms_checked': True,
                             'default_kernel_replay_passed': True})
        nano_config = {'use_stdin': True, 'permitted_axioms': ALLOWED,
            'unpermitted_axiom_hard_error': True, 'nat_extension': True, 'string_extension': True,
            'num_threads': 0, 'unsafe_permit_all_axioms': False, 'print_success_message': True,
            'print_axioms': True, 'pp_to_stdout': True}
        write_new(self.work / 'nanoda-config.json', nano_config)
        self.bind(self.work / 'nanoda-config.json', self.sha(self.work / 'nanoda-config.json'))
        self.run('nanoda', [config['nanoda'], str(self.work / 'nanoda-config.json')],
                 env=self.environment(toolpaths), stdin=self.work / 'solution.ndjson')
        text = (self.work / 'logs/nanoda.log').read_text(encoding='utf-8', errors='replace')
        count = re.search(r'Checked (\d+) declarations with no errors', text)
        assert count
        observed = [n.split('.{')[0] for n in re.findall(r'^axiom ([^\s]+)', text, re.M)]
        assert set(observed) <= set(ALLOWED)
        self.immutable()
        self.receipt.update({'stage': 'all-proof-stages-passed', 'independent_nanoda_passed': True,
            'checked_declarations': int(count[1]), 'observed_axioms': observed,
            'bound_sha256_before_and_after': self.bound, 'inputs_unchanged': True,
            'source_bytes': solution.stat().st_size, 'source_sha256': self.sha(solution),
            'score': plan['score'], 'current_record': current,
            'disk_bytes': sum(p.stat().st_size for p in self.work.rglob('*') if p.is_file()),
            'peak_stage_rss_kib': max(x.get('max_rss_kib') or 0 for x in self.receipt['stages']),
            'proof_stages_elapsed_seconds': time.monotonic() - self.t0})
        self.remaining()
        self.receipt['local_single_file_verified'] = True
        self.receipt['total_deadline_enforced'] = True
        write_new(self.work / 'verification.json', self.receipt)
        self.remaining()
        final = {'elapsed_seconds_after_fsynced_verification_receipt': time.monotonic() - self.t0,
            'verification_receipt_sha256': self.sha(self.work / 'verification.json'),
            'total_limit_seconds': BUDGET, 'within_total_limit': True,
            'official_website_acceptance': False}
        write_new(self.work / 'deadline-receipt.json', final)
        self.remaining()
        write_new(self.mirror / 'terminal.json', {'linux_work_directory': str(self.work), **final})
        self.remaining()
        print(json.dumps({'local_single_file_verified': True,
            'total_elapsed_seconds_through_all_receipts': time.monotonic() - self.t0,
            'official_website_acceptance': False}), flush=True)

    def failure(self, error):
        self.receipt.update({'failed': True, 'local_single_file_verified': False,
            'error_type': type(error).__name__, 'error': str(error),
            'total_elapsed_seconds_at_failure': time.monotonic() - self.t0})
        if self.setup_done:
            write_new(self.work / 'failure.json', self.receipt)
            write_new(self.mirror / 'failure.json', self.receipt)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gate', required=True)
    parser.add_argument('--gate-sha256', required=True)
    args = parser.parse_args()
    def interrupted(signum, frame):
        raise KeyboardInterrupt('Received signal ' + str(signum))
    signal.signal(signal.SIGTERM, interrupted)
    attempt = Attempt(args)
    try:
        attempt.execute()
    except BaseException as error:
        attempt.failure(error)
        raise

if __name__ == '__main__':
    main()
