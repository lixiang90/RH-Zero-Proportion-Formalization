"""Fresh, gated W9A2 full-chain verification; PREPARED ONLY, NOT EXECUTED.

One deadline covers pins, deterministic source reconstruction, exact trusted
spec, fresh ordinary compilation, both native exports, the unmodified pinned
Comparator CoreAudit/default Lean replay, serial nanoda and fsynced receipts.
No repair, retry, resume, user-olean reuse, installation, network or submission.
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
import signal
import subprocess
import sys
import time
import traceback

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
BUDGET = 3200.0
ALLOWED = ['propext', 'Quot.sound', 'Classical.choice']
TARGETS = ['candidate_strict_improvement', 'candidate_critical_line_bound',
           'candidate_critical_line_bound_cumulative']
PRIMITIVES = ['Nat', 'String', 'String.mk', 'Char', 'Quot', 'Quot.mk', 'Quot.lift',
              'Quot.ind', *ALLOWED, 'Nat.add', 'Nat.sub', 'Nat.mul', 'Nat.pow',
              'Nat.gcd', 'Nat.div', 'Nat.mod', 'Nat.beq', 'Nat.ble', 'Nat.land',
              'Nat.lor', 'Nat.xor', 'Nat.shiftLeft', 'Nat.shiftRight', 'String.ofList',
              'Char.ofNat', 'List', 'eagerReduce']
CORE_AUDIT_SHA = '7e88e84d1d35d5f3115c97a574cc64dd089ef713ef6f9bccb2303fbd41e07ff2'
TOOL_COMMITS = {'Comparator':'273294467ce06429e6667ece7f5699f8678c9f4e',
                'lean4export':'b18d673bd29b476466a51a3be1012df2ed322b10',
                'nanoda':'418320295890faed83a96fd97907b12a3b6728c2'}
TOOL_SOURCE_LF_SHA = {
    'Comparator/Comparator.lean':'6c73ecd5bd429cf85e0aaa75b7c6f874ec0598d5afca60dcf5711d44e6bdef23',
    'Comparator/Comparator/Axioms.lean':'863c5e1329811be0427880e08c171de733343491c5a3619b5dbf2e12b34c6125',
    'Comparator/Comparator/Compare.lean':'9bc34cb7de5a069a6fef7f3b13b20fea22f1d52603f74320a93d519b735ad3dd',
    'Comparator/Comparator/Util.lean':'693d845330dd7122565aeb19314a3e3de4b49f9a8a7ac6e1fadbc9ab374b9f88',
    'Comparator/Main.lean':'d6474f7ac49cf7a1c2f24aff6ac2bcc97a4a00aa37b969f225c6e688c434d0b4',
    'lean4export/Export.lean':'1c60d571dc24bfb99e7cbb218d8d489919bbc871238f6db9c76248521fbea998',
    'lean4export/Export/Parse.lean':'1f943b5cc776eece6d528937b976509c8bd57d10bc69a39b1c119bfb6d664286',
    'lean4export/Main.lean':'bd8e350903f1382b25fe767f9086dd9882000f01085f7046ea06545e7848842a'}
MODULE_NAMES = [f'StructuralW9A220261020.{n}' for n in
                ['Core', 'Graph', 'Localization', 'Counting', 'Final']]
IMPORT = re.compile(rb'import ([A-Za-z_][A-Za-z0-9_.]*)\r?\n?\Z')
HEADER = b'''/-
SPDX-License-Identifier: Apache-2.0
PREPARATION ONLY. Frozen W9A2 quantitative localization and finite-state
average-energy candidate. All non-import bytes and inherited notices survive.
Ordinary Lean, exact Comparator comparison, default kernel replay, nanoda,
the complete 3200s production budget and website acceptance remain unproved.
-/
'''


def load(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


def fail_unless(condition, message):
    if not condition:
        raise RuntimeError(message)


class Attempt:
    def __init__(self, t0, args):
        self.t0, self.deadline, self.args = t0, t0+BUDGET, args
        self.work = None
        self.active = None
        self.bound = {}
        self.resolutions = {}
        self.output_pins = {}
        self.nano_pidfile = None
        self.receipt = {'schema': 'w9a2-fullchain-verification-v1',
            'started_at_utc': datetime.now(timezone.utc).isoformat(),
            'timer_scope': 'Before gate/pins/source/spec through final hashes and fsynced three receipts',
            'budget_seconds': BUDGET, 'monotonic_t0': t0, 'stages': [],
            'automatic_repairs': 0, 'automatic_retries': 0, 'cached_user_oleans_used': False,
            'official_website_acceptance': False, 'submitted': False,
            'local_fullchain_verified': False, 'failed': False}

    def remaining(self):
        left = self.deadline-time.monotonic()
        if left <= 0:
            raise TimeoutError('The single 3200-second full-chain deadline expired')
        return left

    def sha(self, path):
        digest = hashlib.sha256()
        with Path(path).open('rb') as stream:
            for block in iter(lambda: stream.read(1048576), b''):
                self.remaining()
                digest.update(block)
        self.remaining()
        return digest.hexdigest()

    def path(self, value):
        path = Path(value)
        # Keep the original absolute alias so immutable() can detect symlink retargeting.
        return Path(os.path.abspath(path if path.is_absolute() else ROOT/path))

    def bind(self, path, expected, size=None):
        path = self.path(path)
        fail_unless(path.is_file(), 'Missing pinned input: '+str(path))
        if size is not None:
            fail_unless(path.stat().st_size == size, 'Pinned byte size changed: '+str(path))
        fail_unless(self.sha(path) == expected, 'Pinned SHA changed: '+str(path))
        self.bound[str(path)] = expected
        return path

    def bind_row(self, row):
        path = self.path(row['path'])
        resolved = str(path.resolve())
        if 'resolved_path' in row:
            fail_unless(resolved == row['resolved_path'], 'Pinned link resolution changed')
        self.resolutions[str(path)] = resolved
        return self.bind(path, row['sha256'], row.get('bytes'))

    def immutable(self):
        for name, expected in self.bound.items():
            fail_unless(self.sha(name) == expected, 'Bound input/output changed: '+name)
        for name, expected in self.resolutions.items():
            fail_unless(str(Path(name).resolve()) == expected, 'Pinned file link changed')

    def write_bytes(self, path, data, bind=True):
        self.remaining()
        path = Path(path)
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('xb') as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        self.remaining()
        if bind:
            self.bind(path, hashlib.sha256(data).hexdigest(), len(data))

    def write_json(self, path, data, bind=True):
        self.write_bytes(path, (json.dumps(data, ensure_ascii=False, indent=2)+'\n').encode(), bind)

    def read_log(self, record):
        self.remaining()
        return Path(record['log']).read_text(encoding='utf-8', errors='replace')

    def wsl_command(self, *args):
        return [self.wsl, '--distribution', self.gate['runtime']['wsl_distribution'], '--exec', *args]

    def linux_mapped(self, path):
        path = Path(path).resolve()
        fail_unless(os.name == 'nt' and re.fullmatch('[A-Za-z]:', path.drive) is not None,
                    'Only an absolute local Windows drive path can be mapped into WSL')
        return '/mnt/'+path.drive[0].lower()+str(path)[2:].replace('\\', '/')

    def cleanup(self, proc, record):
        """Only this attempt's process tree/group; bounded cleanup is no proof PASS."""
        start = time.monotonic()
        if proc.poll() is not None:
            return
        if os.name == 'nt':
            if record.get('wsl_nanoda') and self.nano_pidfile and self.nano_pidfile.is_file():
                try:
                    pid = int(self.nano_pidfile.read_text().strip())
                    fail_unless(pid > 1, 'Invalid owned nanoda process-group id')
                    observed = subprocess.run(self.wsl_command('/usr/bin/readlink', '/proc/'+str(pid)+'/exe'),
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=3, check=False)
                    # Refuse to address a reused Linux PID that no longer names our exact binary.
                    if observed.returncode == 0 and observed.stdout.decode().strip() == self.nano['resolved_execution_path']:
                        subprocess.run(self.wsl_command('/bin/kill', '-TERM', '--', '-'+str(pid)),
                                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=3, check=False)
                        again = subprocess.run(self.wsl_command('/usr/bin/readlink', '/proc/'+str(pid)+'/exe'),
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=3, check=False)
                        if again.returncode == 0 and again.stdout.decode().strip() == self.nano['resolved_execution_path']:
                            subprocess.run(self.wsl_command('/bin/kill', '-KILL', '--', '-'+str(pid)),
                                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=3, check=False)
                except (OSError, ValueError, subprocess.SubprocessError, RuntimeError) as error:
                    record['nanoda_group_cleanup_observation'] = repr(error)
            subprocess.run([self.taskkill, '/PID', str(proc.pid), '/T', '/F'],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=5, check=False)
        else:
            try:
                os.killpg(proc.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
        try:
            proc.wait(timeout=3)
        except subprocess.TimeoutExpired:
            if os.name != 'nt':
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            else:
                proc.kill()
            proc.wait(timeout=3)
        record['failure_cleanup_seconds_outside_proof_budget'] = time.monotonic()-start

    def run(self, label, command, *, env=None, stdin=None, output=None, wsl_nanoda=False):
        left = self.remaining()
        fail_unless(re.fullmatch('[A-Za-z0-9_.-]+', label) is not None, 'Invalid stage label')
        log = self.work/'logs'/(label+'.log')
        record = {'label': label, 'argv': list(map(str, command)), 'cwd': str(self.work),
            'started_monotonic': time.monotonic(), 'remaining_total_budget_seconds': left,
            'log': str(log), 'wsl_nanoda': wsl_nanoda}
        self.receipt['stage'] = label
        self.receipt['stages'].append(record)
        self.write_json(self.work/'logs'/(label+'.started.json'), record)
        print(json.dumps({'starting': label, 'remaining_seconds': round(self.remaining(), 3)}), flush=True)
        inp = Path(stdin).open('rb') if stdin else subprocess.DEVNULL
        out = Path(output).open('xb') if output else log.open('xb')
        err = log.open('xb') if output else out
        proc = None
        try:
            options = {'start_new_session': True} if os.name != 'nt' else {
                'creationflags': subprocess.CREATE_NEW_PROCESS_GROUP}
            proc = subprocess.Popen(command, cwd=self.work, env=env,
                stdin=inp, stdout=out, stderr=err, **options)
            self.active = (proc, record)
            record['pid'] = proc.pid
            self.write_json(self.work/'logs'/(label+'.child.json'), {'pid':proc.pid,'argv':record['argv']})
            record['exit_code'] = proc.wait(timeout=self.remaining())
        except BaseException:
            if proc is not None:
                try:
                    self.cleanup(proc, record)
                except (OSError, RuntimeError, subprocess.SubprocessError) as cleanup_error:
                    record['cleanup_error'] = repr(cleanup_error)
                record['exit_code'] = proc.returncode
            raise
        finally:
            self.active = None
            if stdin:
                inp.close()
            out.flush(); os.fsync(out.fileno()); out.close()
            if err is not out:
                err.flush(); os.fsync(err.fileno()); err.close()
            record['elapsed_seconds'] = time.monotonic()-record['started_monotonic']
        self.remaining()
        record['log_sha256'] = self.sha(log)
        self.bind(log, record['log_sha256'])
        if output:
            record.update({'output':str(output),'output_bytes':Path(output).stat().st_size,
                           'output_sha256':self.sha(output)})
            self.bind(output,record['output_sha256'])
        self.write_json(self.work/'logs'/(label+'.terminal.json'), record)
        fail_unless(record['exit_code'] == 0, label+' exited nonzero; no retry or repair')
        return record

    def environment(self, paths):
        runtime = self.gate['runtime']
        # No inherited LEAN_PATH/LEAN_SRC_PATH/plugin/search/preload overrides.
        env = {'PATH': runtime['controlled_path'], 'LEAN_PATH':os.pathsep.join(map(str,paths)),
               'LEAN_SYSROOT':str(self.path(runtime['lean_sysroot'])),
               'HOME':str(self.work/'home'), 'LANG':'C.UTF-8', 'LC_ALL':'C.UTF-8',
               'LEAN_ABORT_ON_PANIC':'1'}
        if os.name == 'nt':
            env.update({'SYSTEMROOT':os.environ['SYSTEMROOT'], 'WINDIR':os.environ['WINDIR'],
                        'TEMP':str(self.work/'temporary'),'TMP':str(self.work/'temporary'),
                        'USERPROFILE':str(self.work/'home')})
        return env

    def setup_gate(self):
        gate_path = self.path(self.args.gate)
        fail_unless(gate_path.is_relative_to(ROOT), 'Gate must be in the workspace')
        self.bind(gate_path, self.args.gate_sha256)
        gate = self.gate = load(gate_path)
        fail_unless(gate['allow_verification_execution'] is True, 'Root execution gate is not enabled')
        fail_unless(gate['schema'] == 'w9a2-fullchain-gate-v1' and gate['sole_owner'], 'Invalid root gate')
        fail_unless(gate['total_budget_seconds'] == BUDGET and gate['automatic_retries'] == 0
                    and gate['automatic_repairs'] == 0 and gate['cached_user_oleans'] is False,
                    'Gate attempts to weaken the fixed full-chain contract')
        self.bind(__file__, gate['runner_sha256'])
        manifest = self.bind(gate['prepared_manifest']['path'], gate['prepared_manifest']['sha256'])
        for row in load(manifest)['files']:
            self.bind(manifest.parent/row['path'], row['sha256'], row['bytes'])
        expected_platform = 'windows-native-wsl-nanoda' if os.name == 'nt' else 'linux-native'
        fail_unless(gate['platform'] == expected_platform, 'Runner platform differs from the gate')
        self.work = self.path(gate['work_directory']).resolve()
        fail_unless(self.work.is_relative_to(ROOT/'tmp') and not self.work.exists(),
                    'Work directory must be a new exclusive directory inside workspace/tmp')
        self.work.mkdir(parents=True, exist_ok=False)
        for name in ['logs','source','lib','home','temporary']:
            (self.work/name).mkdir()
        self.write_json(self.work/'started.json', {'pid':os.getpid(),'gate_sha256':self.args.gate_sha256,
                         'monotonic_t0':self.t0,'budget_seconds':BUDGET,'platform':expected_platform})
        self.receipt.update({'gate_path':str(gate_path),'gate_sha256':self.args.gate_sha256,
                            'sole_owner':gate['sole_owner'],'platform':expected_platform})

    def setup_runtime(self):
        runtime = self.gate['runtime']
        fail_unless(runtime['root_confirmed_setup_terminal_exit_code'] == 0
                    and runtime['root_reviewed_complete_runtime_closure'] is True,
                    'Root has not verified the current source-bound runtime closure and setup exit0')
        manifest_path = self.bind(runtime['closure_manifest']['path'],runtime['closure_manifest']['sha256'])
        manifest = load(manifest_path)
        fail_unless(manifest['schema'] == 'w9a2-trusted-runtime-closure-v1'
                    and manifest['complete_source_bound_runtime_closure_verified'] is True
                    and manifest['user_proofs_compiled_or_reused_in_setup'] is False
                    and manifest['official_runtime_equivalence_claimed'] is False,
                    'Incomplete or wrong-scope trusted runtime closure receipt')
        fail_unless(manifest['files'], 'No runtime files were bound')
        for row in manifest['files']:
            self.bind_row(row)
        allowed_paths = {str(self.path(row['path'])) for row in manifest['files']}
        fail_unless(manifest['tool_commits'] == TOOL_COMMITS, 'Trusted tool source revisions changed')
        source_rows = manifest['trusted_tool_sources']
        fail_unless(len(source_rows) == len(TOOL_SOURCE_LF_SHA) and
                    {row['logical_name'] for row in source_rows} == set(TOOL_SOURCE_LF_SHA),
                    'Incomplete pinned Comparator/Export source closure')
        for row in source_rows:
            tool_source = self.bind_row(row)
            fail_unless(str(tool_source) in allowed_paths and
                        hashlib.sha256(tool_source.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
                        == TOOL_SOURCE_LF_SHA[row['logical_name']], 'Pinned trusted tool source differs')
        expected_packages={'mathlib':'51e6992efd06126df61a496bebf8f49482a4e129',
                           'Zeta23':'3635e74826a4c1fcece7d1cd2b6fa75e43a00510'}
        fail_unless(all(manifest['package_source_revisions'].get(name)==rev
                    for name,rev in expected_packages.items()), 'Mathlib/Zeta23 source revisions changed')
        self.bind_row(manifest['trusted_setup_receipt'])
        controller = self.bind_row(runtime['python_controller'])
        fail_unless(controller.resolve() == Path(sys.executable).resolve()
                    and runtime['python_controller']['version'] == sys.version,
                    'Controller Python executable/version differs from the reviewed closure')
        self.lean = str(self.bind_row(runtime['lean']))
        self.exporter = str(self.bind_row(runtime['native_exporter']))
        self.audit = runtime['coreaudit']
        self.audit_source = self.bind(self.audit['source_path'],CORE_AUDIT_SHA)
        fail_unless(self.audit['mode'] in ['native','interpreted'], 'Unsupported CoreAudit execution mode')
        self.audit_binary = str(self.bind_row(self.audit['binary'])) if self.audit['mode']=='native' else None
        self.nano = runtime['nanoda']
        self.nano_host = self.bind_row(self.nano['host_binary'])
        fail_unless(all(str(p) in allowed_paths for p in [Path(self.lean),Path(self.exporter),
                    self.nano_host,*([Path(self.audit_binary)] if self.audit_binary else [])]),
                    'An executable is absent from the reviewed complete runtime closure')
        fail_unless(CORE_AUDIT_SHA == self.sha(self.audit_source), 'Locked CoreAudit changed')
        fail_unless(manifest['coreaudit_source_sha256'] == CORE_AUDIT_SHA,
                    'Runtime closure does not bind the unchanged CoreAudit')
        self.packages = [self.path(p) for p in runtime['package_libs']]
        package_root = self.path(runtime['package_root'])
        fail_unless(self.packages and all(p.is_dir() and p.is_relative_to(package_root)
                    for p in self.packages), 'Candidate LEAN_PATH must contain trusted package libs only')
        fail_unless([str(p) for p in self.packages] == manifest['candidate_package_libs'],
                    'Runtime manifest and actual candidate package paths differ')
        forbidden = ['ChallengeDeps.olean','ChallengeDeps/CandidateSpec.olean','Challenge/Candidate.olean',
                     'Solution/Candidate.olean',*[n.replace('.','/')+'.olean' for n in MODULE_NAMES]]
        fail_unless(not any((p/n).exists() for p in self.packages for n in forbidden),
                    'Candidate/user olean contaminated a trusted package path')
        self.tool_libs = [self.path(p) for p in runtime['interpreted_tool_libs']]
        fail_unless(all(p.is_dir() for p in self.tool_libs) and
                    [str(p) for p in self.tool_libs] == manifest['interpreted_tool_libs'],
                    'Tool import overlay differs from its reviewed closure')
        self.receipt['runtime_closure_manifest_sha256'] = runtime['closure_manifest']['sha256']
        if os.name == 'nt':
            self.wsl = str(self.bind_row(runtime['wsl_executable']))
            self.taskkill = str(self.bind_row(runtime['taskkill_executable']))
            fail_unless(all(p in allowed_paths for p in [str(controller),self.wsl,self.taskkill]),
                        'Controller/WSL/cleanup executable is absent from the reviewed runtime closure')
            fail_unless(self.linux_mapped(self.nano_host) == self.nano['execution_path'],
                        'Nanoda Windows/WSL path identity mismatch')
        else:
            fail_unless(str(controller) in allowed_paths, 'Controller is absent from reviewed runtime closure')
            fail_unless(str(self.nano_host) == self.nano['execution_path'], 'Nanoda path mismatch')
        ordinary_env = self.environment([self.work/'lib',*self.packages])
        version = self.run('compiler-version',[self.lean,'--version'],env=ordinary_env)
        fail_unless(self.read_log(version).strip() == runtime['lean']['version'], 'Compiler version changed')

    def fresh_record(self):
        row = self.gate['fresh_record']
        receipt_path = self.bind(row['receipt_path'],row['receipt_sha256'])
        body_path = self.bind(row['body_path'],row['body_sha256'])
        receipt = load(receipt_path)
        fail_unless(receipt['status'] == 200 and receipt['sha256'] == row['body_sha256'],
                    'Fresh record HTTP/body receipt mismatch')
        timestamp = datetime.fromisoformat(receipt['retrievedAt'].replace('Z','+00:00'))
        age = (datetime.now(timezone.utc)-timestamp).total_seconds()
        fail_unless(0 <= age <= row['maximum_age_seconds'] <= 900, 'Record recheck is stale or future-dated')
        data = load(body_path)
        records = data['records'] if isinstance(data,dict) else data
        eligible = [r for r in records if r['track']=='critical-line' and r['status']=='kernel-verified'
                    and r.get('exactRational')]
        value = lambda r: Fraction(int(r['exactRational']['numerator']),int(r['exactRational']['denominator']))
        current = max(eligible,key=value)
        fail_unless(current['exactRational'] == self.gate['expected_current_record'], 'Current record changed')
        fail_unless(0 < value(current) < Fraction(int(self.gate['score']['numerator']),
                     int(self.gate['score']['denominator'])) <= 1, 'Candidate does not improve the exact fresh record')
        self.current = current
        self.receipt.update({'fresh_record_checked_at_start':True,'record_receipt_age_seconds':age,
                            'current_record':current,'score':self.gate['score']})

    def generate_sources(self):
        selected = self.gate['frozen_draft']
        directory = self.path(selected['directory'])
        manifest_path = self.bind(directory/'files.json',selected['manifest_sha256'])
        for row in load(manifest_path)['files']:
            path = (directory/row['path']).resolve()
            fail_unless(path.is_relative_to(directory), 'Draft manifest path escape')
            self.bind(path,row['sha256'],row['bytes'])
        plan = load(directory/'candidate-parameters.json')
        fail_unless(plan['score'] == self.gate['score'] and
                    plan['current_record']['exactRational'] == self.gate['expected_current_record'],
                    'Source metadata score/baseline differs from the root gate')
        fail_unless([r['module'] for r in plan['source_modules']] == MODULE_NAMES, 'Wrong frozen module order')
        imports, parts = [], []
        for row in plan['source_modules']:
            data = (directory/'frozen-inputs'/row['path']).read_bytes()
            fail_unless(hashlib.sha256(data).hexdigest()==row['sha256'], 'Frozen module SHA mismatch')
            data.decode('utf-8',errors='strict')
            body = []
            for line in data.splitlines(keepends=True):
                if line.startswith(b'import '):
                    match = IMPORT.fullmatch(line)
                    fail_unless(match is not None, 'Unrecognized frozen import grammar')
                    name = match[1].decode('ascii')
                    if name in MODULE_NAMES:
                        fail_unless(MODULE_NAMES.index(name)<MODULE_NAMES.index(row['module']), 'Forward internal import')
                    else:
                        imports.append(line)
                else:
                    body.append(line)
            blob = b''.join(body)
            fail_unless(hashlib.sha256(blob).hexdigest()==row['retained_non_import_sha256'],
                        'Frozen non-import body mismatch')
            parts.append((row['module'],blob))
        solution = HEADER+b'import ChallengeDeps.CandidateSpec\n'+b''.join(imports)+b'\n'
        for name,body in parts:
            self.remaining()
            solution += ('\n/- BEGIN FLATTENED MODULE '+name+' -/\n').encode()+body+b'\n'
        solution += b'\n'+(directory/'frozen-inputs/public-wrapper.lean.txt').read_bytes()
        digest = hashlib.sha256(solution).hexdigest()
        fail_unless(digest==selected['solution_sha256']==plan['solution_sha256']
                    and len(solution)==selected['solution_bytes']==plan['solution_bytes']<=2_000_000,
                    'Fresh reconstructed single-file bytes/hash/budget differ from frozen expectation')
        for name in TARGETS:
            fail_unless(len(re.findall(rb'(?m)^theorem '+name.encode()+rb'\s*:',solution))==1,
                        'A public wrapper is missing or duplicated')
        fail_unless(not re.search(rb'(?m)^\s*(?:noncomputable\s+)?def\s+(?:candidateKappa|currentRecordKappa)\b',solution),
                    'Untrusted Solution defines a trusted score/record constant')
        trusted = self.gate['trusted_inputs']
        deps = self.bind_row(trusted['ChallengeDeps']).read_bytes()
        spec_template = self.bind_row(trusted['CandidateSpec_template']).read_bytes()
        challenge = self.bind_row(trusted['Challenge_template']).read_bytes()
        fail_unless(hashlib.sha256(deps).hexdigest()=='f05666d0745edbf2dac6ce2a4de675abd1bba3c336fe24aebb80f27d1365ebbd',
                    'Trusted ChallengeDeps is not the pinned upstream source')
        for token in [b'{{CURRENT_EXPRESSION}}',b'{{NUMERATOR}}',b'{{DENOMINATOR}}']:
            fail_unless(spec_template.count(token)==1, 'Trusted spec template token mismatch')
        # Use an exact expression constructed from the checked rational, not arbitrary leaderboard text.
        record=self.gate['expected_current_record']; score=self.gate['score']
        exact_current=('('+record['numerator']+' : ℝ) / '+record['denominator']).encode()
        spec=spec_template.replace(b'{{CURRENT_EXPRESSION}}',exact_current)
        spec=spec.replace(b'{{NUMERATOR}}',score['numerator'].encode()).replace(b'{{DENOMINATOR}}',score['denominator'].encode())
        fail_unless(b'{{' not in spec, 'Unexpanded trusted spec template')
        for relative,data in [('ChallengeDeps.lean',deps),('ChallengeDeps/CandidateSpec.lean',spec),
                              ('Challenge/Candidate.lean',challenge),('Solution/Candidate.lean',solution)]:
            self.write_bytes(self.work/'source'/relative,data)
        fail_unless(not list((self.work/'lib').rglob('*')), 'Fresh lib was not empty before ordinary compilation')
        self.receipt.update({'source_freshly_regenerated_inside_budget':True,
            'source_bytes':len(solution),'source_sha256':digest,'source_slack_bytes':2_000_000-len(solution),
            'trusted_spec_generated_from_exact_checked_rationals':True})
        self.write_json(self.work/'generation.json',{'source_bytes':len(solution),'source_sha256':digest,
                         'fresh_source_generation':True,'cached_user_oleans':False,
                         'generation_elapsed_from_total_start':time.monotonic()-self.t0})

    def ordinary(self):
        paths=[self.work/'lib',*self.packages]
        env=self.environment(paths)
        results=[]
        for module in ['ChallengeDeps','ChallengeDeps.CandidateSpec','Challenge.Candidate','Solution.Candidate']:
            relative=Path(*module.split('.'))
            source=(self.work/'source'/relative).with_suffix('.lean')
            output=(self.work/'lib'/relative).with_suffix('.olean')
            output.parent.mkdir(parents=True,exist_ok=True)
            command=[self.lean,'-j1','-M13500','--tstack=262144','-DrelaxedAutoImplicit=false',
                     '-DElab.async=false','-R',str(self.work/'source'),'-o',str(output),str(source)]
            result=self.run('ordinary-'+module,command,env=env)
            fail_unless(output.is_file(),'Compiler returned without the expected fresh olean')
            for generated in (self.work/'lib').rglob('*'):
                if generated.is_file() and str(generated.resolve()) not in self.bound:
                    self.bind(generated,self.sha(generated))
            result.update({'module':module,'source_sha256':self.sha(source),'olean_sha256':self.sha(output)})
            if module=='Solution.Candidate':
                text=self.read_log(result)
                axioms={name:[x.strip() for x in raw.split(',') if x.strip()] for name,raw in
                        re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S)}
                axioms.update({name:[] for name in re.findall(r"'([^']+)' does not depend on any axioms",text)})
                fail_unless(set(TARGETS)<=set(axioms) and all(set(a)<=set(ALLOWED) for a in axioms.values()),
                            'Solution public/transitive printed axiom audit failed or a root is missing')
                self.receipt['ordinary_printed_axioms']=axioms
            results.append(result)
        self.receipt['ordinary_single_file_passed']=True
        self.receipt['compiled_modules']=results
        self.immutable()

    def proof_replays(self):
        paths=[self.work/'lib',*self.packages]
        env=self.environment(paths)
        exports={}
        for label,module in [('challenge','Challenge.Candidate'),('solution','Solution.Candidate')]:
            target=self.work/(label+'.ndjson')
            exports[label]=self.run(label+'-native-export',[self.exporter,module,'--',*TARGETS,*PRIMITIVES],
                                    env=env,output=target)
        self.immutable()
        if self.audit['mode']=='native':
            command=[self.audit_binary,str(self.work/'challenge.ndjson'),str(self.work/'solution.ndjson'),*TARGETS]
        else:
            command=[self.lean,'-j1','-M13500','--tstack=262144','--run',str(self.audit_source),
                     str(self.work/'challenge.ndjson'),str(self.work/'solution.ndjson'),*TARGETS]
        audit=self.run('comparator-default-Lean-kernel',command,
                       env=self.environment([*paths,*self.tool_libs]))
        for required in ['Pinned Comparator statement, dependency and primitive comparison passed',
                         'Pinned Comparator transitive axiom check passed','Lean default kernel replay passed']:
            fail_unless(required in self.read_log(audit),'A full pinned CoreAudit check was not observed')
        self.receipt.update({'exports':exports,'Comparator_statement_dependency_primitive_passed':True,
                             'Comparator_transitive_axioms_passed':True,'default_Lean_kernel_replay_passed':True})
        config={'use_stdin':True,'permitted_axioms':ALLOWED,'unpermitted_axiom_hard_error':True,
                'nat_extension':True,'string_extension':True,'num_threads':0,
                'unsafe_permit_all_axioms':False,'print_success_message':True,
                'print_axioms':True,'pp_to_stdout':True}
        cfg=self.work/'nanoda-config.json'; self.write_json(cfg,config)
        if os.name=='nt':
            self.nano_pidfile=self.work/'nanoda-owned-pgid.txt'
            # A fixed shell program, parameter arrays, own new session and fresh PID file.
            script='umask 077; printf "%s\\n" "$$" > "$1"; exec "$2" "$3"'
            command=self.wsl_command('/usr/bin/setsid','--wait','/bin/sh','-c',script,'owned-w9a2-nanoda',
                self.linux_mapped(self.nano_pidfile),self.nano['execution_path'],self.linux_mapped(cfg))
        else:
            command=[self.nano['execution_path'],str(cfg)]
        nano=self.run('serial-nanoda',command,env=env,stdin=self.work/'solution.ndjson',wsl_nanoda=os.name=='nt')
        text=self.read_log(nano)
        checked=re.search(r'Checked (\d+) declarations with no errors',text)
        printed=[name.split('.{')[0] for name in re.findall(r'^axiom ([^\s]+)',text,re.M)]
        fail_unless(checked is not None and int(checked[1])>0 and set(printed)<=set(ALLOWED),
                    'Independent complete nanoda replay/axiom audit did not pass')
        self.receipt.update({'serial_nanoda_passed':True,'nanoda_num_threads':0,
                             'nanoda_checked_declarations':int(checked[1]),'nanoda_printed_axioms':printed})

    def finish(self):
        self.immutable()
        self.receipt.update({'stage':'all-proof-stages-passed','failed':False,'local_fullchain_verified':True,
            'complete_source_and_bound_artifacts_unchanged':True,'bound_sha256':self.bound,
            'elapsed_before_final_receipts_seconds':time.monotonic()-self.t0,
            'outer_actual_process_exit0_and_terminal_sha_observation_still_required':True})
        # Three genuine fsynced, hash-linked receipts. A process cannot attest its own future exit.
        verify=self.work/'verification.json'; self.write_json(verify,self.receipt,bind=False)
        verify_sha=self.sha(verify)
        deadline=self.work/'deadline-receipt.json'
        self.write_json(deadline,{'verification_sha256':verify_sha,'total_limit_seconds':BUDGET,
            'elapsed_after_fsynced_verification_seconds':time.monotonic()-self.t0,
            'within_total_limit':True,'official_website_acceptance':False},bind=False)
        deadline_sha=self.sha(deadline)
        terminal=self.work/'terminal.json'
        self.write_json(terminal,{'verification_sha256':verify_sha,'deadline_receipt_sha256':deadline_sha,
            'elapsed_before_terminal_fsync_seconds':time.monotonic()-self.t0,
            'full_chain_and_hashes_completed':True,'completion_return_code':0,
            'actual_process_exit0_must_be_observed_by_outer_handle':True,
            'failure_receipt_must_be_absent':True,'official_website_acceptance':False},bind=False)
        terminal_sha=self.sha(terminal)
        self.remaining()
        print(json.dumps({'local_fullchain_verified':True,'work_directory':str(self.work),
            'terminal_sha256':terminal_sha,'total_elapsed_through_all_fsynced_receipts_seconds':time.monotonic()-self.t0,
            'root_must_observe_actual_process_exit_code':0,'official_website_acceptance':False}),flush=True)
        self.remaining()

    def execute(self):
        fail_unless(__debug__, 'Do not run with Python optimization/assert elision')
        self.setup_gate(); self.setup_runtime(); self.fresh_record(); self.generate_sources()
        self.ordinary(); self.proof_replays(); self.finish()

    def failure(self,error):
        self.receipt.update({'failed':True,'local_fullchain_verified':False,
            'error_type':type(error).__name__,'error':str(error),'traceback':traceback.format_exc(),
            'elapsed_at_failure_seconds':time.monotonic()-self.t0})
        if self.work and self.work.is_dir():
            # Failure receipt is preserved even after budget expiry; it never grants a PASS.
            target=self.work/'failure.json'
            try:
                with target.open('x',encoding='utf-8',newline='\n') as stream:
                    json.dump(self.receipt,stream,ensure_ascii=False,indent=2); stream.write('\n')
                    stream.flush(); os.fsync(stream.fileno())
            except OSError as failure_error:
                print('Could not preserve failure receipt: '+repr(failure_error),file=sys.stderr,flush=True)


def main():
    t0=time.monotonic()
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--gate',required=True); ap.add_argument('--gate-sha256',required=True)
    args=ap.parse_args()
    attempt=Attempt(t0,args)
    def interrupted(signum,frame):
        raise KeyboardInterrupt('Received signal '+str(signum))
    signal.signal(signal.SIGTERM,interrupted)
    try:
        attempt.execute()
    except BaseException as error:
        attempt.failure(error)
        raise
    return 0


if __name__=='__main__':
    raise SystemExit(main())
