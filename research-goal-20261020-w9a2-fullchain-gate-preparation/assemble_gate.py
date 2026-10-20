"""Assemble a DISABLED full-chain proposal from real completed preflight evidence.

No subprocess, network, source generation, proof evaluation, cache installation,
or compiler invocation. No enabled execution gate is produced by this program.
Root must inspect the proposal and separately authorize a new gate.
"""
from __future__ import annotations

import argparse
import ast
import copy
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import re
import sys
from urllib.parse import urlsplit

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
RUNNER_DIR = ROOT / 'research-goal-20261020-w9a2-verification-preparation-v1'
RUNNER = RUNNER_DIR / 'run_verification.py'
RUNNER_SHA = '92cc8dcf3e3c46e76490ba7bfe8d93bc10e331131eaab3b4c3ae500f80ac66a8'
RUNNER_MANIFEST_SHA = '3dc697cd99c9a38730b4e32cef02fd1f780f74ffeaa1512e6e52500d9e6e3e53'
DRAFT = ROOT / 'research-goal-20261020-w9a2-delivery/draft-v1'
ORDINARY_GATE_SHA = '92def59e80c77b461e3cc301bff748f65e44d53b4c031d745098b156882a3bc5'
ORDINARY_RUNNER = ROOT / 'research-goal-20261020-w9a2-runtime/compile_frozen.py'
ORDINARY_RUNNER_SHA = '09b7478efdc8ed380df82b7e04329cd783e347230b46ff283014e20a36822c62'
ORDINARY_RUNNERS = {
    ORDINARY_RUNNER_SHA: ORDINARY_RUNNER,
    '633039e6f029db0ded5de91d7c24cda062cf862ddb95e27cfbdf7e18a2402cc9':
        ROOT / 'research-goal-20261020-w9a2-runtime/compile_frozen_scoped_v1.py'}
TRUSTED_JOB = ROOT / 'tmp/w9a2-20261020/trusted-v1'
CORE_AUDIT_SHA = '7e88e84d1d35d5f3115c97a574cc64dd089ef713ef6f9bccb2303fbd41e07ff2'
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}
MODULES = ['StructuralW9A220261020.' + name for name in
           ['Core', 'Graph', 'Localization', 'Counting', 'Final']]
PACKAGES = ['LeanSearchClient', 'Qq', 'plausible', 'importGraph', 'proofwidgets',
            'aesop', 'batteries', 'Zeta23', 'mathlib']
PRINTED_ROOTS = {
    MODULES[0]: [], MODULES[1]: [], MODULES[2]: [],
    MODULES[3]: ['StructuralW9A220261020.Counting.' + name for name in
        ['sum_range_coboundary_lower', 'summed_of_state', 'actual_defect_estimate_effective',
         'actual_dyadic_of_summed', 'actual_cumulative_of_summed']],
    MODULES[4]: ['StructuralW9A220261020.Localization.located_state',
        'StructuralW9A220261020.Graph.edge_from_locations',
        'StructuralW9A220261020.Graph.edge_potential',
        *['StructuralW9A220261020.Final.' + name for name in
          ['actual_summed', 'strict_improvement', 'actual_dyadic', 'actual_cumulative']]]}
SCORE = {'numerator': '3337881639516708570682858853672166187793',
         'denominator': '4955348542279967171490000000000000000000'}
RECORD = {'numerator': SCORE['numerator'],
          'denominator': '4955348548503844558750000000000000000000'}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def integer_zero(value):
    return type(value) is int and value == 0


def now():
    return datetime.now(timezone.utc)


def timestamp(text):
    value = datetime.fromisoformat(text.replace('Z', '+00:00'))
    require(value.tzinfo is not None, 'Timestamp must specify a time zone')
    return value


def path(value):
    item = Path(value)
    return Path(os.path.abspath(item if item.is_absolute() else ROOT / item))


def same_path(a, b):
    return path(a).resolve() == path(b).resolve()


def sha(item):
    result = hashlib.sha256()
    with Path(item).open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            result.update(block)
    return result.hexdigest()


def load(item):
    return json.loads(Path(item).read_bytes())


class Bindings:
    def __init__(self):
        self.files = {}

    def bind(self, value, digest, size=None):
        item = path(value)
        require(item.is_file(), 'Missing completed input: ' + str(item))
        require(re.fullmatch('[0-9a-f]{64}', digest) is not None, 'Unfilled SHA: ' + str(item))
        require(size is None or item.stat().st_size == size, 'Byte size changed: ' + str(item))
        require(sha(item) == digest, 'SHA changed: ' + str(item))
        entry = {'path': str(item), 'resolved_path': str(item.resolve()),
                 'bytes': item.stat().st_size, 'sha256': digest}
        key = str(item)
        require(key not in self.files or self.files[key] == entry, 'Conflicting input pin')
        self.files[key] = entry
        return item

    def row(self, entry):
        item = self.bind(entry['path'], entry['sha256'], entry.get('bytes'))
        require('resolved_path' not in entry or str(item.resolve()) == entry['resolved_path'],
                'Input link resolution changed: ' + str(item))
        return item

    def current(self, item):
        item = path(item)
        return self.bind(item, sha(item), item.stat().st_size)

    def manifest(self, item, digest):
        item = self.bind(item, digest)
        data = load(item)
        require(data['files'], 'Empty manifest')
        for entry in data['files']:
            target = (item.parent / entry['path']).resolve()
            require(target.is_relative_to(item.parent.resolve()), 'Preparation manifest path escape')
            self.bind(target, entry['sha256'], entry['bytes'])
        return data

    def immutable(self):
        for entry in self.files.values():
            item = Path(entry['path'])
            require(str(item.resolve()) == entry['resolved_path'] and
                    item.stat().st_size == entry['bytes'] and sha(item) == entry['sha256'],
                    'Input changed during assembly: ' + str(item))


def literal(name):
    expressions = [node.value for node in ast.parse(RUNNER.read_bytes()).body
        if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == name
                                                for t in node.targets)]
    require(len(expressions) == 1, 'Missing pinned runner constant: ' + name)
    return ast.literal_eval(expressions[0])


def outer_observation(bind, entry, *, role, runner, completion, session=None, parent_pid=None, gate=None, exit_code=0):
    data = load(bind.row(entry))
    require(data['schema'] == 'w9a2-root-terminal-observation-v1' and
            data['sole_owner'] == '/root' and data['role'] == role,
            'Wrong root outer observation role/owner')
    require(type(data['exec_session_id']) is int and data['exec_session_id'] > 0 and
            type(data['parent_pid']) is int and data['parent_pid'] > 0 and
            type(data['actual_exit_code']) is int and data['actual_exit_code'] == exit_code,
            'Actual outer exit differs from the completed stage')
    require(session is None or data['exec_session_id'] == session, 'Wrong original parent handle')
    require(parent_pid is None or data['parent_pid'] == parent_pid, 'Wrong parent PID')
    require(data['observed_scope'] == 'completed-outer-parent-handle',
            'A module receipt, PID disappearance or self-declared future exit is insufficient')
    require(data['observation_source'] in ['functions.exec_command', 'functions.write_stdin'],
            'Observation must name the actual external process-handle tool')
    require(0 <= (now() - timestamp(data['observed_at_utc'])).total_seconds(),
            'Future-dated external process observation')
    raw = load(bind.row(data['raw_tool_terminal']))
    require(type(raw.get('exit_code')) is int and raw['exit_code'] == exit_code and
            isinstance(raw.get('output'), str), 'Pinned raw outer tool result has no matching actual exit/output')
    require(raw.get('session_id') in [None, data['exec_session_id']], 'Raw handle mismatch')
    actual_runner = bind.row(data['runner'])
    require(same_path(actual_runner, runner), 'Outer observation names a different runner')
    receipt = bind.row(data['completion_receipt'])
    require(same_path(receipt, completion), 'Outer observation names a different completion receipt')
    if gate is not None:
        require(same_path(bind.row(data['gate']), gate), 'Outer observation names a different gate')
    return data


def printed_axioms(text):
    pairs = [(name, [x.strip() for x in raw.split(',') if x.strip()]) for name, raw in
        re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S)]
    pairs += [(name, []) for name in re.findall(r"'([^']+)' does not depend on any axioms", text)]
    require(len(pairs) == len(dict(pairs)), 'Duplicate printed axiom roots')
    require(all(set(values) <= ALLOWED for _, values in pairs), 'Unexpected printed axiom')
    return dict(pairs)


def ordinary_observation(bind, stage, *, job, start, terminal_path, terminal, gate_path, runner, exit_code):
    if 'outer_observation' in stage:
        return outer_observation(bind, stage['outer_observation'], role=job.name,
            runner=runner, completion=terminal_path, parent_pid=start['pid'], gate=gate_path,
            exit_code=exit_code)
    # Root's already-preserved actual session attestations are also accepted.
    # These are explicitly trusted root observations, never inferred from a
    # vanished PID or an internal receipt. Bind the complete archive and match
    # its started/terminal bytes to this actual job before using its attestation.
    archive_manifest = bind.row(stage['archive_manifest'])
    manifest = bind.manifest(archive_manifest, sha(archive_manifest))
    archive = path(stage['archived_job_directory']).resolve()
    require(archive.is_relative_to(archive_manifest.parent.resolve()), 'Archived job escapes its manifest')
    declared = {(archive_manifest.parent / r['path']).resolve() for r in manifest['files']}
    for name in ['started.json', 'terminal.json']:
        item = archive / name
        require(item.resolve() in declared and sha(item) == sha(job / name),
                'Root-observed archive belongs to a different started/terminal job')
    attestation_path = bind.row(stage['root_attestation']); attestation = load(attestation_path)
    require(attestation_path.resolve() in declared or same_path(attestation_path, archive_manifest),
            'Root attestation is not sealed by the archived manifest')
    actual_session = attestation.get('root_observed_parent_session',
                                     attestation.get('root_observed_previous_parent_session'))
    require(type(actual_session) is int and actual_session > 0 and
            type(attestation['actual_parent_exit_code']) is int and
            attestation['actual_parent_exit_code'] == exit_code,
            'Root attestation does not record this actual outer terminal exit')
    if 'source' in attestation:
        require(attestation['source'] ==
                'Root observed original exec session terminal, rather than inferred process disappearance',
                'Attestation was inferred instead of observed through the original handle')
    if 'job' in attestation:
        require(same_path(attestation['job'], job), 'Root attestation identifies another job')
    if 'terminal_passed' in attestation:
        require(attestation['terminal_passed'] is terminal['passed'], 'Root/internal terminal disagree')
    require(attestation.get('fullchain_passed', False) is False and
            attestation.get('submitted', False) is False, 'Development archive upgraded its scope')
    return {'exec_session_id': actual_session, 'parent_pid': start['pid'],
        'actual_exit_code': exit_code, 'root_trust_boundary': 'Pinned original-handle attestation and exact archived job bytes'}


def ordinary_preflight(bind, request, plan):
    # Explicitly authorized development stages may fail after producing an exact
    # passing prefix/Core. Select only actual PASS outputs whose source matches
    # the final frozen draft. Never turn a failed whole batch into a whole PASS.
    for digest, source in ORDINARY_RUNNERS.items():
        bind.bind(source, digest)
    trusted = load(bind.current(TRUSTED_JOB / 'ChallengeDeps.receipt.json'))
    trusted_terminal = load(bind.current(TRUSTED_JOB / 'terminal.json'))
    require(trusted_terminal['passed'] is True and trusted_terminal['modules_completed'] == 1 and
            integer_zero(trusted['exit_code']) and trusted['source_unchanged'] is True and
            trusted['ordinary_compile_passed'] is True and
            trusted['source_sha256'] == 'f05666d0745edbf2dac6ce2a4de675abd1bba3c336fe24aebb80f27d1365ebbd',
            'Prior trusted definition preflight failed')
    bind.bind(TRUSTED_JOB / 'ChallengeDeps.log', trusted['log_sha256'])
    trusted_olean = bind.bind(TRUSTED_JOB / 'lib/ChallengeDeps.olean', trusted['olean_sha256'])
    passed_outputs = {str(trusted_olean.resolve()): (trusted['olean_sha256'], 'ChallengeDeps.olean')}
    stage_records, results = [], {}
    prefix_module = 'StructuralW9A220261020.Prefix'
    expected_roots = {prefix_module: [], **PRINTED_ROOTS}
    stages = request['ordinary_stages']
    require(isinstance(stages, list) and 1 <= len(stages) <= 64, 'Missing explicit ordinary stage chain')
    for index, stage in enumerate(stages):
        gate_path = bind.row(stage['gate']); gate = load(gate_path)
        job = path(gate['work_directory'])
        require(job.resolve().is_relative_to(ROOT / 'tmp') and
                re.fullmatch(r'candidate-ordinary-v\d+', job.name) is not None and
                gate['authorized'] is True and gate['task'] == 'w9a2-ordinary-source-pinned' and
                gate['runner_sha256'] in ORDINARY_RUNNERS and
                gate['automatic_repairs_or_retries'] == 0 and
                gate['sole_candidate_compiler_owner'] == '/root' and
                integer_zero(gate['root_observed_trusted_parent_actual_exit_code']),
                'Wrong ordinary stage authorization/owner/scope')
        for entry in gate['source_files']:
            bind.row(entry)
        for entry in gate['reused_oleans']:
            item = bind.row(entry)
            require(passed_outputs.get(str(item.resolve())) == (entry['sha256'], entry['module_path']),
                    'A development reused olean lacks an earlier exact PASS/source-bound output')
        require(not (job / 'failure.json').exists(), 'Incomplete or exceptional ordinary stage')
        start = load(bind.current(job / 'started.json'))
        terminal_path = bind.current(job / 'terminal.json'); terminal = load(terminal_path)
        count = terminal['modules_completed']
        require(type(count) is int and 1 <= count <= len(gate['targets']) and
                start['gate_sha256'] == sha(gate_path) and start['ordinary_only'] is True and
                terminal['ordinary_only'] is True and terminal['time_unix'] >= start['time_unix'] and
                type(terminal['passed']) is bool, 'Ordinary stage has no genuine terminal target prefix')
        expected_exit = 0 if terminal['passed'] else 1
        outer = ordinary_observation(bind, stage, job=job, start=start, terminal_path=terminal_path,
            terminal=terminal, gate_path=gate_path, runner=ORDINARY_RUNNERS[gate['runner_sha256']],
            exit_code=expected_exit)
        if job.name == 'candidate-ordinary-v0':
            require(sha(gate_path) == '3960ea16d3ef7b2bf7d91453e95ec77aa143aee295ca655df0a45c01661d0533' and
                    outer['exec_session_id'] == 68239 and start['pid'] == 39800 and expected_exit == 1,
                    'Historical v0 identity/exit changed')
        if job.name == 'candidate-ordinary-v1':
            require(sha(gate_path) == ORDINARY_GATE_SHA and outer['exec_session_id'] == 93720 and
                    start['pid'] == 40416 and expected_exit == 1, 'Historical v1 identity/exit changed')
        if job.name == 'candidate-ordinary-v2':
            require(sha(gate_path) == '59062ce669fcfc8e8a18e3367688f3f9e7d0eb8e9e1120fdbc2ab12f3ff57dac' and
                    outer['exec_session_id'] == 42867 and start['pid'] == 24036 and expected_exit == 1,
                    'Historical v2 identity/exit changed')
        source_pins = {str(path(row['path'])): row['sha256'] for row in gate['source_files']}
        stage_passes = []
        for position, target in enumerate(gate['targets'][:count]):
            module = target['module']; name = module.replace('.', '_')
            require(module in expected_roots, 'Unexpected development module')
            receipt_path = bind.current(job / (name + '.receipt.json')); receipt = load(receipt_path)
            source = path(target['source']); source_sha = source_pins[str(source)]
            output = job / 'lib' / Path(*module.split('.')).with_suffix('.olean')
            bind.bind(job / (name + '.lean'), source_sha)
            log = bind.bind(job / (name + '.log'), receipt['log_sha256'])
            child = load(bind.current(job / (name + '.child.json')))
            command = load(bind.current(job / (name + '.command.json')))
            expected_command = [gate['lean']['path'], '-j1', '-M13500', '--tstack=262144',
                '-DrelaxedAutoImplicit=false', '-DElab.async=false', '-R',
                str(path(target.get('source_root', '.'))), '-o', str(output), str(source)]
            require(command['argv'] == expected_command and type(child['pid']) is int and child['pid'] > 0 and
                    receipt['module'] == module and receipt['source_sha256'] == source_sha and
                    receipt['expected_roots'] == target['printed_roots'] == expected_roots[module],
                    'Development source/command/child/root identity mismatch')
            passed = receipt['ordinary_compile_passed']
            require(type(passed) is bool, 'Malformed ordinary result')
            observed = printed_axioms(log.read_text(encoding='utf-8', errors='strict'))
            if passed:
                require(integer_zero(receipt['exit_code']) and receipt['source_unchanged'] is True and
                        set(observed) == set(expected_roots[module]) and receipt['observed_axioms'] == observed and
                        (receipt['axiom_audit_passed'] is True if expected_roots[module]
                         else receipt['axiom_audit_passed'] is None), 'Passing module/log/axiom audit failed')
                bind.bind(output, receipt['olean_sha256'])
                passed_outputs[str(output.resolve())] = (receipt['olean_sha256'], module.replace('.', '/') + '.olean')
            else:
                require(not terminal['passed'] and position == count - 1, 'A failure was bypassed within a stage')
                if receipt.get('olean_sha256') is not None:
                    bind.bind(output, receipt['olean_sha256'])
            results[(index, module)] = {'passed': passed, 'source_sha256': source_sha,
                'observed_axioms': observed, 'receipt': str(receipt_path), 'olean_sha256': receipt.get('olean_sha256')}
            stage_passes.append(passed)
        require((terminal['passed'] and count == len(gate['targets']) and all(stage_passes)) or
                (not terminal['passed'] and stage_passes[-1] is False and all(stage_passes[:-1])),
                'A failed stage was misrepresented as complete')
        stage_records.append({'job': str(job), 'gate_sha256': sha(gate_path), 'actual_parent_exit_code': expected_exit,
            'modules_completed': count, 'whole_stage_passed': terminal['passed'],
            'actual_session_id': outer['exec_session_id']})
    selected = request['selected_development_modules']
    require(len(selected) == 6 and {r['module'] for r in selected} == {prefix_module, *MODULES},
            'Select exactly Prefix/Core/Graph/Localization/Counting/Final PASS provenance')
    final_sha = {r['module']: r['sha256'] for r in plan['source_modules']}
    require(final_sha[MODULES[0]] == 'c2af225175f9a5ab14d2ba2612714a21e0613f66107a1d75b9d47bf1c77ba02a',
            'This gate family requires the independently reviewed full Core repair')
    final_sha[prefix_module] = 'bfd774658f3f855596a5453f86f4d98fbc884ca651b3e595d68f70b9553f5b3c'
    final_sha[MODULES[0]] = '26e23c7fc4fbae33bdfff446901eaeb0f22f0f08fe13fa4e326541565a25279f'
    roots, selections = {}, []
    for choice in selected:
        require(type(choice['stage_index']) is int and isinstance(choice['module'], str),
                'Selection must identify an explicit integer stage and module')
        key = (choice['stage_index'], choice['module'])
        require(key in results, 'Selected development module has no actual receipt')
        result = results[key]
        require(result['passed'] is True and result['source_sha256'] == final_sha[choice['module']],
                'Selected module is failed/stale or differs from final frozen source')
        require(not set(roots).intersection(result['observed_axioms']), 'Duplicate selected axiom root')
        roots.update(result['observed_axioms']); selections.append({**choice, **result})
    require(len(roots) == 12 and stage_records[-1]['whole_stage_passed'] is True,
            'All twelve roots and final explicitly completed repair stage are required')
    return {'scope': 'Exact per-module development PASS chain only; no production olean imports',
        'ordinary_stages': stage_records, 'selected_modules': selections, 'observed_printed_axioms': roots,
        'prior_trusted_ChallengeDeps_ordinary_pass': True, 'production_cached_user_oleans': False}


def runtime_preflight(bind, request):
    closure_path = bind.row(request['runtime_closure'])
    closure = load(closure_path)
    require(closure['schema'] == 'w9a2-trusted-runtime-closure-v1' and
            closure['complete_source_bound_runtime_closure_verified'] is True and
            closure['user_proofs_compiled_or_reused_in_setup'] is False and
            closure['official_runtime_equivalence_claimed'] is False and closure['files'],
            'Runtime closure is incomplete or its scope changed')
    allowed, runtime_file_aliases = set(), set()
    for entry in closure['files']:
        item = bind.row(entry)
        allowed.add(str(item.resolve())); runtime_file_aliases.add(str(item))
    require(closure['tool_commits'] == literal('TOOL_COMMITS'), 'Tool commits changed')
    source_sha = literal('TOOL_SOURCE_LF_SHA')
    require(len(closure['trusted_tool_sources']) == len(source_sha) and
            {r['logical_name'] for r in closure['trusted_tool_sources']} == set(source_sha),
            'Incomplete fixed tool source set')
    for entry in closure['trusted_tool_sources']:
        item = bind.row(entry)
        require(str(item.resolve()) in allowed and hashlib.sha256(
            item.read_bytes().replace(b'\r\n', b'\n')).hexdigest() == source_sha[entry['logical_name']],
            'Tool source is absent or changed')
    for name, commit in {'mathlib': '51e6992efd06126df61a496bebf8f49482a4e129',
                         'Zeta23': '3635e74826a4c1fcece7d1cd2b6fa75e43a00510'}.items():
        require(closure['package_source_revisions'].get(name) == commit, 'Package revision changed')
    require(closure['coreaudit_source_sha256'] == CORE_AUDIT_SHA, 'CoreAudit source changed')
    setup_path = bind.row(closure['trusted_setup_receipt']); setup = load(setup_path)
    outer = outer_observation(bind, request['setup_outer_observation'], role='trusted-runtime-closure-v1',
        runner=request['setup_runner']['path'], completion=setup_path)
    setup_runner = bind.row(request['setup_runner'])
    require(setup['assembler_pid'] == outer['parent_pid'] and
            setup['assembler_sha256'] == sha(setup_runner) and
            setup['proof_runs'] == 0 and setup['user_proofs_compiled_or_reused_in_setup'] is False,
            'Setup receipt does not bind its actual assembler process/source/proof-free scope')
    runtime = copy.deepcopy(closure['runtime_gate_fragment'])
    runtime.update(root_confirmed_setup_terminal_exit_code=0,
        root_reviewed_complete_runtime_closure=False,
        closure_manifest={'path': str(closure_path), 'sha256': sha(closure_path)})
    require(runtime['coreaudit']['mode'] == 'interpreted' and runtime['coreaudit']['binary'] is None,
            'This reviewed proposal supports the interpreted locked CoreAudit route')
    bind.bind(runtime['coreaudit']['source_path'], CORE_AUDIT_SHA)
    require(same_path(runtime['python_controller']['path'], sys.executable) and
            runtime['python_controller']['version'] == sys.version, 'Different controller Python')
    for key in ['python_controller', 'lean', 'native_exporter', 'wsl_executable', 'taskkill_executable']:
        require(str(bind.row(runtime[key]).resolve()) in allowed, 'Executable absent from closure: ' + key)
    require(runtime['lean']['sha256'] == 'bc137e6662c48eedf2cdf167fb176080e18a15f57e248d214df0cb3939248683' and
            runtime['native_exporter']['sha256'] == 'bc718c9ff717b36827799e8edbc86028edaf86bdd26931ce7a8882fd3fbb67d9',
            'Unreviewed Windows compiler/exporter binary')
    sdk = path(runtime['lean_sysroot'])
    require(same_path(sdk / 'bin/lean.exe', runtime['lean']['path']) and
            runtime['lean']['version'] ==
            'Lean (version 4.33.0-rc2, x86_64-w64-windows-gnu, commit d8b18978322de05a8f3dba51ef03cf5461676c17, Release)' and
            runtime['controlled_path'] == str(sdk / 'bin') + ';C:\\Windows\\System32;C:\\Windows',
            'Compiler sysroot/version or controlled loader PATH changed')
    nano = runtime['nanoda']; nano_host = bind.row(nano['host_binary'])
    require(str(nano_host.resolve()) in allowed and nano['host_binary']['sha256'] ==
            'b19804767cb72bf5a317fcfc20e8af7eafdfba789dd6b24bddee2574379ff35a',
            'Unreviewed Nano binary')
    drive = nano_host.resolve().drive
    require(re.fullmatch('[A-Za-z]:', drive) is not None, 'Nano must be on a Windows local drive')
    require(nano['execution_path'] == '/mnt/' + drive[0].lower() + str(nano_host.resolve())[2:].replace('\\', '/'),
            'Nano host/WSL identity differs')
    require(nano['resolved_execution_path'].startswith('/') and runtime['wsl_distribution'] == 'Ubuntu',
            'Missing actual WSL Nano resolution or changed distribution')
    package_root = path(closure['package_root']).resolve()
    libs = [path(value) for value in closure['candidate_package_libs']]
    require(same_path(runtime['package_root'], package_root) and
            runtime['package_libs'] == closure['candidate_package_libs'] and
            runtime['interpreted_tool_libs'] == closure['interpreted_tool_libs'],
            'Closure/runtime overlay paths disagree')
    library_names = [p.parent.parent.parent.parent.name for p in libs]
    require(package_root.is_relative_to(ROOT / 'tmp') and
            [name for name in library_names if name != 'Cli'] == PACKAGES and library_names.count('Cli') <= 1,
            'Expected fixed clean package overlays, with only the pinned optional Cli metadata package')
    if 'Cli' in library_names:
        require(closure['package_source_revisions'].get('Cli') ==
                '1319485273bf87833fa472afbcefdedecb16b45f', 'Optional Cli source revision changed')
    forbidden = ['ChallengeDeps.olean', 'ChallengeDeps/CandidateSpec.olean', 'Challenge/Candidate.olean',
        'Solution/Candidate.olean', *[n.replace('.', '/') + '.olean' for n in MODULES],
        'StructuralW9A220261020/Prefix.olean']
    for lib in libs:
        require(lib.is_dir() and lib.resolve().is_relative_to(package_root), 'Package overlay escape')
        require(not any((lib / name).exists() for name in forbidden), 'User olean contaminates package overlay')
        for item in lib.rglob('*'):
            if item.is_file():
                require(item.resolve().is_relative_to(package_root) and str(item.resolve()) in allowed and
                        item.suffix.lower() not in ['.dll', '.exe', '.so', '.a', '.o', '.obj'],
                        'Unbound/native/escaping file in data-only package overlay')
    zeta = libs[library_names.index('Zeta23')]
    require(all(p.name == 'Zeta23' for p in zeta.iterdir()), 'Zeta overlay contains old root-level modules')
    tools = [path(p) for p in closure['interpreted_tool_libs']]
    require(len(tools) == 1 and tools[0].is_dir(), 'Expected one exact interpreted tool overlay')
    expected_tools = {'Comparator.olean', 'Comparator/Axioms.olean', 'Comparator/Compare.olean',
                      'Comparator/Util.olean', 'Export/Parse.olean'}
    actual_tools = {p.relative_to(tools[0]).as_posix() for p in tools[0].rglob('*.olean')}
    require(actual_tools == expected_tools, 'Nested Parse or an exact interpreted module is missing/extra')
    for item in tools[0].rglob('*'):
        if item.is_file():
            require(str(item.resolve()) in allowed and item.resolve().is_relative_to(tools[0].resolve()),
                    'Interpreted overlay file is not bound')
    names = {Path(entry['path']).name.lower() for entry in closure['files']}
    require({'_decimal.pyd', '_hashlib.pyd', 'python312.dll'} <= names,
            'Actual controller extension closure is incomplete')
    return runtime, runtime_file_aliases


def fresh_record(bind, request):
    entry = request['fresh_record']; receipt_path = bind.row(entry['receipt']); body_path = bind.row(entry['body'])
    receipt = load(receipt_path); raw = body_path.read_bytes()
    url = urlsplit(receipt['url'])
    require(url.scheme == 'https' and url.netloc == 'www.riemannzeta.fun' and
            url.path == '/api/leaderboard' and receipt['status'] == 200 and
            receipt['sha256'] == sha(body_path) and receipt['bytes'] == len(raw),
            'Fresh record URL/status/body receipt differs')
    age = (now() - timestamp(receipt['retrievedAt'])).total_seconds()
    require(0 <= age <= entry['maximum_age_seconds'] <= 900, 'Fresh record expired or future-dated')
    data = json.loads(raw); records = data['records'] if isinstance(data, dict) else data
    eligible = [r for r in records if r['track'] == 'critical-line' and r['status'] == 'kernel-verified'
                and r.get('exactRational')]
    value = lambda row: Fraction(int(row['exactRational']['numerator']), int(row['exactRational']['denominator']))
    current = max(eligible, key=value)
    require(current['exactRational'] == RECORD and 0 < value(current) <
            Fraction(int(SCORE['numerator']), int(SCORE['denominator'])) <= 1,
            'Current exact record changed; original objective requires route review')
    return {'receipt_path': str(receipt_path), 'receipt_sha256': sha(receipt_path),
        'body_path': str(body_path), 'body_sha256': sha(body_path),
        'maximum_age_seconds': entry['maximum_age_seconds']}


def write_json(item, obj):
    with item.open('xb') as stream:
        stream.write((json.dumps(obj, ensure_ascii=False, indent=2) + '\n').encode())
        stream.flush(); os.fsync(stream.fileno())


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--request', required=True)
    ap.add_argument('--request-sha256', required=True)
    ap.add_argument('--preparation-manifest-sha256', required=True)
    args = ap.parse_args()
    require(__debug__ and os.name == 'nt', 'Use reviewed Windows Python without optimization')
    bind = Bindings()
    bind.manifest(HERE / 'prepared-files.json', args.preparation_manifest_sha256)
    require(str(path(__file__)) in bind.files, 'Assembler source absent from its preparation manifest')
    request = load(bind.bind(args.request, args.request_sha256))
    require(request['schema'] == 'w9a2-fullchain-assemble-request-v1' and request['sole_owner'] == '/root',
            'This proposal has a single root owner')
    destination = path(request['proposal_directory']).resolve()
    work = path(request['production_work_directory']).resolve()
    require(destination.is_relative_to(ROOT / 'tmp') and not destination.exists() and
            work.is_relative_to(ROOT / 'tmp') and not work.exists() and
            not destination.is_relative_to(work) and not work.is_relative_to(destination),
            'Proposal and production directories must be separate new exclusive tmp paths')
    bind.manifest(RUNNER_DIR / 'prepared-files.json', RUNNER_MANIFEST_SHA)
    bind.bind(RUNNER, RUNNER_SHA)
    selected_draft = request['frozen_draft']
    draft = path(selected_draft['directory']).resolve()
    require(draft.parent == DRAFT.parent and re.fullmatch(r'draft-v[1-9][0-9]*', draft.name) is not None,
            'Select a new frozen draft in the original delivery directory')
    bind.manifest(draft / 'files.json', selected_draft['manifest_sha256'])
    bind.bind(draft / 'Solution.lean', selected_draft['solution_sha256'], selected_draft['solution_bytes'])
    plan = load(draft / 'candidate-parameters.json')
    require(plan['score'] == SCORE and plan['current_record']['exactRational'] == RECORD,
            'Frozen source score/record metadata changed')
    require([r['module'] for r in plan['source_modules']] == MODULES and
            plan['solution_sha256'] == selected_draft['solution_sha256'] and
            plan['solution_bytes'] == selected_draft['solution_bytes'] <= 2000000,
            'Final frozen draft manifest/metadata/source budget disagree')
    ordinary = ordinary_preflight(bind, request, plan)
    keep_preflight_aliases = set(bind.files)
    runtime, runtime_file_aliases = runtime_preflight(bind, request)
    record = fresh_record(bind, request)
    # This new manifest binds all preflight source/receipt/log/outer-handle evidence
    # into the UNMODIFIED runner's existing bind()+immutable() checks. No body is copied.
    # The unchanged runner already binds every closure.files row in setup_runtime.
    # Do not duplicate the entire SDK/cache file walk in its initial manifest loop.
    evidence_manifest = {'scope': 'Frozen runner plus actual completed development/setup evidence; proposal only',
        'runtime_file_pins_are_bound_by_unmodified_runner_setup_runtime': True,
        'files': [entry for key, entry in bind.files.items()
                  if key not in runtime_file_aliases or key in keep_preflight_aliases]}
    gate = {'schema': 'w9a2-fullchain-gate-v1', 'allow_verification_execution': False,
        'proposal_only': True, 'sole_owner': '/root', 'platform': 'windows-native-wsl-nanoda',
        'total_budget_seconds': 3200, 'automatic_retries': 0, 'automatic_repairs': 0,
        'cached_user_oleans': False, 'runner_sha256': RUNNER_SHA,
        'prepared_manifest': {'path': str(destination / 'bound-inputs-manifest.json'), 'sha256': ''},
        'work_directory': str(work), 'frozen_draft': {**selected_draft, 'directory': str(draft)},
        'score': SCORE, 'expected_current_record': RECORD,
        'fresh_record': record, 'trusted_inputs': {
            'ChallengeDeps': {'path': str(draft / 'trusted/ChallengeDeps.lean'),
                              'sha256': 'f05666d0745edbf2dac6ce2a4de675abd1bba3c336fe24aebb80f27d1365ebbd'},
            'CandidateSpec_template': {'path': str(draft / 'frozen-inputs/CandidateSpec.lean.tmpl'),
                'sha256': '0e85c8c6b123eec25597fb1e838c632214d3aeb0f2ed8e40ab2890df3ece807c'},
            'Challenge_template': {'path': str(draft / 'frozen-inputs/Challenge.Candidate.lean'),
                'sha256': 'e77513b7751460054be21697d06b5ffff142d109b65b131e392aa568ccf22378'}},
        'runtime': runtime, 'development_preflight': ordinary,
        'remaining_before_separate_root_authorization': [
            'Root reviews exact disabled proposal, all evidence, current process ownership and runtime OS trust boundary.',
            'Root writes a NEW gate with allow_verification_execution true, proposal_only false and runtime.root_reviewed_complete_runtime_closure true.',
            'Root computes the new gate SHA and launches only the unchanged frozen runner with its own real outer process handle.',
            'All production compilation/export/Comparator/default Lean/serial Nano and three receipts remain required inside one 3200s deadline.'],
        'proof_compiler_export_kernel_runs_by_assembler': 0,
        'preflight_source_body_generated_or_copied': False,
        'production_candidate_oleans_reused': False}
    for entry in gate['trusted_inputs'].values():
        bind.row(entry)
    bind.immutable()
    # A long local hash audit can age a receipt. Refuse before writing anything.
    fresh_record(bind, request)
    destination.mkdir(parents=True, exist_ok=False)
    evidence_path = destination / 'bound-inputs-manifest.json'
    write_json(evidence_path, evidence_manifest)
    gate['prepared_manifest']['sha256'] = sha(evidence_path)
    write_json(destination / 'gate-proposal.json', gate)
    write_json(destination / 'assembly-receipt.json', {'schema': 'w9a2-disabled-fullgate-assembly-v1',
        'prepared_at_utc': now().isoformat(), 'assembler_pid': os.getpid(), 'assembler_sha256': sha(__file__),
        'proposal_sha256': sha(destination / 'gate-proposal.json'),
        'bound_manifest_sha256': sha(evidence_path), 'bound_file_count': len(evidence_manifest['files']),
        'allow_verification_execution': False, 'proof_runs': 0,
        'source_body_generated_or_copied': False,
        'this_receipt_is_not_evidence_of_its_own_future_process_exit': True})
    print(json.dumps({'proposal': str(destination / 'gate-proposal.json'),
        'proposal_sha256': sha(destination / 'gate-proposal.json'),
        'allow_verification_execution': False, 'proof_runs': 0}), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
