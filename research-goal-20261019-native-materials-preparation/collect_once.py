"""Collect only after root confirms the real terminal exit0 of fullcold v2.

Preparation never executes this file. This collector runs no compiler, exporter,
kernel, generator, network, Git or website operation. It creates one new material
directory, never overwrites/resumes it, and preserves failed partial collection.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
from decimal import Decimal, localcontext
from fractions import Fraction
import hashlib
import json
import math
import os
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PREPARED = HERE / 'prepared-files.json'
PROD = ROOT / 'research-goal-20261019-tiny-production-preparation-v2'
FLAT = ROOT / 'research-goal-20261019-tiny-flatten-preparation-v4'
OLD_MATH = ROOT / 'submission/single-exception-overlap-20261019'
WORK = Path('/var/tmp/rh-zero-20261015/tiny-production-v2')
MIRROR = ROOT / 'tmp/current-s1r-tiny-20261018/production-v2'
DEST = ROOT / 'submission/single-exception-overlap-native-v4-20261019'
GATE = ROOT / 'research-goal-20261016/gates/tiny-native-production-cold-v2-20261019.json'
GATE_PIN = '3cd2bc378f815b53d5c31233d89662c090b04bcdabc489c115f3a4d66924631a'
PROD_PIN = 'f2ab9d281bf39769da08280f40d9369e9b9ffc2f51c57acccbb116999daa9d74'
FLAT_PIN = '2b77159157e500b0177c3c2294860830a495248ce3e3b216a813524032509d72'
P = '3337839448633819172184136761695440236797'
Q = '4955319193827760237900000000000000000000'
R_Q = '4955319193847235264050000000000000000000'
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}
MODULES = ['ChallengeDeps', 'ChallengeDeps.CandidateSpec', 'Challenge.Candidate', 'Solution.Candidate']
PUBLIC_ROOTS = ['candidate_strict_improvement', 'candidate_critical_line_bound',
                'candidate_critical_line_bound_cumulative']
PRIMITIVES = ['Nat', 'String', 'String.mk', 'Char', 'Quot', 'Quot.mk', 'Quot.lift',
              'Quot.ind', 'propext', 'Quot.sound', 'Classical.choice',
              'Nat.add', 'Nat.sub', 'Nat.mul', 'Nat.pow', 'Nat.gcd', 'Nat.div',
              'Nat.mod', 'Nat.beq', 'Nat.ble', 'Nat.land', 'Nat.lor', 'Nat.xor',
              'Nat.shiftLeft', 'Nat.shiftRight', 'String.ofList', 'Char.ofNat', 'List', 'eagerReduce']
LABELS = ['compiler-version', 'generation', *['ordinary-' + m for m in MODULES],
          'challenge-export', 'solution-export', 'comparator-default-kernel', 'nanoda']

def load(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''):
            h.update(block)
    return h.hexdigest()

def write_new(path, value):
    with Path(path).open('x', encoding='utf-8', newline='\n') as f:
        json.dump(value, f, ensure_ascii=False, indent=2); f.write('\n')
        f.flush(); os.fsync(f.fileno())

def text_new(path, text):
    with Path(path).open('x', encoding='utf-8', newline='\n') as f:
        f.write(text); f.flush(); os.fsync(f.fileno())

def finite_seconds(value, upper=3200):
    assert type(value) in {int, float} and math.isfinite(value) and 0 < value <= upper
    return value

def main():
    assert __debug__, 'Assertions must remain enabled'
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepared-sha256', required=True)
    parser.add_argument('--root-confirmation', required=True)
    parser.add_argument('--root-confirmation-sha256', required=True)
    args = parser.parse_args()
    assert os.name == 'posix'
    assert ROOT == Path('/mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization')
    assert sha(PREPARED) == args.prepared_sha256
    original_pins = {str(PREPARED): args.prepared_sha256}
    for row in load(PREPARED)['files'] + load(PREPARED)['dependencies']:
        path = ROOT / row['path']
        assert path.stat().st_size == row['bytes'] and sha(path) == row['sha256'], row['path']
        original_pins[str(path)] = row['sha256']
    assert sha(PROD / 'prepared-files.json') == PROD_PIN
    assert sha(FLAT / 'prepared-files.json') == FLAT_PIN
    assert sha(GATE) == GATE_PIN
    gate, production_config = load(GATE), load(PROD / 'configuration.json')
    assert gate['prepared_sha256'] == PROD_PIN and gate['flatten_prepared_sha256'] == FLAT_PIN
    assert gate['job_directory'] == str(WORK) and gate['sole_owner'] == '/root'
    assert gate['total_budget_seconds'] == 3200 and gate['automatic_retries'] == 0
    confirmation_path = Path(args.root_confirmation).resolve()
    assert confirmation_path.is_relative_to(ROOT / 'research-goal-20261016/gates')
    assert sha(confirmation_path) == args.root_confirmation_sha256
    original_pins[str(confirmation_path)] = args.root_confirmation_sha256
    confirmation = load(confirmation_path)
    assert confirmation['confirmed_by'] == '/root'
    for field in ['root_confirmed_session_terminal', 'root_reviewed_complete_verification_deadline_and_mirror',
                  'root_confirmed_no_failure_and_all_bound_inputs_unchanged']:
        assert confirmation[field] is True, field
    assert confirmation['production_session_id'] == 84529
    assert confirmation['production_session_exit_code'] == 0
    assert confirmation['production_gate_sha256'] == GATE_PIN
    assert confirmation['production_prepared_sha256'] == PROD_PIN
    assert confirmation['flatten_prepared_sha256'] == FLAT_PIN
    assert confirmation['collector_prepared_sha256'] == args.prepared_sha256
    result = confirmation['terminal_tool_result']
    assert result['exit_code'] == 0
    finals = []
    for line in result['output'].splitlines():
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict) and 'total_elapsed_seconds_through_all_receipts' in value:
            finals.append(value)
    assert len(finals) == 1, 'Retain the actual terminal tool stdout, not a synthesized PASS'
    stdout_final = finals[0]
    assert stdout_final['local_single_file_verified'] is True
    assert stdout_final['official_website_acceptance'] is False
    elapsed = finite_seconds(stdout_final['total_elapsed_seconds_through_all_receipts'])
    assert not DEST.exists(), 'Exclusive destination exists; no overwrite, repair or retry'

    verification_path = WORK / 'verification.json'
    deadline_path = WORK / 'deadline-receipt.json'
    terminal_path = MIRROR / 'terminal.json'
    for path, key in [(verification_path, 'verification'), (deadline_path, 'deadline'),
                      (terminal_path, 'mirror_terminal')]:
        assert sha(path) == confirmation['receipt_sha256'][key]
        original_pins[str(path)] = sha(path)
    verification, deadline, terminal = map(load, [verification_path, deadline_path, terminal_path])
    assert verification['schema'] == 'tiny-cold-production-result-v3'
    assert verification['failed'] is False
    for field in ['local_single_file_verified', 'ordinary_single_file_lean_passed',
                  'statement_equality_proved', 'permitted_axioms_checked', 'default_kernel_replay_passed',
                  'independent_nanoda_passed', 'inputs_unchanged', 'total_deadline_enforced']:
        assert verification[field] is True, field
    assert verification['official_website_acceptance'] is False and verification['submitted'] is False
    assert verification['budget_seconds'] == 3200 and verification['retry_count'] == 0
    assert verification['cached_user_oleans_used'] is False
    assert verification['stage'] == 'all-proof-stages-passed'
    assert verification['prepared_sha256'] == PROD_PIN
    assert verification['gate_path'] == str(GATE) and verification['gate_sha256'] == GATE_PIN
    assert verification['sole_owner'] == '/root'
    assert verification['RLIMIT_FSIZE_bytes'] == 8 * 1024 ** 3 and verification['RAM_limit_claimed'] is False
    assert verification['local_nanoda_threads'] == 0
    assert verification['locked_official_Comparator_default_nanoda_is_serial'] is True
    assert verification['official_runtime_equivalence_claimed'] is False
    assert terminal['linux_work_directory'] == str(WORK)
    for receipt in [deadline, terminal]:
        assert receipt['verification_receipt_sha256'] == sha(verification_path)
        assert receipt['total_limit_seconds'] == 3200 and receipt['within_total_limit'] is True
        assert receipt['official_website_acceptance'] is False
        assert finite_seconds(receipt['elapsed_seconds_after_fsynced_verification_receipt']) <= elapsed
    assert deadline == {k: v for k, v in terminal.items() if k != 'linux_work_directory'}
    assert finite_seconds(verification['proof_stages_elapsed_seconds']) <= deadline['elapsed_seconds_after_fsynced_verification_receipt']
    assert verification['score'] == {'numerator': P, 'denominator': Q}
    assert verification['current_record']['exactRational'] == {'numerator': P, 'denominator': R_Q}
    assert verification['fresh_record_recheck'] == gate['fresh_record_recheck']
    assert verification['previous_failed_attempt_sha256'] == production_config['previous_failure_receipt_sha256']
    assert verification['deduplicated_production_source_prepared_sha256'] == gate['production_source_prepared_sha256']
    assert set(verification['observed_axioms']) <= ALLOWED
    assert type(verification['checked_declarations']) is int and verification['checked_declarations'] > 0
    assert [r['module'] for r in verification['compiled_modules']] == MODULES
    assert verification['tool_compiled_modules'] == []

    native = verification['trusted_native_tools']
    selected = gate['trusted_native_tools']
    assert native['installation_path'] == selected['installation_path']
    assert native['installation_sha256'] == selected['installation_sha256']
    assert native['setup_prepared_path'] == str(ROOT / selected['setup_prepared_path'])
    assert native['setup_prepared_sha256'] == selected['setup_prepared_sha256']
    install_path = Path(native['installation_path'])
    assert sha(install_path) == selected['installation_sha256']
    install = load(install_path)
    assert install['schema'] == 'trusted-native-tool-installation-v1'
    assert install['prepared_sha256'] == selected['setup_prepared_sha256']
    assert install['passed'] is True and install['proof_runs'] == 0 and install['automatic_retries'] == 0
    for field in ['complete_source_and_SDK_C_toolchain_unchanged', 'no_external_Lake_packages_or_network_fetch_configured']:
        assert install[field] is True
    assert install['user_oleans_compiled_or_reused'] is False
    assert install['official_website_acceptance'] is False
    assert native['setup_was_prior_to_this_proof_timer'] is True
    assert native['trusted_tools_recompiled_in_this_proof_attempt'] is False and native['user_oleans_reused'] is False
    for field in ['native_executables', 'native_runtime_closure_pins', 'source_provenance']:
        assert native[field] == install[field], field
    assert set(native['native_executables']) == {'lean4export', 'coreaudit'}
    assert all(row['exit_code'] == 0 for row in install['commands'])
    native_work = install_path.parent
    native_mirror = ROOT / 'tmp/current-s1r-tiny-20261018' / native_work.name.removeprefix('tiny-')
    assert sha(native_mirror / 'installation.json') == selected['installation_sha256']
    fail_paths = [WORK / 'failure.json', MIRROR / 'failure.json', native_work / 'failure.json', native_mirror / 'failure.json']
    bound = verification['bound_sha256_before_and_after']
    assert bound and all(re.fullmatch('[0-9a-f]{64}', value) for value in bound.values())
    for path, expected in [(GATE, GATE_PIN), (PROD / 'prepared-files.json', PROD_PIN),
                           (install_path, selected['installation_sha256']),
                           (ROOT / selected['setup_prepared_path'], selected['setup_prepared_sha256'])]:
        assert bound[str(path.resolve())] == expected
    resolutions = native['runtime_symlink_resolutions']
    for row in install['source_pins'] + native['native_runtime_closure_pins']:
        path = Path(row['path'])
        assert str(path.resolve()) == row['resolved_path'] and path.stat().st_size == row['bytes']
        assert resolutions[str(path)] == row['resolved_path']
        assert bound[str(path.resolve())] == row['sha256']
    def stable():
        for failure in fail_paths:
            assert not failure.exists(), str(failure)
        for path, resolved in resolutions.items():
            assert str(Path(path).resolve()) == resolved, 'Native runtime symlink changed'
        for path in original_pins.keys() & bound.keys():
            assert original_pins[path] == bound[path], 'Conflicting frozen and proof bindings'
        for path, expected in {**original_pins, **bound}.items():
            assert sha(path) == expected, 'A frozen input, receipt or bound artifact changed: ' + path
    stable()

    stages = verification['stages']
    assert [r['label'] for r in stages] == LABELS
    by_label = {r['label']: r for r in stages}
    previous_end = verification['monotonic_t0']
    log_copies = []
    for stage in stages:
        assert stage['exit_code'] == 0
        assert type(stage['elapsed_seconds']) in {float, int} and math.isfinite(stage['elapsed_seconds']) and stage['elapsed_seconds'] >= 0
        finite_seconds(stage['timeout_seconds_remaining_from_total'])
        assert stage['started_monotonic'] >= previous_end
        previous_end = stage['started_monotonic'] + stage['elapsed_seconds']
        assert previous_end <= verification['monotonic_t0'] + elapsed
        assert stage['cwd'] == str(WORK)
        log = WORK / 'logs' / (stage['label'] + '.log')
        stats = WORK / 'logs' / (stage['label'] + '.resources.txt')
        assert stage['log'] == str(log) and stage['resources'] == str(stats)
        assert sha(log) == stage['log_sha256']
        rss = re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)', stats.read_text(encoding='utf-8', errors='replace'))
        assert rss and int(rss[1]) == stage['max_rss_kib']
        started = WORK / 'logs' / (stage['label'] + '.started.json')
        ended = WORK / 'logs' / (stage['label'] + '.terminal.json')
        start_record, end_record = load(started), load(ended)
        assert 'exit_code' not in start_record
        assert all(stage[key] == value for key, value in start_record.items())
        assert all(stage[key] == value for key, value in end_record.items())
        assert end_record['exit_code'] == 0
        log_copies.extend([log, stats, started, ended])
    assert verification['peak_stage_rss_kib'] == max(row['max_rss_kib'] for row in stages)
    for label, module in [('challenge', 'Challenge.Candidate'), ('solution', 'Solution.Candidate')]:
        stage = by_label[label + '-export']
        assert stage == verification['exports'][label]
        assert stage['command'] == [native['native_executables']['lean4export']['path'], module, '--', *PUBLIC_ROOTS, *PRIMITIVES]
        export = WORK / (label + '.ndjson')
        assert stage['output'] == str(export)
        assert export.stat().st_size == stage['output_bytes'] and sha(export) == stage['output_sha256']
        assert bound[str(export)] == stage['output_sha256']
    assert by_label['comparator-default-kernel']['command'] == [native['native_executables']['coreaudit']['path'],
        str(WORK / 'challenge.ndjson'), str(WORK / 'solution.ndjson'), *PUBLIC_ROOTS]
    assert by_label['nanoda']['command'] == [production_config['nanoda'], str(WORK / 'nanoda-config.json')]
    comparison = (WORK / 'logs/comparator-default-kernel.log').read_text(encoding='utf-8')
    for sentence in ['Pinned Comparator statement, dependency and primitive comparison passed',
                     'Pinned Comparator transitive axiom check passed', 'Lean default kernel replay passed']:
        assert sentence in comparison
    nano_text = (WORK / 'logs/nanoda.log').read_text(encoding='utf-8')
    counts = re.findall(r'Checked (\d+) declarations with no errors', nano_text)
    assert len(counts) == 1 and int(counts[0]) == verification['checked_declarations']
    observed = {name.split('.{')[0] for name in re.findall(r'^axiom ([^\s]+)', nano_text, re.M)}
    assert observed <= ALLOWED and observed == set(verification['observed_axioms'])
    nano_config = load(WORK / 'nanoda-config.json')
    assert nano_config == {'use_stdin': True, 'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'],
        'unpermitted_axiom_hard_error': True, 'nat_extension': True, 'string_extension': True,
        'num_threads': 0, 'unsafe_permit_all_axioms': False, 'print_success_message': True,
        'print_axioms': True, 'pp_to_stdout': True}

    source = FLAT / 'draft/Solution.lean'
    metadata_path, generation_path = FLAT / 'draft/candidate-metadata.json', FLAT / 'draft/generation.json'
    metadata, generation = load(metadata_path), load(generation_path)
    source_hash, source_size = sha(source), source.stat().st_size
    assert 0 < source_size <= 2_000_000
    assert source_hash == metadata['solution_sha256'] == verification['source_sha256'] == confirmation['source_sha256']
    assert source_size == metadata['solution_bytes'] == verification['source_bytes']
    assert metadata['prepared_manifest_sha256'] == FLAT_PIN and metadata['all_non_import_bytes_preserved'] is True
    assert metadata['upload_ready'] is False and metadata['compiler_inputs_modified'] is False
    assert metadata['score'] == verification['score'] and metadata['public_theorem_names'] == PUBLIC_ROOTS
    assert generation['upload_ready'] is False
    assert generation['files'] == [
        {'path': 'Solution.lean', 'bytes': source_size, 'sha256': source_hash},
        {'path': 'candidate-metadata.json', 'bytes': metadata_path.stat().st_size, 'sha256': sha(metadata_path)}]
    assert bound[str(source)] == source_hash
    assert bound[str(metadata_path)] == sha(metadata_path) and bound[str(generation_path)] == sha(generation_path)
    source.read_bytes().decode('utf-8')
    for record, module in zip(verification['compiled_modules'], MODULES):
        module_path = Path(*module.split('.'))
        path = WORK / 'source' / module_path.with_suffix('.lean')
        olean = WORK / 'lib' / module_path.with_suffix('.olean')
        assert record == by_label['ordinary-' + module]
        assert sha(path) == record['source_sha256'] == bound[str(path)]
        assert sha(olean) == record['olean_sha256'] == bound[str(olean)]
    assert sha(WORK / 'source/Solution/Candidate.lean') == source_hash

    # Strict whitelist; large proof artifacts stay in place and are hash-bound.
    copies = {}
    def add(path, relative, limit=2_000_000):
        path = Path(path)
        assert path.is_file() and path.stat().st_size <= limit
        assert path.suffix in {'.lean', '.json', '.log', '.txt', '.md'}
        with path.open('rb') as handle:
            assert handle.read(4) != b'\x7fELF'
        assert relative not in copies and not Path(relative).is_absolute() and '..' not in Path(relative).parts
        copies[relative] = {'path': path, 'bytes': path.stat().st_size, 'sha256': sha(path)}
    add(source, 'proof/Solution.lean')
    for path in [verification_path, deadline_path, WORK / 'nanoda-config.json']:
        add(path, 'verification/cold/' + path.name)
    add(terminal_path, 'verification/mirror-terminal.json')
    add(confirmation_path, 'verification/root-session-confirmation.json')
    add(GATE, 'verification/production-gate.json')
    add(PREPARED, 'verification/collector-prepared.json')
    add(PROD / 'prepared-files.json', 'verification/production-prepared.json')
    add(PROD / 'configuration.json', 'verification/production-configuration.json')
    add(FLAT / 'prepared-files.json', 'verification/flatten-prepared.json')
    for path in [metadata_path, generation_path]:
        add(path, 'verification/generation/' + path.name)
    for path in log_copies:
        add(path, 'verification/cold/logs/' + path.name)
    for relative in ['ChallengeDeps.lean', 'ChallengeDeps/CandidateSpec.lean', 'Challenge/Candidate.lean']:
        add(WORK / 'source' / relative, 'verification/trusted-local-overlay/' + relative)
    assert sum(row['bytes'] for row in copies.values()) <= 16_000_000
    for row in copies.values():
        original_pins[str(row['path'])] = row['sha256']
    stable()

    ratio, baseline = Fraction(int(P), int(Q)), Fraction(int(P), int(R_Q))
    gain = ratio - baseline
    assert gain > 0
    with localcontext() as ctx:
        ctx.prec = 80
        percent = str(100 * Decimal(ratio.numerator) / Decimal(ratio.denominator))
        baseline_percent = str(100 * Decimal(baseline.numerator) / Decimal(baseline.denominator))
        gain_percent = str(100 * Decimal(gain.numerator) / Decimal(gain.denominator))
    fields = load(OLD_MATH / 'website-fields.draft.json')
    fields.update({'schema': 'native-v4-local-cold-verified-website-fields-v1',
        'suggested_result_name': 'single-exception-overlap-native-v4-20261019',
        'summary': ('Strengthens the current s1R nine-point Gram-defect certificate by localizing every separated '
            'window below a raised threshold to one exceptional cell or its reflection. Consecutive exceptional '
            'windows force their common gap into disjoint intervals in all four orientations. Pairing windows '
            'then improves the summed lower bound with one fixed boundary loss. The existing separation, '
            'matching and actual zero-counting argument gives unconditional dyadic and cumulative bounds for '
            'distinct critical-line zeros. The complete deduplicated source retains inherited attributions and '
            'licenses. It passed a single local 3200-second generation-through-receipt run including cold Lean, '
            'native exact statement/dependency/primitive comparison, transitive axiom audit, Lean default '
            'kernel and serial independent nanoda. Website acceptance remains pending.'),
        'proof_file': {'path': 'proof/Solution.lean', 'bytes': source_size, 'sha256': source_hash,
            'copied_into_materials': True, 'version': 'v4 deduplicated actual cold-generated source'},
        'ready_for_manual_website_submission': True, 'automatic_upload_performed': False,
        'website_status': 'Pending separate website verification; local PASS is not website acceptance',
        'submitted': False, 'official_website_acceptance': False})
    status = {'schema': 'native-v4-local-verified-materials-v1',
        'collected_at_utc': datetime.now(timezone.utc).isoformat(),
        'source_sha256': source_hash, 'source_bytes': source_size,
        'local_single_file_verified': True, 'single_total_elapsed_seconds': elapsed,
        'checked_declarations': verification['checked_declarations'], 'observed_axioms': sorted(observed),
        'nanoda_threads': 0, 'trusted_native_tools_preinstalled': True,
        'trusted_tool_build_time_included_in_proof_budget': False,
        'peak_stage_rss_kib': verification['peak_stage_rss_kib'],
        'RLIMIT_FSIZE_bytes': verification['RLIMIT_FSIZE_bytes'], 'RAM_limit_claimed': False,
        'score': fields['score'], 'comparison_record': {'numerator': P, 'denominator': R_Q},
        'score_percent_decimal': percent, 'comparison_percent_decimal': baseline_percent,
        'strict_gain': {'numerator': str(gain.numerator), 'denominator': str(gain.denominator)},
        'gain_percentage_points_decimal': gain_percent, 'public_theorem_names': PUBLIC_ROOTS,
        'production_session_id': 84529, 'production_session_exit_code': 0,
        'production_gate_sha256': GATE_PIN, 'production_prepared_sha256': PROD_PIN,
        'root_confirmation_sha256': args.root_confirmation_sha256,
        'collector_prepared_sha256': args.prepared_sha256,
        'source_copied_byte_identically': True, 'all_bound_files_rehashed_before_and_after_collection': True,
        'large_exports_oleans_native_binaries_and_cache_copied': False,
        'post_verification_collection_outside_proof_budget': True,
        'official_runtime_equivalence_claimed': False,
        'submitted': False, 'official_website_acceptance': False}
    native_evidence = {'schema': 'native-installation-pinned-excerpt-v1',
        'original_installation_path': str(install_path), 'original_installation_sha256': sha(install_path),
        'full_installation_receipt_copied': False, 'excerpt_is_not_a_replacement_for_original_receipt': True,
        'setup_prepared_sha256': selected['setup_prepared_sha256'],
        'source_pins': install['source_pins'], 'source_provenance': native['source_provenance'],
        'native_executables': native['native_executables'],
        'native_runtime_closure_pins': native['native_runtime_closure_pins'],
        'runtime_symlink_resolutions': resolutions, 'commands': install['commands'],
        'submitted': False, 'official_website_acceptance': False}
    readme = f'''# 相邻例外窗口排除：原生 v4 提交材料

精确候选为 `{P}/{Q}`，约 **{percent[:22]}%**。本次比较纪录为 `{P}/{R_Q}`；增益为 `{gain.numerator}/{gain.denominator}`（比例），约 `{gain_percent}` 个百分点。实际提交前仍应核当时网站精确纪录。

上传 `proof/Solution.lean`（{source_size} UTF-8 bytes，SHA256 `{source_hash}`），填写 `submission-fields.json`。这是 v4 的实际冷生成源；此前用户上传的 v3 和旧材料保持原字节。不要用本包 trusted-local-overlay 规格代替网站生成的可信规格。

root 确认 session 84529 真实 exit0；完整本地统一计时为 **{elapsed:.6f} 秒**，含所有 proof pins、生成、四模块冷编译、两个原生 export、Comparator/default kernel、serial nanoda、最终哈希和 fsynced receipts。可信原生工具预先安装，其构建不属于这次证明计时；工具安装身份和运行闭包已在计时内核验。没有复用用户 olean，也没有减少比较范围或允许公理集。nanoda 以 num_threads=0 完整检查 {verification['checked_declarations']} 个声明。

证据见 `verification/`；完整大型 export 仅记录其字节数和 SHA，不复制 NDJSON、olean、ELF 或 cache。8GiB 是单文件大小限制；没有声称 RAM 上限。峰值阶段 RSS 为 {verification['peak_stage_rss_kib']} KiB。收集材料另在证明结束后进行，不并入或改写原3200秒收据。

`MATHEMATICAL-NOTE.zh.md` 沿用已冻结数学说明中的同一 κ；此版本去除生产源重复代码，没有新增数学前提。源中所有版权和许可保留。

**本目录尚未提交，网站官方接受仍待独立确认。** 旧 v3 的网站运行状态不据本地 v4 的通过推断。网站记录及实际协议仍以官网最终结果为准。
'''
    original_math = (OLD_MATH / 'MATHEMATICS.zh.md').read_text(encoding='utf-8')
    marker = '\n本材料逐source接口和纯有理ratio核对；'
    assert original_math.count(marker) == 1
    math_note = original_math.split(marker)[0] + f'''\n\n本数学说明沿用冻结说明的数学正文，精确 κ={P}/{Q}。本包 v4 在 session 84529 的单次3200秒本地完整冷验收已由 root 终结确认；ordinary Lean、native Comparator/default kernel 和 serial nanoda 证据分别保留。此前失败的 v0 和 v3 单独诊断不被重新分类。官网提交与官方接受尚未发生。\n'''
    math_reference = {'path': str(OLD_MATH / 'MATHEMATICS.zh.md'),
        'sha256': sha(OLD_MATH / 'MATHEMATICS.zh.md'), 'mathematical_prefix_preserved': True,
        'historical_status_paragraph_replaced_with_current_local_status': True,
        'same_exact_kappa': fields['score'], 'submitted': False, 'official_website_acceptance': False}

    DEST.mkdir()
    try:
        for relative, info in copies.items():
            target = DEST / relative
            assert target.resolve().is_relative_to(DEST)
            target.parent.mkdir(parents=True, exist_ok=True)
            with info['path'].open('rb') as source_handle, target.open('xb') as target_handle:
                for block in iter(lambda: source_handle.read(1048576), b''):
                    target_handle.write(block)
                target_handle.flush(); os.fsync(target_handle.fileno())
            assert target.stat().st_size == info['bytes'] and sha(target) == info['sha256']
        write_new(DEST / 'submission-fields.json', fields)
        write_new(DEST / 'verification-status.json', status)
        write_new(DEST / 'verification/native-installation-excerpt.json', native_evidence)
        write_new(DEST / 'verification/mathematics-reference.json', math_reference)
        write_new(DEST / 'website-status.json', {'status': 'pending', 'source_version': 'native-v4',
            'local_verification_does_not_establish_website_acceptance': True,
            'submitted': False, 'official_website_acceptance': False})
        text_new(DEST / 'README.zh.md', readme)
        text_new(DEST / 'MATHEMATICAL-NOTE.zh.md', math_note)
        assert sha(DEST / 'proof/Solution.lean') == source_hash
        stable()
        files = [{'path': path.relative_to(DEST).as_posix(), 'bytes': path.stat().st_size, 'sha256': sha(path)}
                 for path in sorted(DEST.rglob('*')) if path.is_file()]
        assert all(Path(row['path']).suffix in {'.lean', '.json', '.log', '.txt', '.md'} for row in files)
        write_new(DEST / 'manifest.json', {'schema': 'native-v4-submission-materials-v1',
            'files': files, 'source_sha256': source_hash, 'local_verification_passed': True,
            'collector_prepared_sha256': args.prepared_sha256,
            'root_confirmation_sha256': args.root_confirmation_sha256,
            'all_frozen_inputs_old_drafts_bound_files_and_symlinks_unchanged': True,
            'submitted': False, 'official_website_acceptance': False})
        print(json.dumps({'materials_collected': True, 'destination': str(DEST),
            'manifest_sha256': sha(DEST / 'manifest.json'), 'solution_sha256': source_hash,
            'submitted': False, 'official_website_acceptance': False}), flush=True)
    except BaseException as error:
        write_new(DEST / 'COLLECTION-FAILED.json', {'failed': True,
            'error_type': type(error).__name__, 'error': str(error),
            'submitted': False, 'official_website_acceptance': False})
        raise

if __name__ == '__main__':
    main()
