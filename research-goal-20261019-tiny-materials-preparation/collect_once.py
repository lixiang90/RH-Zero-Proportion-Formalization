"""One-shot collection after root-confirmed terminal cold PASS. Not executed by preparation.

No Lean, export, solver, network, Git operation or website submission is run.
Sources and evidence are copied byte-for-byte only after every success gate.
Existing submission drafts and all bound production inputs are read-only.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
from decimal import Decimal, localcontext
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PREPARED = HERE / 'prepared-files.json'
PROD = ROOT / 'research-goal-20261018-tiny-production-preparation'
FLAT = ROOT / 'research-goal-20261018-tiny-flatten-preparation-v3'
WORK = Path('/var/tmp/rh-zero-20261015/tiny-production-v0')
MIRROR = ROOT / 'tmp/current-s1r-tiny-20261018/production-v0'
DEST = ROOT / 'submission/single-exception-overlap-20261018'
P = '3337839448633819172184136761695440236797'
Q = '4955319193827760237900000000000000000000'
R_Q = '4955319193847235264050000000000000000000'
PROD_PIN = '8de6adf94411254d8aef96e625faa1dc869069848049e99eab31e38a06e957c1'
FLAT_PIN = '8d866f77503210091280574f6a14fcead5461f07c156f383f1b67f78ee52ab32'
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}
MODULES = ['ChallengeDeps', 'ChallengeDeps.CandidateSpec', 'Challenge.Candidate', 'Solution.Candidate']
TOOLS = {'Export', 'Export.Parse', 'ExporterMain', 'Comparator', 'Comparator.Axioms',
         'Comparator.Compare', 'Comparator.Util', 'ComparatorMain', 'CoreAudit'}
PUBLIC_ROOTS = ['candidate_strict_improvement', 'candidate_critical_line_bound',
                'candidate_critical_line_bound_cumulative']

def load(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for part in iter(lambda: f.read(1048576), b''):
            h.update(part)
    return h.hexdigest()

def write_new(path, obj):
    with Path(path).open('x', encoding='utf-8', newline='\n') as f:
        json.dump(obj, f, ensure_ascii=False, indent=2); f.write('\n')

def text_new(path, text):
    with Path(path).open('x', encoding='utf-8', newline='\n') as f:
        f.write(text)

def main():
    assert __debug__, 'Assertions must remain enabled'
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepared-sha256', required=True)
    parser.add_argument('--root-confirmation', required=True)
    parser.add_argument('--root-confirmation-sha256', required=True)
    args = parser.parse_args()
    assert ROOT == Path('/mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization')
    assert sha(PREPARED) == args.prepared_sha256
    prep = load(PREPARED)
    original_pins = {}
    for row in prep['files'] + prep['dependencies']:
        path = ROOT / row['path']
        assert path.stat().st_size == row['bytes'] and sha(path) == row['sha256'], row['path']
        original_pins[str(path)] = row['sha256']
    assert sha(PROD / 'prepared-files.json') == PROD_PIN
    assert sha(FLAT / 'prepared-files.json') == FLAT_PIN
    confirmation_path = Path(args.root_confirmation).resolve()
    assert confirmation_path.is_relative_to(ROOT / 'research-goal-20261016/gates')
    assert sha(confirmation_path) == args.root_confirmation_sha256
    confirmation = load(confirmation_path)
    assert confirmation['confirmed_by'] == '/root'
    assert confirmation['root_confirmed_session_terminal'] is True
    assert confirmation['production_session_id'] == 86707
    assert confirmation['production_session_exit_code'] == 0
    assert confirmation['production_prepared_sha256'] == PROD_PIN
    assert confirmation['flatten_prepared_sha256'] == FLAT_PIN
    assert confirmation['collector_prepared_sha256'] == args.prepared_sha256
    terminal_tool_result = confirmation['terminal_tool_result']
    assert terminal_tool_result['exit_code'] == 0
    stdout_finals = []
    for line in terminal_tool_result['output'].splitlines():
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict) and 'total_elapsed_seconds_through_all_receipts' in value:
            stdout_finals.append(value)
    assert len(stdout_finals) == 1, 'Root must retain the actual final stdout JSON from the terminal session result'
    stdout_final = stdout_finals[0]
    assert stdout_final['local_single_file_verified'] is True
    assert stdout_final['official_website_acceptance'] is False
    elapsed = stdout_final['total_elapsed_seconds_through_all_receipts']
    assert isinstance(elapsed, (int, float)) and 0 < elapsed <= 3200
    assert not DEST.exists(), 'Exclusive final-material directory already exists; no retry/overwrite'
    for failure in [WORK / 'failure.json', MIRROR / 'failure.json']:
        assert not failure.exists(), str(failure)
    verification_path = WORK / 'verification.json'
    deadline_path = WORK / 'deadline-receipt.json'
    terminal_path = MIRROR / 'terminal.json'
    verification = load(verification_path)
    deadline = load(deadline_path)
    terminal = load(terminal_path)
    assert verification['failed'] is False
    for field in ['local_single_file_verified', 'ordinary_single_file_lean_passed',
                  'statement_equality_proved', 'permitted_axioms_checked',
                  'default_kernel_replay_passed', 'independent_nanoda_passed',
                  'inputs_unchanged', 'total_deadline_enforced']:
        assert verification[field] is True, field
    assert verification['official_website_acceptance'] is False and verification['submitted'] is False
    assert verification['budget_seconds'] == 3200 and verification['retry_count'] == 0
    assert verification['cached_user_oleans_used'] is False
    assert verification['stage'] == 'all-proof-stages-passed'
    assert verification['prepared_sha256'] == PROD_PIN
    assert terminal['linux_work_directory'] == str(WORK)
    for receipt in [deadline, terminal]:
        assert receipt['verification_receipt_sha256'] == sha(verification_path)
        assert receipt['total_limit_seconds'] == 3200 and receipt['within_total_limit'] is True
        assert receipt['official_website_acceptance'] is False
        assert 0 < receipt['elapsed_seconds_after_fsynced_verification_receipt'] <= elapsed <= 3200
    assert deadline == {k: v for k, v in terminal.items() if k != 'linux_work_directory'}
    assert verification['score'] == {'numerator': P, 'denominator': Q}
    assert verification['current_record']['exactRational'] == {'numerator': P, 'denominator': R_Q}
    assert set(verification['observed_axioms']) <= ALLOWED
    assert isinstance(verification['checked_declarations'], int) and verification['checked_declarations'] > 0
    assert [r['module'] for r in verification['compiled_modules']] == MODULES
    assert {r['module'] for r in verification['tool_compiled_modules']} == TOOLS
    assert len(verification['tool_compiled_modules']) == len(TOOLS)
    required_labels = {'compiler-version', 'generation', 'challenge-export', 'solution-export',
                       'comparator-default-kernel', 'nanoda'}
    required_labels |= {'ordinary-' + m for m in MODULES}
    required_labels |= {'tool-' + m for m in TOOLS}
    stages = verification['stages']
    assert len(stages) == len(required_labels)
    assert {r['label'] for r in stages} == required_labels
    for stage in stages:
        assert stage['exit_code'] == 0 and stage['elapsed_seconds'] >= 0
        assert 0 < stage['timeout_seconds_remaining_from_total'] <= 3200
        log = Path(stage['log'])
        stats = Path(stage['resources'])
        assert log.is_relative_to(WORK / 'logs') and stats.is_relative_to(WORK / 'logs')
        assert log.is_file() and stats.is_file()
        assert sha(log) == stage['log_sha256']
        text = stats.read_text(encoding='utf-8', errors='replace')
        rss = re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)', text)
        assert rss and int(rss[1]) == stage['max_rss_kib']
    comparison = (WORK / 'logs/comparator-default-kernel.log').read_text(encoding='utf-8')
    for sentence in ['Pinned Comparator statement, dependency and primitive comparison passed',
                     'Pinned Comparator transitive axiom check passed', 'Lean default kernel replay passed']:
        assert sentence in comparison
    nano_text = (WORK / 'logs/nanoda.log').read_text(encoding='utf-8')
    checked = re.search(r'Checked (\d+) declarations with no errors', nano_text)
    assert checked and int(checked[1]) == verification['checked_declarations']
    observed = {n.split('.{')[0] for n in re.findall(r'^axiom ([^\s]+)', nano_text, re.M)}
    assert observed <= ALLOWED and observed == set(verification['observed_axioms'])
    config = load(WORK / 'nanoda-config.json')
    assert set(config['permitted_axioms']) == ALLOWED
    assert config['unsafe_permit_all_axioms'] is False and config['unpermitted_axiom_hard_error'] is True
    assert config['use_stdin'] is True
    # Read and hash the large exports in place; never place them in submission/Git.
    for label in ['challenge', 'solution']:
        export = WORK / (label + '.ndjson')
        expected = verification['exports'][label]
        assert export.stat().st_size == expected['output_bytes']
        assert sha(export) == expected['output_sha256']
    source = FLAT / 'draft/Solution.lean'
    source_hash = sha(source)
    source_size = source.stat().st_size
    assert 0 < source_size <= 2_000_000
    assert source_hash == verification['source_sha256']
    assert source_size == verification['source_bytes']
    assert sha(WORK / 'source/Solution/Candidate.lean') == source_hash
    generation = load(FLAT / 'draft/candidate-metadata.json')
    assert generation['solution_sha256'] == source_hash and generation['solution_bytes'] == source_size
    assert generation['prepared_manifest_sha256'] == FLAT_PIN
    assert generation['all_non_import_bytes_preserved'] is True
    assert generation['upload_ready'] is False
    source.read_bytes().decode('utf-8')
    for module in MODULES:
        path = WORK / 'source' / Path(*module.split('.')).with_suffix('.lean')
        assert verification['bound_sha256_before_and_after'][str(path)] == sha(path)
    gate_path = Path(verification['gate_path'])
    assert gate_path.is_relative_to(ROOT / 'research-goal-20261016/gates')
    assert sha(gate_path) == verification['gate_sha256']
    # Everything is checked before the destination is created. A failure after
    # creation is retained explicitly and never silently resumed or repaired.
    copies = {}
    def add(path, relative, limit=20_000_000):
        path = Path(path)
        assert path.is_file() and path.stat().st_size <= limit
        assert path.suffix not in {'.ndjson', '.olean', '.ilean', '.tar', '.gz'}
        assert relative not in copies
        copies[relative] = {'path': path, 'bytes': path.stat().st_size, 'sha256': sha(path)}
    add(source, 'proof/Solution.lean', 2_000_000)
    for path in [verification_path, deadline_path, WORK / 'nanoda-config.json']:
        add(path, 'verification/cold/' + path.name)
    add(terminal_path, 'verification/mirror-terminal.json')
    add(confirmation_path, 'verification/root-session-confirmation.json')
    add(gate_path, 'verification/production-gate.json')
    add(PROD / 'prepared-files.json', 'verification/production-prepared.json')
    add(PROD / 'configuration.json', 'verification/production-configuration.json')
    add(FLAT / 'prepared-files.json', 'verification/flatten-prepared.json')
    for name in ['candidate-metadata.json', 'generation.json']:
        add(FLAT / 'draft' / name, 'verification/generation/' + name)
    for path in sorted((WORK / 'logs').iterdir()):
        assert path.is_file() and path.suffix in {'.json', '.log', '.txt'}
        add(path, 'verification/cold/logs/' + path.name)
    for relative in ['ChallengeDeps.lean', 'ChallengeDeps/CandidateSpec.lean', 'Challenge/Candidate.lean']:
        add(WORK / 'source' / relative, 'verification/trusted-local-overlay/' + relative)
    assert sum(r['bytes'] for r in copies.values()) <= 64_000_000
    original_pins[str(confirmation_path)] = args.root_confirmation_sha256
    for path, expected in original_pins.items():
        assert sha(path) == expected
    ratio, baseline = Fraction(int(P), int(Q)), Fraction(int(P), int(R_Q))
    gain = ratio - baseline
    assert gain > 0
    with localcontext() as ctx:
        ctx.prec = 80
        percent = str(100 * Decimal(ratio.numerator) / Decimal(ratio.denominator))
        baseline_percent = str(100 * Decimal(baseline.numerator) / Decimal(baseline.denominator))
        gain_percent = str(100 * Decimal(gain.numerator) / Decimal(gain.denominator))
    summary = ('Uses the accepted s1R nine-gap Gram-defect certificate to localize every window below '
        'a higher threshold to a single exceptional cell or its reflection. Consecutive exceptional '
        'windows force their shared physical gap into disjoint intervals in all four orientations. '
        'The resulting adjacent-window energy bound yields a stronger summed estimate with one fixed '
        'boundary loss, and the existing separation and matching argument gives unconditional dyadic '
        'and cumulative bounds for distinct critical-line zeros. The complete upload source has passed '
        'cold ordinary Lean, exact public-statement/dependency/primitive comparison, the transitive '
        'axiom audit, Lean default-kernel replay and independent nanoda replay within one 3200-second '
        'generation-through-receipt budget. All inherited attribution and licenses are retained. '
        'This is a local verification result; website acceptance remains pending.')
    fields = {'suggested_result_name': 'lixiang90-single-exception-overlap-20261018',
        'public_display_name': 'Li Xiang',
        'method': 'Geometric exclusion of consecutive exceptional nine-gap windows',
        'score': {'numerator': P, 'denominator': Q}, 'summary': summary,
        'coding_harness_optional': 'Codex', 'ai_model_optional': None,
        'proof_file': 'proof/Solution.lean', 'proof_file_generated': True,
        'proof_file_sha256': source_hash, 'proof_file_bytes': source_size,
        'ordinary_full_chain_passed': True, 'local_cold_comparator_nanoda_passed': True,
        'ready_for_manual_website_submission': True,
        'submitted': False, 'official_website_acceptance': False}
    status = {'schema': 'single-exception-local-verified-materials-v1',
        'collected_at_utc': datetime.now(timezone.utc).isoformat(), 'source_sha256': source_hash,
        'source_bytes': source_size, 'local_single_file_verified': True,
        'single_total_elapsed_seconds': elapsed, 'checked_declarations': verification['checked_declarations'],
        'observed_axioms': sorted(observed), 'peak_stage_rss_kib': verification['peak_stage_rss_kib'],
        'RLIMIT_FSIZE_bytes': verification['RLIMIT_FSIZE_bytes'], 'RAM_limit_claimed': False,
        'score': fields['score'], 'comparison_record': {'numerator': P, 'denominator': R_Q},
        'score_percent_decimal': percent, 'comparison_percent_decimal': baseline_percent,
        'strict_gain': {'numerator': str(gain.numerator), 'denominator': str(gain.denominator)},
        'gain_percentage_points_decimal': gain_percent,
        'public_theorem_names': PUBLIC_ROOTS, 'production_session_id': 86707,
        'production_session_exit_code': 0, 'root_confirmation_sha256': args.root_confirmation_sha256,
        'collector_prepared_sha256': args.prepared_sha256,
        'source_copied_byte_identically': True, 'large_exports_oleans_and_cache_copied': False,
        'submitted': False, 'official_website_acceptance': False}
    readme = f'''# 相邻例外窗口排除：网站提交材料

本目录包含完整上传源、提交字段、数学说明及本地冷验证证据；尚未向网站提交，尚未取得网站官方接受。

精确候选为 `{P} / {Q}`，约 **{percent[:22]}%**。本次比较的已验证纪录为 `{P} / {R_Q}`；严格增益为 `{gain.numerator}/{gain.denominator}`（比例），约 `{gain_percent}` 个百分点。实际提交前应再核当时网站精确纪录。

上传 `proof/Solution.lean`（{source_size} UTF-8 bytes，SHA256 `{source_hash}`），字段见 `submission-fields.json`。不要上传本目录的 trusted-local-overlay 规格代替官网生成的可信规格。

本地冷验证真实 exit0，统一总计时 **{elapsed:.6f} 秒**，含文本生成、四模块冷编译、可信工具准备、两个 export、Comparator/default kernel、nanoda、最终哈希和 receipt。nanoda 完整重放 {verification['checked_declarations']} 个声明；允许公理只有 propext、Quot.sound、Classical.choice。三个官网公开 theorem 的完整陈述、依赖、primitive 和传递公理均已比较。

资源和原始日志在 `verification/cold/`。8GiB 是单文件大小限制，不能解释为 RAM 上限；峰值阶段 RSS 为 {verification['peak_stage_rss_kib']} KiB。大型 NDJSON、olean 和 package cache 均未复制至提交材料。官网受限 verifier、最新协议及最终 attestation 仍须由网站实际运行。

所有源版权、许可及来源说明以字节相同方式保留于上传源中。本目录是新材料包；旧 `submission/tiny-overlap-20261018` 草案和此前冻结输入保持原字节。
'''
    math = f'''# 数学改进及形式化链条

采用当前已接受 s1R 的 W9 窗函数、权重、压力和全局计数框架。令 c₀=893616123055294719/10²⁰，δ=389500523/10²⁰，c=c₀+δ；新的高阈值为 c₀+2δ=893616123834295765/10²⁰。

完整的13,046个原数值叶中，只有第462例外叶不能承受 κscale×779001046 的提高扣款，κscale=335544320000000000；其余13,045叶均能证明局部能量达到高阈值，最小余量为81738199346000000。例外叶仍沿用原 c₀ 下界。形式化强化的是整棵覆盖证书：低于高阈值的实际窗口只能落在该例外单元或其反射，不将数值试验当作全局定理。

例外单元的相邻差分闭区间，下界为 [64168,33989,64287,34192,64031,65043,33724,64461]/32768，上界为 [65648,34980,65278,35097,65033,66904,34464,67523]/32768。在任一反射方向，前一窗口第二个物理间隙至多34980/32768；后一窗口第一个物理间隙至少64168/32768。两者是同一个共享间隙，而34980<64168；所以四种方向组合下，相邻两窗都例外均矛盾。这是利用重叠窗口几何兼容性的新增推理。

至少一窗不例外，因此相邻能量和至少(c₀+2δ)+c₀=2c。结合每窗原下界 c₀，逐对归纳得到 N 窗总能量至少 cN−δ；δ只支付一次有限边界损失。现有 W9 分离、排序、带估计和匹配框架把该总窗估计连接到实际 Gram 缺陷，再连接实际 ζ 函数零点计数。

H=6721290091768038344368273523390880473594/10⁴⁰，B₉=456111945004000000/10²⁰。精确比值 (H−B₉)/(1−c) 等于 {P}/{Q}，严格高于本次记录 {P}/{R_Q}。最终定理无新增局部下界或解析假设，同时给出二倍区间及从0累积区间内 distinct critical-line zeros 的下界。

三个公开根为 candidate_strict_improvement、candidate_critical_line_bound、candidate_critical_line_bound_cumulative；完整陈述由官网模板给出并由 Comparator 比较。本地 ordinary、默认 Lean kernel 和 nanoda 结果均在证据包中；网站官方接受尚未发生。
'''
    DEST.mkdir()
    try:
        for relative, info in copies.items():
            target = DEST / relative
            assert target.resolve().is_relative_to(DEST)
            target.parent.mkdir(parents=True, exist_ok=True)
            with info['path'].open('rb') as src, target.open('xb') as out:
                for part in iter(lambda: src.read(1048576), b''):
                    out.write(part)
            assert target.stat().st_size == info['bytes'] and sha(target) == info['sha256']
        write_new(DEST / 'submission-fields.json', fields)
        write_new(DEST / 'verification-status.json', status)
        text_new(DEST / 'README.zh.md', readme)
        text_new(DEST / 'MATHEMATICAL-NOTE.zh.md', math)
        assert sha(DEST / 'proof/Solution.lean') == source_hash == sha(source)
        for path, expected in original_pins.items():
            assert sha(path) == expected, 'A frozen input or old draft changed during collection'
        assert not (WORK / 'failure.json').exists() and not (MIRROR / 'failure.json').exists()
        files = [{'path': p.relative_to(DEST).as_posix(), 'bytes': p.stat().st_size, 'sha256': sha(p)}
                 for p in sorted(DEST.rglob('*')) if p.is_file()]
        assert not any(Path(r['path']).suffix in {'.ndjson', '.olean', '.ilean'} for r in files)
        write_new(DEST / 'manifest.json', {'schema': 'single-exception-submission-materials-v1',
            'files': files, 'source_sha256': source_hash, 'local_verification_passed': True,
            'collector_prepared_sha256': args.prepared_sha256,
            'root_confirmation_sha256': args.root_confirmation_sha256,
            'all_frozen_inputs_and_old_drafts_unchanged': True,
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
