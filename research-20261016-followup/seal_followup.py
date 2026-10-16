"""Bind current Lean receipts and research inputs without asserting a new record."""
from pathlib import Path
from decimal import Decimal, localcontext, ROUND_DOWN
from fractions import Fraction as F
import argparse, hashlib, json, re, subprocess

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).parent
PACKAGE = ROOT/'StructuralW10Followup20261016'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
REQUIRED = {'scalar_Checker', 'scalar_Data', 'scalar_Basin7', 'scalar_FwBasin7',
            'MatchingThreshold', 'KernelPair123128', 'WindowProfileGeneral',
            'WindowMajorantGeneral', 'NewWindows', 'NewLedger', 'FourierMinorantTransfer'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--stage', action='store_true')
    args = parser.parse_args()
    modules = {}
    for source in sorted(PACKAGE.glob('*.lean')):
        modules['StructuralW10Followup20261016.'+source.stem] = {
            'source_sha256': sha(source), 'ordinary_lean_passed': False,
            'independent_nanoda_this_run': False}
    for receipt in sorted(HERE.glob('*verification.json')):
        doc = json.loads(receipt.read_bytes())
        for row in doc.get('modules', []):
            if row['module'] not in modules:
                continue
            info = modules[row['module']]
            log = HERE/row['log']
            current = (row['source_sha256'] == info['source_sha256'] and
                       log.is_file() and sha(log) == row['log_sha256'])
            if row.get('passed') and row.get('source_unchanged') and current:
                text = log.read_bytes().decode('utf8', errors='replace')
                groups = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', text)
                axioms = set(a.strip() for group in groups for a in group.split(',') if a.strip())
                assert axioms <= STANDARD, (row['module'], axioms)
                assert 'sorryAx' not in text
                info.update({'ordinary_lean_passed': True,
                             'receipt': str(receipt.relative_to(ROOT)).replace('\\', '/'),
                             'receipt_sha256': sha(receipt),
                             'log': str(log.relative_to(ROOT)).replace('\\', '/'),
                             'log_sha256': sha(log), 'printed_axioms': sorted(axioms)})
    checked = [m.rsplit('.', 1)[-1] for m, v in modules.items() if v['ordinary_lean_passed']]
    independent = HERE/'window_independent_audit.json'
    audit = json.loads(independent.read_bytes())
    assert audit['all_checks_passed']
    for path, digest in audit['input_sha256'].items():
        assert sha(ROOT/path) == digest, path
    assert sha(HERE/'window_independent_audit.py') == audit['script_sha256']
    params = HERE/'window_reweight_rational.json'
    candidate = json.loads(params.read_bytes())
    assert candidate['all_exact_admissibility_checks_passed']
    ledger = (PACKAGE/'NewLedger.lean').read_text(encoding='utf8')
    atext = ledger.split('def aN :', 1)[1].split('def bN :', 1)[0]
    btext = ledger.split('def bN :', 1)[1].split('def a (', 1)[0]
    actual_a = {(int(i), int(j)): int(v) for i, j, v in
                re.findall(r'\| (\d+), (\d+) => (\d+)', atext)}
    actual_b = [int(v) for v in re.findall(r'\| \d+ => (\d+)', btext)]
    assert all(actual_a.get((i, j), 0) == a for i, j, a in candidate['a_upper'])
    assert actual_b == candidate['b_numerators']
    kappa = F(candidate['conditional_kappa_exact'])
    assert kappa == (F(candidate['window_H_lower'])-F(candidate['B_exact']))/(1-F(candidate['proposed_floor_exact']))
    with localcontext() as ctx:
        ctx.prec = 90
        percent = Decimal(100*kappa.numerator)/Decimal(kappa.denominator)
        truncated = percent.quantize(Decimal('0.0000000001'), rounding=ROUND_DOWN)
    status = {'scope': __doc__, 'modules': modules,
              'ordinary_lean_verified_modules': len(checked),
              'actual_Fw_basin7_ordinary_lean_proven': 'scalar_FwBasin7' in checked,
              'all_69_actual_Fw_basins_lean_proven': False,
              'old_W10_global_floor_proven': False,
              'new_window_global_floor_proven': False,
              'new_window_operator_counting_bridge_complete': False,
              'new_unconditional_zero_proportion_proven': False,
              'upload_ready': False, 'submitted': False,
              'candidate_parameter_sha256': sha(params),
              'candidate_conditional_kappa_exact': str(kappa),
              'candidate_conditional_percent_decimal': str(percent),
              'candidate_conditional_percent_truncated10': str(truncated),
              'independent_window_audit_sha256': sha(independent),
              'remaining': ['Full global coverage for the old W10 candidate',
                            'New-window finite-height operator and counting specialization',
                            'Whole-domain energy lower bound for the new window and weights',
                            'Size-compliant unconditional source, statement comparison and dual-kernel verification']}
    (HERE/'proof-status.json').write_text(json.dumps(status, indent=2)+'\n', encoding='utf8')
    note = ('研究材料草稿：尚不可提交网站\n\n'
            '标题：重新设计 Fourier 窗函数与十点配对权重\n'
            '作者：Li Xiang\n'
            '条件目标比例（网站截断十位）：'+str(truncated)+'%\n'
            '精确条件分数：'+str(kappa)+'\n'
            '局部 floor 目标：'+candidate['proposed_floor_exact']+'（未证明）\n'
            '压力 B：'+candidate['B_exact']+'\n'
            '窗函数参数：window_exact_parameters.json 中的 24 模窗\n\n'
            '不能上传的原因：全域下界未证明；新窗有限高度算子与实际零点计数桥未完成；'
            '尚无无条件单文件、严格声明比较或新结果的双内核通过证据。'
            '任何数值局部极小值均只是全局下确界的上界，不能替代缺失定理。\n')
    (HERE/'submission-research-note.txt').write_text(note, encoding='utf8')
    if args.stage:
        assert REQUIRED <= set(checked), sorted(REQUIRED-set(checked))
        files = {'.gitattributes', 'README.md'}
        for directory in [PACKAGE, HERE]:
            files.update(str(p.relative_to(ROOT)).replace('\\', '/') for p in directory.rglob('*')
                         if p.is_file() and p.suffix in {'.lean', '.py', '.json', '.md', '.txt', '.log', '.npz', '.draft'})
        subprocess.run(['git', 'add', '--force', '--', *sorted(files)], cwd=ROOT, check=True)
        changed = subprocess.check_output(['git', 'diff', '--cached', '--name-only', '-z'], cwd=ROOT).decode().split('\0')[:-1]
        entries = []
        for path in changed:
            raw = subprocess.check_output(['git', 'show', ':'+path], cwd=ROOT)
            try:
                raw.decode('utf8')
                binary = b'\0' in raw
            except UnicodeDecodeError:
                binary = True
            entries.append({'path': path, 'sha': subprocess.check_output(['git', 'rev-parse', ':'+path], cwd=ROOT).decode().strip(),
                            'bytes': len(raw), 'binary': binary})
        staged = {'parent': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT).decode().strip(),
                  'tree': subprocess.check_output(['git', 'write-tree'], cwd=ROOT).decode().strip(), 'entries': entries}
        dest = ROOT/'tmp/followup-sync'; dest.mkdir(parents=True, exist_ok=True)
        (dest/'staged.json').write_text(json.dumps(staged, indent=2)+'\n', encoding='utf8')
        print(json.dumps({'parent': staged['parent'], 'tree': staged['tree'], 'files': len(entries),
                          'bytes': sum(r['bytes'] for r in entries)}))
    print(json.dumps({'ordinary_lean_verified': len(checked), 'required_unverified': sorted(REQUIRED-set(checked)),
                      'new_unconditional_zero_proportion_proven': False, 'upload_ready': False}))


if __name__ == '__main__':
    main()
