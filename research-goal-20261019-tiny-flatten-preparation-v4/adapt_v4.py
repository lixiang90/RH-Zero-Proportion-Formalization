"""Static flatten-tool adaptation to four deduplicated production input modules.

The upload-source generator is only written and AST-inspected, never executed.
"""
import ast
import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OLD = ROOT / 'research-goal-20261018-tiny-flatten-preparation-v3'
SOURCE_PREP = ROOT / 'research-goal-20261019-tiny-dedup-source-preparation/prepared-files.json'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    manifest = OLD / 'prepared-files.json'
    assert sha(manifest.read_bytes()) == '8d866f77503210091280574f6a14fcead5461f07c156f383f1b67f78ee52ab32'
    assert sha(SOURCE_PREP.read_bytes()) == '98a9dfe125cfdb4febc24fb8666bb73228e4f27fcbac9fe66506c1c7720f99d6'
    for r in json.loads(manifest.read_text(encoding='utf-8'))['files']:
        assert sha((ROOT / r['path']).read_bytes()) == r['sha256']
    sources = json.loads(SOURCE_PREP.read_text(encoding='utf-8'))
    source_rows = sources['files'][:4]
    for r in source_rows:
        assert sha((ROOT / r['path']).read_bytes()) == r['sha256']
    modules = [(r['path'][:-5].replace('/', '.'), r['path']) for r in source_rows]
    gen = (OLD / 'generate_draft.py').read_text(encoding='utf-8')
    begin, end = gen.index('MODULES = ('), gen.index('\nIMPORT =')
    gen = gen[:begin] + 'MODULES = (\n' + ''.join(f'    ({m!r}, {p!r}),\n' for m, p in modules) + ')\n' + gen[end:]
    prep = (OLD / 'prepare_only.py').read_text(encoding='utf-8')
    a, b = prep.index('MODULE_PINS = {'), prep.index('\nMODULE_NAMES =')
    prep = prep[:a] + 'MODULE_PINS = {\n' + ''.join(f" {r['path']!r}: {r['sha256']!r},\n" for r in source_rows) + '}\n' + prep[b:]
    replacements = {
        'assert module_bytes == 1_977_052': 'assert module_bytes == 1_854_229',
        'assert len(internal) == 5': 'assert len(internal) == 4',
        "'schema':'tiny-flatten-generator-prepared-v4'": "'schema':'tiny-flatten-generator-prepared-v5'",
        "'schema':'tiny-flatten-static-preparation-v4'": "'schema':'tiny-flatten-static-preparation-v5'",
        "'adapt_v3.py','v2-to-v3.diff'": "'adapt_v4.py','v3-to-v4.diff'",
    }
    for old, new in replacements.items():
        assert prep.count(old) == 1, old
        prep = prep.replace(old, new)
    marker = "DEPS = list(MODULE_PINS) + ["
    prep = prep.replace(marker, marker + "\n 'research-goal-20261019-tiny-dedup-source-preparation/prepared-files.json',\n 'research-goal-20261019-tiny-dedup-static-review/report-files.json',\n 'research-goal-20261018-tiny-flatten-preparation-v3/prepared-files.json',\n 'research-goal-20261018-tiny-flatten-preparation-v3/generate_draft.py',\n 'tmp/current-s1r-tiny-20261018/production-v0/failure.json',")
    outputs = {'generate_draft.py': gen, 'prepare_only.py': prep,
        'official-wrapper.lean.txt': (OLD / 'official-wrapper.lean.txt').read_text(encoding='utf-8')}
    for n in ['generate_draft.py', 'prepare_only.py']:
        ast.parse(outputs[n], filename=n)
    outputs['SPEC.zh.md'] = '''# 去重 Production 四模块单源准备

本包只冻结文本拼接工具；upload-source generator 零执行。四个输入为 Production.Core、Production.Localization、Production.Counting、Production.Final，共1,854,229 UTF-8 bytes。精确字节/SHA以 input-pins/prepared 为准。

Core 来自 canonical strengthened TinyGoal Core，精确以同7字节命名族 PC9QB6M→PC9Tiny；只删旧最终定理代码，旧尾两块版权 block 原字节保留，原 full third-party licenses 全保留，137个 packed walk payload 与所有数学数据/见证不变。三桥只有 import 路径变化，正文与原已通过版本完全相同，原官方 wrapper 字节不变。

算法仍只移出完整单模块 import 行。四个内部 import 由此前拼入的正文替代；24个可信外部 import 原字节/原顺序移到头。所有源体的非import字节逐段保持，并记录offset/hash；不重定义 currentRecordKappa/candidateKappa，不压缩/改写数据。

旧 production-v0 真实在 nanoda 阶段耗尽统一3200秒而失败；ordinary与Comparator/defaultkernel已通过，但不是完整成功。旧 source/prepared/failure/draft 均不覆盖。新文本源和本工具均未通过普通编译、导出或重放。纯静态同源审查不是完成验证。

未来唯一 generator 调用必须由新 production-v1 launcher 在单一 monotonic t0 之后执行，包含在统一3200秒预算内；不在此准备阶段运行。输出目录本包 draft/ 必须不存在，独占创建一次，无自动修源/重试；上传元数据恒 upload_ready=false，直到全套后续验证和材料收集通过。

新可信 CandidateSpec 由新冷目录中从固定官方模板、真实当前可信ledger exactExpression、候选p/q生成。候选与预期纪录见 candidate-parameters.json；若最新纪录变化，停止并重新评估。不得修改旧installed Spec。

仍须完成实际生成/保留字节审计、四模块冷ordinary、公理标准三项、全部三个官方完整陈述及依赖/primitive比较、默认kernel/nanoda、统一generation-through-receipt≤3200秒和官方验收。8GiB仅文件大小限制，不声称RAM上限。不运行网络或网站提交，official acceptance=false。
'''
    outputs['v3-to-v4.diff'] = ''.join(''.join(difflib.unified_diff(
        (OLD / n).read_text(encoding='utf-8').splitlines(keepends=True), v.splitlines(keepends=True),
        fromfile='v3/' + n, tofile='v4/' + n)) for n, v in outputs.items())
    for n in outputs:
        assert not (HERE / n).exists()
    for n, v in outputs.items():
        with (HERE / n).open('x', encoding='utf-8', newline='\n') as f:
            f.write(v)
    with (HERE / 'version-delta.json').open('x', encoding='utf-8', newline='\n') as f:
        json.dump({'schema': 'tiny-dedup-flatten-v4-adaptation',
            'prior_prepared_sha256': sha(manifest.read_bytes()),
            'production_source_prepared_sha256': sha(SOURCE_PREP.read_bytes()),
            'module_count': 4, 'internal_import_count': 4,
            'generator_algorithm_changed': False, 'wrapper_bytes_changed': False,
            'mathematical_statements_changed': False, 'old_files_modified': False,
            'generator_executions': 0, 'Lean_runs': 0}, f, indent=2); f.write('\n')
    print(json.dumps({'static_adaptation_written': True, 'full_upload_generator_executions': 0}))

if __name__ == '__main__':
    main()
