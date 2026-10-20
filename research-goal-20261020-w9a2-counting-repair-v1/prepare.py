"""Exclusive textual name-qualification repair. No proof/runtime execution."""
from pathlib import Path
import difflib
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OLD_SHA = '163fbaae81c9afd492cdfd5c66dd2848f1d1e03ac0af6ae3774a7cc619c631d5'
FLAT_SHA = '650ad1762ee36ba1ddf5f6a027900b20f0f85ba087ac099fd2c99a54eaf6ae13'
LOG_SHA = 'e02e5ca0b3fa36045f28831eb7553cdd61e829345af9100d330771880f4f2224'
ARCHIVE_SHA = 'f3a6ef61522efc700e43b43e7cd0ad580701ae522f8adf3724157300f3ec874a'
inputs = {}


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path, expected=None):
    raw = path.read_bytes()
    value = dict(path=path.relative_to(ROOT).as_posix(), bytes=len(raw), sha256=digest(raw))
    assert expected is None or value['sha256'] == expected, path
    assert str(path) not in inputs or inputs[str(path)] == value
    inputs[str(path)] = value
    return raw


def write(relative, raw):
    path = HERE / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as f:
        f.write(raw)


def jsonwrite(relative, value):
    write(relative, (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode())


def main():
    assert set(p.name for p in HERE.iterdir()) == {'prepare.py'}
    canonical = ROOT / 'StructuralW9A220261020/Counting.lean'
    old = read(canonical, OLD_SHA)
    frozen = ROOT / 'research-goal-20261020-w9a2-delivery/draft-v5/frozen-inputs/StructuralW9A220261020'
    assert read(frozen / 'Counting.lean', OLD_SHA) == old
    pattern = rb'(?<![A-Za-z_0-9.])wfun\b'
    matches = list(re.finditer(pattern, old))
    assert [old[:m.start()].count(b'\n') + 1 for m in matches] == [158, 178, 205]
    new = re.sub(pattern, b'Zeta23Ext.Bridge.wfun', old)
    assert len(matches) == 3 and len(new) == len(old) + 51
    assert new.replace(b'Zeta23Ext.Bridge.wfun', b'wfun') == old
    assert not re.search(pattern, new)
    assert len(old.splitlines()) == len(new.splitlines())
    literals = rb'(?<![A-Za-z_0-9])\d+(?![A-Za-z_0-9])'
    assert re.findall(literals, new) == re.findall(literals, old)
    write('original/Counting.lean', old)
    write('StructuralW9A220261020/Counting.lean', new)
    write('README.zh.md', '''本包只对 Counting 的三个未限定名称作显式限定：158、178、205 行的 wfun 改为 Zeta23Ext.Bridge.wfun，共增加51字节，行数不变。对应旧flat-v5的16765、16785、16812行。两个位于原定理陈述，一个位于原有change证明命令；它们都显式指向原独立模块编译时已经使用的同一个Bridge.wfun，定理的数学命题与证明步骤不变。

Core内 Fw_windowGaps、window_pairs_le_band、OpethN.band_close_n 的相关能量和均用 Zeta23Ext.Bridge.wfun。Counting模块自身显式open该Bridge；模块化导入不会继承Graph的open命令。Graph的anonymous noncomputable section却只有namespace结束、没有显式section结束，文本flatten后其open AMW.Cert延续至后面的Counting；Localization仅关闭自己的内层section，不能清除Graph外层open。因此单文件中出现Bridge.wfun与AMW.Cert.wfun两个候选。Core另有RiemannFail.cert_wfun_eq的rfl等式，但此修复不添加或调用新等式，也不改函数定义。

正式生产原父session68653/PID48644实际exit1，非timeout；Candidate子PID6020实际exit1/1091.172秒。唯一三项名称歧义后，16842行linarith收到的he求和已含failed-elaboration sorry占位，而hb是Bridge.wfun求和，故属于同源下游失败。此处不改linarith或任何付款/望远镜证明。所有failed sorryAx输出都被拒绝，没有当成证明。

原Counting、flat-v5/650、其他四模块、旧数值证书与完整真实失败archive全部保全。本包给出唯一前向替换及逐字逆投影；所有数字literal与三项名称之外的字节不变。repair.json中的新flat SHA仅为内存投影，没有在此写新flat源码；新flat由delivery独立生成复核。

这是源码与证据准备，不是编译成功声明。本包没有运行Lean、exporter、kernel或数值walk。新Counting模块普通编译、新flat生产单文件及独立双核仍待root后续明确gate；官网未提交、未接受。全部manifest路径相对本包根。
'''.encode())
    patch = ''.join(difflib.unified_diff(old.decode().splitlines(keepends=True),
        new.decode().splitlines(keepends=True), fromfile='v0/Counting.lean',
        tofile='repair-v1/Counting.lean'))
    write('exact-source-diff.patch', patch.encode())

    archive = ROOT / 'research-goal-20261020-w9a2-fullchain-v1-terminal'
    archive_manifest = read(archive / 'files.json', ARCHIVE_SHA)
    archive_data = json.loads(archive_manifest)
    write('failed-production-v1/files.json', archive_manifest)
    for row in archive_data['files']:
        value = read(archive / row['path'], row['sha256'])
        assert len(value) == row['bytes']
        write('failed-production-v1/' + row['path'], value)
    flat = read(archive / 'job/source/Solution/Candidate.lean', FLAT_SHA)
    assert len(flat) == 1830001
    assert read(ROOT / 'tmp/w9a2-20261020/fullchain-v1/source/Solution/Candidate.lean', FLAT_SHA) == flat
    assert read(ROOT / 'research-goal-20261020-w9a2-delivery/draft-v5/Solution.lean', FLAT_SHA) == flat
    log = read(archive / 'job/logs/ordinary-Solution.Candidate.log', LOG_SHA)
    assert read(ROOT / 'tmp/w9a2-20261020/fullchain-v1/logs/ordinary-Solution.Candidate.log', LOG_SHA) == log
    errors = re.findall(rb'Candidate\.lean:(\d+):(\d+): error:', log)
    assert errors == [(b'16765', b'10'), (b'16785', b'18'), (b'16812', b'10'), (b'16842', b'4')]
    stage = json.loads(read(archive / 'job/logs/ordinary-Solution.Candidate.terminal.json'))
    parent = json.loads(read(archive / 'root-parent-exit-attestation.json'))
    failure = json.loads(read(archive / 'job/failure.json'))
    assert stage['exit_code'] == 1 and stage['elapsed_seconds'] == 1091.1720000000005
    assert parent['exec_session_id'] == 68653 and parent['parent_pid'] == 48644
    assert parent['actual_exit_code'] == 1 and parent['timeout'] is False
    assert failure['failed'] is True and failure['local_fullchain_verified'] is False

    old_body = b''.join(line for line in old.splitlines(keepends=True) if not line.startswith(b'import '))
    new_body = b''.join(line for line in new.splitlines(keepends=True) if not line.startswith(b'import '))
    assert flat.count(old_body) == 1
    start = flat.index(old_body)
    projected = flat[:start] + new_body + flat[start + len(old_body):]
    assert projected[:start] == flat[:start]
    assert projected[start + len(new_body):] == flat[start + len(old_body):]
    assert projected.replace(new_body, old_body, 1) == flat
    assert len(projected) == 1830052
    assert [flat[:start + m.start()].count(b'\n') + 1 for m in re.finditer(pattern, old_body)] == [16765, 16785, 16812]

    core = read(frozen / 'Core.lean')
    graph = read(frozen / 'Graph.lean')
    loc = read(frozen / 'Localization.lean')
    final = read(frozen / 'Final.lean')
    assert b'open AMW.Cert AMW.Cert.Pyr AMW.Cert.PCell AMW.Cert.PC9QB6M' in graph
    assert graph.rstrip().endswith(b'end StructuralW9A220261020.Graph')
    assert graph.count(b'noncomputable section') == 1
    excerpts = []
    for title, raw, ranges in [('Core', core, [(3465,3475),(5050,5080),(5150,5168),(7596,7608),(13170,13178),(13428,13432),(15316,15334)]),
                               ('Graph', graph, [(10,19),(218,222)]),
                               ('Localization', loc, [(10,21),(286,291)]),
                               ('Counting-before', old, [(18,26),(144,182),(193,210),(230,241)])]:
        lines = raw.decode().splitlines()
        for lo, hi in ranges:
            excerpts.append(f'--- {title}:{lo}-{hi} ---\n' + '\n'.join(f'{i}: {lines[i-1]}' for i in range(lo,min(hi,len(lines))+1)))
    write('name-resolution-source-excerpts.txt', ('\n\n'.join(excerpts)+'\n').encode())
    jsonwrite('repair.json', dict(scope='Same-symbol name-resolution repair only; no mathematical premise, theorem, data, tactic or threshold change',
        compiler_runs=0, exporter_runs=0, kernel_runs=0, numerical_walk_runs=0,
        old_counting=dict(bytes=len(old),sha256=digest(old)),
        new_counting=dict(bytes=len(new),sha256=digest(new)),
        replacement=dict(from_token='wfun',to_token='Zeta23Ext.Bridge.wfun',occurrences=3,module_lines=[158,178,205],flat_v5_lines=[16765,16785,16812],bytes_added=51),
        old_flat=dict(bytes=len(flat),sha256=digest(flat)),
        in_memory_projected_flat=dict(bytes=len(projected),sha256=digest(projected),source_file_written=False),
        checks=dict(exact_forward_projection=True,exact_reverse_projection=True,line_count_unchanged=True,integer_literals_unchanged=True,
            all_bytes_outside_three_qualifications_unchanged=True,flat_prefix_suffix_unchanged=True),
        affected_declarations=['block_energy_band_of_sum statement','block_energy_band_of_sum proof change command','block_energy_band_separated statement'],
        intended_symbol='Zeta23Ext.Bridge.wfun, as already fixed in Fw_windowGaps/window_pairs_le_band/OpethN.band_close_n',
        scope_cause='Graph anonymous noncomputable section has no explicit closing end at EOF; its open AMW.Cert remains active under textual concatenation, whereas importing Graph does not export open commands. Localization closes only its own nested section.',
        downstream_linarith='line16842 receives a he expression containing failed-elaboration sorry placeholder at energy sum, while hb contains Bridge.wfun; no tactic changed',
        actual_failure=dict(parent_session=68653,parent_pid=48644,parent_exit_code=1,timeout=False,candidate_pid=stage['pid'],candidate_exit_code=1,candidate_elapsed_seconds=stage['elapsed_seconds'],log_sha256=LOG_SHA,
            all_four_error_locations=[dict(line=int(a),column=int(b)) for a,b in errors],failed_sorryAx_output_accepted_as_proof=False),
        new_source_ordinary_passed=False,new_source_single_file_passed=False,new_source_independent_kernels_passed=False,official_website_acceptance=False,submitted=False))
    for row in inputs.values():
        value = (ROOT / row['path']).read_bytes()
        assert len(value) == row['bytes'] and digest(value) == row['sha256']
    jsonwrite('input-read-check.json',dict(all_before_after_input_hashes_equal=True,files=list(inputs.values()),
        original_canonical_source_modified=False,original_draft_v5_modified=False,frozen_failure_archive_modified=False))
    rows=[]
    for p in sorted(HERE.rglob('*')):
        if p.is_file():
            raw=p.read_bytes();rows.append(dict(path=p.relative_to(HERE).as_posix(),bytes=len(raw),sha256=digest(raw)))
    jsonwrite('files.json',dict(scope='Exact three-name same-symbol Counting repair; source/evidence preparation only; zero proof execution',files=rows))
    print(json.dumps(dict(manifest_sha256=digest((HERE/'files.json').read_bytes()),new_counting_sha256=digest(new),new_counting_bytes=len(new),projected_flat_sha256=digest(projected),projected_flat_bytes=len(projected),files=len(rows))))


if __name__ == '__main__':
    main()
