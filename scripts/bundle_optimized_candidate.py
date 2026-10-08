"""Reproduce the synchronous optimized candidate in a fresh ignored scratch tree.

Default: python scripts/bundle_optimized_candidate.py
Optional: --reflection --output-dir tmp/optimized-repro/reflected
The fixed public sources are hash-locked. The 21 AM deletions are mechanically
checked, not inferred afresh from a kernel dependency graph. This generates
source only; compilation, axiom audits, independent checking and official
resource verification remain separate. No existing output tree is overwritten.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

if not __debug__:
    raise SystemExit('Run without -O: fixed-input and transform guards must remain enabled.')
ROOT = Path(__file__).resolve().parents[1]
OUTPUT_SCOPE = ROOT / 'tmp/optimized-repro'
PINS = {'NOTICE': '5accf6621dc0bc863bd252798595cbc825829a1af4e66ddee2a027777e079097', 'scripts/bundle_solution.py': '8d21a36cd5a72a88f65c7976dc1b4a6c4393e6651dc6024fe127006f61fb5876', 'scripts/generate_two_edge_candidate.py': 'dbb3028a38da5dd7a4c817335af7719d6a240f50d5273cd989aaaca37ad1fe39', 'submission/candidate-entry.lean.in': '4afc277198a4e6482f04d805812728f66d2a9fc7ec07ff267e6daaf36d006796', 'submission/proof/Solution.lean': 'd52f013f7edcc8536a28ef3908e64a967e5b9184d6546952cb5a541dc6d65e8a', 'RecordProportion/ImportedAM.lean': '7a2fb08c598a32b05f041b51a762c3dc789ce36e0a3ff871e9f3776a69cd64f8', 'RecordProportion/Majorant.lean': '161f95eae8798b7ceb1658ccf1f04469573af0475930a24ff664a4035a3f770d', 'RecordProportion/AnalyticBridge.lean': '850a1479aa4e6851fa5c19f30d6b0de26a73b7a5e05cd282f0289f54159ffcae', 'RecordProportion/FloydSoundness.lean': '2c743f6c6b94fa31e97162cd7d6ec9afdf7f096fbdfb169876ac5c0f1c6efdbb', 'RecordProportion/FloydWeakening.lean': '146adbcf22bd73003c4913979a39d2de3df7ef181e6fa52a683919f76b46b879', 'RecordProportion/FloydTwoEdge.lean': 'e381f27356dca8ea3d876981c544f4d12298a4246eafaef94ec620b58b8701a3', 'RecordProportion/FiniteCertificateData.lean': '0b12cba764e62ac55f1d7acdebc6c86cf1a26253ccb31939519b983f01b1bc59', 'RecordProportion/RowEvaluation.lean': '4b85194185223041984ea7bd870eb742ee5a678065c09fa8a45a0a3e2ee60454', 'RecordProportion/SparseDualSoundness.lean': '05e1f9ccb64c99ac1d5fb66b67147a902569c17e6d8598dd7ee2295bf7aa23e5', 'RecordProportion/PointSoundness.lean': 'e0feca589d54ae049e8ff721dfd1bbe7ea9804f0fac0c42ba96ef0d5bd153764', 'RecordProportion/GeometryCoverage.lean': 'f3ccb337e398efddfb9b8e6a0a007235ecb4d5889fcad504b9d4ffc7b0f3f7a1', 'RecordProportion/FiniteCertificate.lean': '6c6cb5dc10588e430c28118107ad66e1da93dcd0b0e62bd579fcc92a3f078cb5', 'RecordProportion/TrustedCounts.lean': '229ac74a5241fc64aaa4bbb165620731c811fb355130fcb3c8355975044e1b7b'}
PRUNES = [('Zeta23Ext.Bridge.energyOn', 3434, 3435, '33a10dfbf7c2fa7563e1b563cb008b22307cb88cde093ee7546ab97bf1753f8f'), ('Zeta23Ext.Bridge.IsInterval', 3440, 3441, '5532cee9b14eeb1f89e81d750437b7be675c517d9da776e14da0bd68db0b197a'), ('Zeta23Ext.Bridge.gramS₁_posSemidef', 3477, 3478, 'e89612e1fc9722028566c40fdaf0dd50cc0b661a2ed65724cbf5a761a91c4f6c'), ('Zeta23Ext.Bridge.gram_posSemidef', 3506, 3507, '084ef9c7eae75fe01dfab5dafe869f221fbbd55c9039c1dfabf91755b0e59d2f'), ('Zeta23Ext.Bridge.xret_injective', 3515, 3526, '9af6b80c4b7543c964dd7529710c000e0cfe6343c5e61ac09c8ca2c47698719f'), ('Zeta23Ext.Bridge.wfun_sub_comm', 3540, 3541, 'e9dfe2fd95f89279efb12aa26f945801736015fe4102c6a9466784088a073cdd'), ('Zeta23Ext.Bridge.wfun_nonneg', 3542, 3542, 'e6022e6c970024598ea7bb620b34151ad552be74659674c9c657c4f6fc0bcd92'), ('Zeta23Ext.Bridge.sortedExt_mono', 3556, 3559, '257c589bce104102d452a5110e02006c96b118b429f1e9ae282ca932bfd305c9'), ('Zeta23Ext.Bridge.sum_shift_sub', 3575, 3589, '8c2e0d7c1a9d0763d3ce21af247317e0a039cdd5708bee9ad41f3642fe5efc43'), ('Zeta23Ext.Bridge.kernel_limit', 4712, 4744, '9d879edba472ef5b5d12d1193a2e8418bcfdc871d83309ff4374e8353f6861cb'), ('Zeta23Ext.Bridge.energyOn_eq_sorted', 4838, 4866, '18a03998f0df22d71de334531f6ddf38f6768cb539cc63ef44511dd6e9695ba3'), ('Zeta23Ext.Bridge.block_defect', 4912, 4914, '7e4c9013da9054c382b9bf6f6a986f7bf60c3885d0160cb02776ce659a04e6c6'), ('Zeta23Ext.Bridge.energyOn_subtype', 4948, 4955, '535eeba68ac9ac95b3ddde086445866a2c81b8f542030259f6df57d937f2ae11'), ('Zeta23Ext.Bridge.eq_of_mod_eq_of_overlap', 4984, 4994, 'fd15a82e62c8682245f474ab8aa4baa026d1f6437dd9acfea8b24cd4c5926920'), ('Zeta23Ext.Bridge.blockStart', 4995, 4997, '9c21032f1bc7e7d367289daa37ed4750a240080720ac339ef4429ab907ec6121'), ('Zeta23Ext.Bridge.blockStart_le', 4998, 5002, '605c070317ecc714082b80503320b5108fc09f190db203dee6077ab010b01487'), ('Zeta23Ext.Bridge.blockStart_eq_iff', 5003, 5016, '636fa94590bd819f06ca25763a40622cc215f7c3598ececd6551e23d7530d12a'), ('Zeta23Ext.Bridge.one_sub_div_pos', 5098, 5104, '310d5a3191a963c6ecf347c6cf34f03c1094a18a7eb54a00c99ddde46658c7d6'), ('Zeta23Ext.Bridge.eventually_L_pos', 5116, 5117, '6d67f5057334ebb29c48e209cd3204981fdfb64e7fdbcb189c0f0d34458deb3e'), ('AMW.Cert.SC_posR', 7448, 7448, '835a9b2a942bebc288ccbbbe47d8f6f3cfa95d5c4969aa16f0f01c66f232def5'), ('AMW.Cert.PyrD.tK', 8435, 8435, '07de7c2116a3839b9560ffba651a99b304bcb97d8231a34cfb9698bb87de7794')]
REFLECTION_PINS = {
    'scripts/generate_reflected_point_candidate.py': 'ba968c3b5cb18f17ca87ea5cd83ab51898148838fbbb13c46f3254776aaa6227',
    'RecordProportion/FrameReflection.lean': '1ec117c627997eab4801023ccffb9e9a10e6ac006ed6470a8437a5dbd9d22be7',
}
AM_PRUNED_SHA = '3bd7fc52f1beb41d2dab81da2da62acbffc24c74308f8f7d63c5d62e467ed283'
DATA_OVERLAY_SHA = '4fae6f34eb5cc44efe31613f557bf8b37f20338fe044e8492457188fe8551aa7'
REFLECTED_POINT_SHA = 'f7d766f8e4b389a5bbb410df05bd718f4149fd3e5f8941bcf52ef0e0eb33b7ad'
REFERENCE_SHA = '583c5becafd39bc083240afa64d4468be15df67a86d819ac4544b18e2bfd98c7'
REFERENCE_BYTES = 1994836


def sha(blob: bytes) -> str:
    return hashlib.sha256(blob).hexdigest()


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def fixed_inputs(reflection: bool) -> dict[str, bytes]:
    pins = PINS | (REFLECTION_PINS if reflection else {})
    blobs = {name: (ROOT/name).read_bytes() for name in pins}
    for name, expected in pins.items():
        require(sha(blobs[name]) == expected, 'Fixed public input changed: '+name)
        require(b'\r' not in blobs[name], 'Expected canonical UTF-8 LF: '+name)
        blobs[name].decode('utf-8')
    return blobs


def command_scopes(masked: str) -> list[str]:
    return [line for line in masked.splitlines()
            if re.match(r'^(?:namespace|(?:noncomputable )?section|end|variable)\b', line)]


def namespace_before(masked: str, stop_line: int) -> str:
    scopes: list[tuple[str, str | None]] = []
    for line in masked.splitlines()[:stop_line]:
        m = re.fullmatch(r'(namespace|(?:noncomputable )?section|end)(?:\s+([\w.]+))?\s*', line)
        if not m:
            continue
        kind, name = m.groups()
        segments = name.split('.') if name else [None]
        if kind == 'end':
            require(len(scopes) >= len(segments), 'Unexpected scope closure')
            require([x[1] for x in scopes[-len(segments):]] == segments, 'Scope mismatch')
            del scopes[-len(segments):]
        else:
            scopes.extend(('namespace' if kind == 'namespace' else 'section', x) for x in segments)
    return '.'.join(name for kind, name in scopes if kind == 'namespace' and name is not None)


def prune_am(blob: bytes, bundler) -> bytes:
    require(sha(blob) == PINS['RecordProportion/ImportedAM.lean'], 'Wrong AM input')
    text = blob.decode('utf-8')
    lines = text.splitlines(keepends=True)
    mask = bundler.code_mask(text)
    removed: set[int] = set()
    require(len(PRUNES) == 21 and len({x[0] for x in PRUNES}) == 21, 'Wrong prune list')
    for name, first, last, expected in PRUNES:
        indices = set(range(first-1, last))
        require(not removed.intersection(indices), 'Overlapping deletion ranges')
        part = ''.join(lines[first-1:last])
        require(sha(part.encode()) == expected, 'Deletion body changed: '+name)
        declarations = re.findall(r'^(?:noncomputable )?(?:def|theorem|lemma|abbrev)\s+([^\s(:]+)', bundler.code_mask(part), re.M)
        require(declarations == [name.rsplit('.', 1)[1]], 'Wrong declaration head: '+name)
        require(namespace_before(mask, first-1)+'.'+declarations[0] == name, 'Wrong declaration namespace: '+name)
        require(not command_scopes(bundler.code_mask(part)), 'Deletion would remove a global scope: '+name)
        removed.update(indices)
    result = ''.join(line for i, line in enumerate(lines) if i not in removed)
    require(sha(result.encode()) == AM_PRUNED_SHA, 'Wrong pruned AM result')
    require(len(blob)-len(result.encode()) == 7647, 'Wrong deletion byte total')
    require(command_scopes(mask) == command_scopes(bundler.code_mask(result)), 'Scope/variable commands changed')
    require(bundler.remaining_sections(text) == bundler.remaining_sections(result), 'Section structure changed')
    require(result.count('atW_tau_eq') == text.count('atW_tau_eq') and result.count('atW_tau_eq') >= 2, 'Required atW_tau_eq lost')
    require(text.count('set_option Elab.async false') == 1 and result.count('set_option Elab.async false') == 1, 'Synchronous AM option changed')
    return result.encode()


def run_source_command(arguments: list[str]) -> None:
    result = subprocess.run([sys.executable, '-B', '-X', 'utf8', *arguments], cwd=ROOT,
                            capture_output=True, text=True, encoding='utf-8')
    require(result.returncode == 0, 'Source generator failed: '+result.stdout+result.stderr)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=Path('tmp/optimized-repro'),
                        help='Fresh directory within tmp/optimized-repro; existing nonempty trees are rejected')
    parser.add_argument('--reflection', action='store_true', help='Generate the fixed reflected Point variant; no whole-check claim')
    args = parser.parse_args()
    require(OUTPUT_SCOPE.resolve() == OUTPUT_SCOPE, 'Owned output scope is a symlink/reparse path')
    destination = (ROOT/args.output_dir).resolve()
    require(destination.is_relative_to(OUTPUT_SCOPE), 'Output must stay in owned tmp/optimized-repro, never an active overlay')
    require(not destination.exists() or (destination.is_dir() and not any(destination.iterdir())), 'Refusing to overwrite an existing/nonempty output tree')
    before = fixed_inputs(args.reflection)
    spec = importlib.util.spec_from_file_location('fixed_public_bundler', ROOT/'scripts/bundle_solution.py')
    require(spec is not None and spec.loader is not None, 'Cannot load public bundler')
    bundler = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(bundler)
    pruned = prune_am(before['RecordProportion/ImportedAM.lean'], bundler)
    for name, content in before.items():
        if name.startswith('RecordProportion/') or name in ['NOTICE', 'scripts/bundle_solution.py', 'submission/candidate-entry.lean.in']:
            if name == 'RecordProportion/FrameReflection.lean':
                continue  # The reflected Point generator inlines the proven helper body.
            out = destination/name
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_bytes(content)
    (destination/'RecordProportion/ImportedAM.lean').write_bytes(pruned)
    generated = destination/'generated/TwoEdgeCandidate.lean'
    run_source_command(['scripts/generate_two_edge_candidate.py', '--output', relative(generated)])
    data = generated.read_text(encoding='utf-8')
    pattern = r'\nrun_cmd Lean.Elab.Command.liftIO <\| do\n  let now ← IO.monoMsNow\n  IO.eprintln s!"COST PROOFS_(?:BEGIN|END) \{now\}"\n'
    data, count = re.subn(pattern, '\n', data)
    require(count == 2, 'Expected exactly two timing-only commands')
    require(sha(data.encode()) == DATA_OVERLAY_SHA, 'Derived Data differs from fixed overlay')
    (destination/'RecordProportion/FiniteCertificateData.lean').write_text(data, encoding='utf-8', newline='\n')
    if args.reflection:
        point = destination/'RecordProportion/PointSoundness.lean'
        run_source_command(['scripts/generate_reflected_point_candidate.py', '--write', '--output', relative(point)])
        require(sha(point.read_bytes()) == REFLECTED_POINT_SHA, 'Reflected Point differs from fixed candidate')
    command = [sys.executable, '-B', '-X', 'utf8', str(destination/'scripts/bundle_solution.py'),
               '--entry', 'submission/candidate-entry.lean.in', '--compact-layout', '--compact-nat-calls',
               '--compact-numeral-dictionary', '--output', 'Solution.optimized.draft.lean']
    completed = subprocess.run(command, cwd=destination, capture_output=True, text=True, encoding='utf-8')
    require(completed.returncode == 0, 'Bundler failed: '+completed.stdout+completed.stderr)
    output = destination/'Solution.optimized.draft.lean'
    result = output.read_bytes()
    if not args.reflection:
        require(sha(result) == REFERENCE_SHA and len(result) == REFERENCE_BYTES, 'Default source fails byte-for-byte reference reproduction')
    after = fixed_inputs(args.reflection)
    require(after == before, 'Fixed public inputs changed during generation')
    manifest_path = output.with_suffix('.manifest.json')
    record = json.loads(manifest_path.read_text(encoding='utf-8'))
    for item in record['sources']:
        item['path'] = relative(destination/item['path'])
    record['output'] = relative(output)
    record['producer'] = {'path': 'scripts/bundle_optimized_candidate.py', 'sha256': sha(Path(__file__).read_bytes())}
    record['fixed_public_inputs'] = {name: sha(content) for name, content in before.items()}
    record['overlay_only'] = True
    record['formal_sources_and_public_checked_solution_unchanged'] = True
    record['source_transforms'] = {
        'Data': {'producer': 'scripts/generate_two_edge_candidate.py', 'original_sha256': PINS['RecordProportion/FiniteCertificateData.lean'], 'remove_timing_commands': 2, 'derived_sha256': DATA_OVERLAY_SHA, 'proof_routes_only': True},
        'ImportedAM': {'original_sha256': PINS['RecordProportion/ImportedAM.lean'], 'removed_declarations': [x[0] for x in PRUNES], 'removed_source_bytes': 7647, 'derived_sha256': AM_PRUNED_SHA, 'scope_and_atW_tau_eq_preserved': True, 'fresh_full_elaboration_required': True},
        'AM_scheduling': 'Original synchronous source; no async override',
        'Point': {'reflection': args.reflection, 'producer': 'scripts/generate_reflected_point_candidate.py' if args.reflection else None, 'derived_sha256': sha((destination/'RecordProportion/PointSoundness.lean').read_bytes())},
    }
    record['reference'] = {'sha256': REFERENCE_SHA, 'bytes': REFERENCE_BYTES, 'exact_source_reproduction': not args.reflection}
    record['validation_scope'] = 'Deterministic guarded source generation only. No Lean compilation, axiom audit, Nano, whole-submission, Linux resource, Comparator or website pass in this invocation.'
    record['submitted'] = False
    manifest_path.write_text(json.dumps(record, indent=2, ensure_ascii=False)+'\n', encoding='utf-8', newline='\n')
    require(record['within_source_limit'] == (len(result) <= 2000000), 'Inconsistent size metadata')
    print(json.dumps({'output': relative(output), 'manifest': relative(manifest_path), 'bytes': len(result), 'sha256': sha(result), 'within_source_limit': len(result) <= 2000000, 'reflection': args.reflection, 'reference_source_equal': not args.reflection, 'fixed_inputs_unchanged': before == after, 'compiled': False, 'submitted': False}, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError) as error:
        raise SystemExit(str(error))
