"""Fresh ordinary Lean build and axiom audit of the additive headline roots.

Uses the pinned compiler directly with Lake's cached import-artifact mapping;
it does not download dependencies or modify historical modules/receipts.
For a fresh checkout, first build the dependencies with Lake.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
ROOTS = [
    'RHWeilRecord.JointFramePair.local_certificate',
    'RHWeilRecord.JointFramePair.simple_dyadic',
    'RHWeilRecord.JointFramePair.simple_cumulative',
    'RHWeilRecord.JointFramePair.distinct_dyadic',
    'RHWeilRecord.JointFramePair.distinct_cumulative',
    'RHWeilRecord.JointFramePair.previous_recordRatio_lt',
    'RHWeilRecord.JointFramePair.ninth_span_recordRatio_lt',
    'RHWeilRecord.JointFramePair.recordRatio_gt_67355',
]

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def sources(module: str) -> dict[str, str]:
    result = {}
    def visit(name: str) -> None:
        path = ROOT.joinpath(*name.split('.')).with_suffix('.lean')
        if name in result or not path.is_file():
            return
        result[name] = sha(path)
        for line in path.read_text(encoding='utf8').splitlines():
            if line.startswith('import '):
                for target in line[7:].split():
                    if target.startswith('RecordProportion'):
                        visit(target)
    visit(module)
    return result

def main() -> None:
    if not __debug__:
        raise SystemExit('Assertions must remain enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rebuild-dependencies', action='store_true',
                        help='Also freshly compile all additive modules, in dependency order')
    parser.add_argument('--linux-native-cache', action='store_true',
                        help='Use the fixed, previously verified WSL native dependency cache')
    args = parser.parse_args()
    if os.name == 'nt':
        compiler = Path.home()/'.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean.exe'
    else:
        compiler = Path(shutil.which('lean') or '')
    assert compiler.is_file(), 'Pinned compiler not installed'
    compiler_command = [str(compiler)]
    compiler_hash = sha(compiler)
    if args.linux_native_cache:
        info_path = ROOT/'verification/linux-memory-time-20261010/am/environment/handoff-v3.json'
        info = json.loads(info_path.read_text())
        linux_root = '/mnt/' + ROOT.drive[0].lower() + str(ROOT)[2:].replace('\\', '/')
        linux_compiler = '/tmp/rh-proportion-memory-20261010/lean-4.33.0-rc2-linux/bin/lean'
        assert info['lean'] == linux_compiler
        compiler_command = ['wsl', '--distribution', 'Ubuntu', '--exec', 'env',
            'LEAN_PATH='+linux_root+'/.lake/build/lib/lean:'+info['lean_path'], linux_compiler]
        compiler_hash = subprocess.check_output(['wsl', '--distribution', 'Ubuntu', '--exec',
            'sha256sum', linux_compiler], cwd=ROOT).decode().split()[0]
        assert compiler_hash == info['lean_sha256']
        # Bind all preexisting local modules, rather than trusting a stale cache label.
        probe = ('import json,hashlib; from pathlib import Path; '
                 'p=Path("/tmp/rh-proportion-memory-20261010/native-cache/.lake/build/lib/lean/RecordProportion"); '
                 'print(json.dumps({f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in p.glob("*.olean")}))')
        native_hashes = json.loads(subprocess.check_output(['wsl', '--distribution', 'Ubuntu',
            '--exec', 'python3', '-c', probe], cwd=ROOT))
        for path in (ROOT/'.lake/build/lib/lean/RecordProportion').glob('*.olean'):
            if not path.stem.startswith(('JointFramePair', 'NinthSpan')):
                assert sha(path) == native_hashes[path.name], f'Stale native cache: {path.name}'
    def compiler_path(path: Path) -> str:
        if args.linux_native_cache:
            return '/mnt/'+path.drive[0].lower()+str(path)[2:].replace('\\', '/')
        return str(path)
    version = subprocess.check_output(compiler_command+['--version'], cwd=ROOT).decode().strip()
    assert 'version 4.33.0-rc2' in version
    manifest = json.loads((ROOT/'lake-manifest.json').read_text())
    deps = {p['name']: p['rev'] for p in manifest['packages']}
    assert deps['mathlib'] == '51e6992efd06126df61a496bebf8f49482a4e129'
    assert deps['Zeta23'] == '3635e74826a4c1fcece7d1cd2b6fa75e43a00510'
    lib = ROOT/'.lake/build/lib/lean'
    environment = dict(os.environ)
    paths = [lib] + [ROOT/'.lake/packages'/p['name']/'.lake/build/lib/lean' for p in manifest['packages']]
    environment['LEAN_PATH'] = os.pathsep.join(map(str, paths))
    # All existing Lake maps have the same pinned dependency identities.
    arts = {}
    for name in ('AnalyticBridge', 'FiniteCertificate', 'PointSoundness'):
        path = ROOT/'.lake/build/ir/RecordProportion'/f'{name}.setup.json'
        if path.is_file():
            for key, value in json.loads(path.read_text())['importArts'].items():
                if key in arts:
                    assert arts[key] == value, f'Conflicting cached mapping: {key}'
                arts[key] = value
    assert arts, 'Build historical dependencies with Lake to create the artifact map'
    for path in (lib/'RecordProportion').glob('*.olean'):
        arts['RecordProportion.'+path.stem] = [[str(path)]]
    scratch = ROOT/'tmp/verification/joint-frame-pair-complete-formal-kernel'
    scratch.mkdir(parents=True, exist_ok=True)
    before = sources('RecordProportion.JointFramePair')
    assert 'RecordProportion.JointFramePair' in before
    new_modules = {m for m in before if m.startswith('RecordProportion.JointFramePair')}
    modules = []
    seen = set()
    def ordered(name):
        if name in seen or name not in new_modules:
            return
        seen.add(name)
        for line in ROOT.joinpath(*name.split('.')).with_suffix('.lean').read_text(encoding='utf8').splitlines():
            if line.startswith('import '):
                for target in line[7:].split():
                    ordered(target)
        modules.append(name)
    ordered('RecordProportion.JointFramePair')
    assert set(modules) == new_modules
    if not args.rebuild_dependencies:
        modules = ['RecordProportion.JointFramePair']
    reused_before = {m: sha(lib.joinpath(*m.split('.')).with_suffix('.olean'))
                     for m in before if m not in modules}
    component_receipts = {}
    if not args.rebuild_dependencies:
        component_modules = set()
        for name in ('joint-frame-pair-data-components.json', 'joint-frame-pair-real-components.json'):
            receipt_path = ROOT/'verification'/name
            receipt = json.loads(receipt_path.read_text(encoding='utf8'))
            assert receipt['passed'] is True and receipt['ordinary_lean'] is True
            component_receipts[str(receipt_path.relative_to(ROOT))] = sha(receipt_path)
            for entry in receipt['modules']:
                module = entry['module']
                assert module in new_modules - set(modules) and module not in component_modules
                component_modules.add(module)
                source_path = ROOT/entry['source']['path']
                artifact_path = ROOT/entry['olean']['path']
                log_path = ROOT/entry['log']['path']
                for path in (source_path, artifact_path, log_path):
                    assert path.resolve().is_relative_to(ROOT.resolve()) and path.is_file()
                assert entry['exit_code'] == 0 and entry['command']
                assert entry['source_sha256_before'] == entry['source_sha256_after'] == before[module]
                assert sha(source_path) == entry['source']['sha256'] == before[module]
                assert sha(artifact_path) == entry['olean']['sha256'] == reused_before[module]
                assert sha(log_path) == entry['log']['sha256']
            for name, expected in receipt['artifacts'].items():
                assert sha(ROOT/name) == expected
        assert component_modules == new_modules - set(modules), 'Missing fresh source-artifact component binding'
    steps = []
    start = time.monotonic()
    for module in modules:
        setup = {'plugins': [], 'package': 'rhZeroProportion',
                 'options': {'relaxedAutoImplicit': False}, 'name': module,
                 'isModule': False, 'importArts': arts}
        setup_path = scratch/(module.rsplit('.', 1)[1]+'.setup.json')
        setup_path.write_text(json.dumps(setup), encoding='utf8', newline='\n')
        source = ROOT.joinpath(*module.split('.')).with_suffix('.lean')
        olean = lib.joinpath(*module.split('.')).with_suffix('.olean')
        command = compiler_command+['-j1', '--tstack=32768', '-DrelaxedAutoImplicit=false', '-R', compiler_path(ROOT)]
        if not args.linux_native_cache:
            command += ['--setup', str(setup_path)]
        command += ['-o', compiler_path(olean), '-i', compiler_path(olean.with_suffix('.ilean')),
                    compiler_path(source)]
        print('Checking', module, flush=True)
        tick = time.monotonic()
        proc = subprocess.run(command, cwd=ROOT, env=environment, capture_output=True,
                              text=True, encoding='utf8', errors='replace')
        log = ROOT/'verification/joint-frame-pair-complete-formal-kernel'/(module.rsplit('.', 1)[1]+'.txt')
        log.parent.mkdir(parents=True, exist_ok=True)
        log.write_text(proc.stdout+proc.stderr, encoding='utf8', newline='\n')
        steps.append({'module': module, 'command': command,
                      'exit_code': proc.returncode,
                      'elapsed_seconds': time.monotonic()-tick,
                      'setup_sha256': sha(setup_path),
                      'source_sha256': sha(source),
                      'output_olean_sha256': sha(olean) if proc.returncode == 0 else None,
                      'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log)})
        if proc.returncode:
            print(proc.stdout+proc.stderr)
            break
        arts[module] = [[str(olean)]]
    build_ok = len(steps) == len(modules) and all(s['exit_code'] == 0 for s in steps)
    audit = None
    observed = {}
    if build_ok:
        audit_source = scratch/'Axioms.lean'
        audit_source.write_text('import RecordProportion.JointFramePair\n'+
            ''.join('#print axioms '+name+'\n' for name in ROOTS), encoding='utf8', newline='\n')
        setup['name'] = 'JointFramePairAxiomAudit'
        setup['importArts'] = arts
        setup_path = scratch/'axiom-audit.setup.json'
        setup_path.write_text(json.dumps(setup), encoding='utf8', newline='\n')
        command = compiler_command+['-j1', '--tstack=32768', '-DrelaxedAutoImplicit=false', '-R', compiler_path(ROOT)]
        if not args.linux_native_cache:
            command += ['--setup', str(setup_path)]
        command += [compiler_path(audit_source)]
        print('Auditing', len(ROOTS), 'headline roots', flush=True)
        audit = subprocess.run(command, cwd=ROOT, env=environment, capture_output=True,
                               text=True, encoding='utf8', errors='replace')
        log = ROOT/'verification/joint-frame-pair-complete-formal-kernel/axiom-audit.txt'
        log.write_text(audit.stdout+audit.stderr, encoding='utf8', newline='\n')
        print(audit.stdout+audit.stderr, flush=True)
        for name in ROOTS:
            m = re.search(r"'"+re.escape(name)+r"' depends on axioms:\s*\[([^]]*)\]", audit.stdout)
            if m:
                observed[name] = [v.strip() for v in m[1].split(',') if v.strip()]
            elif re.search(r"'"+re.escape(name)+r"' does not depend on any axioms", audit.stdout):
                observed[name] = []
    unchanged = before == sources('RecordProportion.JointFramePair')
    reused_after = {m: sha(lib.joinpath(*m.split('.')).with_suffix('.olean')) for m in reused_before}
    reused_unchanged = reused_before == reused_after
    passed = (build_ok and audit is not None and audit.returncode == 0 and unchanged and reused_unchanged
              and set(observed) == set(ROOTS)
              and all(set(a) <= ALLOWED for a in observed.values()))
    record = {'driver_sha256': sha(Path(__file__)), 'compiler': version, 'compiler_sha256': compiler_hash,
              'linux_native_cache': args.linux_native_cache,
              'modules': modules, 'source_sha256': before,
              'source_unchanged_during_check': unchanged,
              'reused_olean_before': reused_before, 'reused_olean_after': reused_after,
              'reused_olean_unchanged': reused_unchanged,
              'component_receipts': component_receipts,
              'audit_log': str(log.relative_to(ROOT)) if audit is not None else None,
              'audit_log_sha256': sha(log) if audit is not None else None,
              'olean_sha256': {m: sha(lib.joinpath(*m.split('.')).with_suffix('.olean'))
                               for m in before if lib.joinpath(*m.split('.')).with_suffix('.olean').is_file()},
              'build_steps': steps, 'module_check_passed': passed,
              'audit_exit_code': audit.returncode if audit is not None else None,
              'observed_axioms': observed, 'allowed_axioms': sorted(ALLOWED),
              'elapsed_seconds': time.monotonic()-start,
              'scope': 'Complete unconditional actual simple/distinct dyadic/cumulative bound; ordinary modular Lean and fresh transitive axiom audit',
              'whole_submission_compiled': False, 'submitted': False}
    out = ROOT/'verification/joint-frame-pair-complete-formal-kernel.json'
    out.write_text(json.dumps(record, indent=2)+'\n', encoding='utf8', newline='\n')
    print('Complete modular check:', passed, flush=True)
    raise SystemExit(0 if passed else 1)

if __name__ == '__main__':
    main()
