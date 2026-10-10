"""Export the new unconditional roots and independently replay their full proofs.

Uses the unchanged pinned lean4export sources and the fixed nanoda binary.
This is local modular verification, not a website submission or resource pass.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
EXPORTER_PIN = 'b18d673bd29b476466a51a3be1012df2ed322b10'
NANO_PIN = '418320295890faed83a96fd97907b12a3b6728c2'
ALLOWED = ['propext', 'Quot.sound', 'Classical.choice']
ROOTS = ['RHWeilRecord.NinthSpan.'+name for name in
         ('local_certificate', 'simple_dyadic', 'simple_cumulative',
          'distinct_dyadic', 'distinct_cumulative', 'previous_recordRatio_lt')]
PRIMITIVES = ['Nat', 'String', 'String.mk', 'Char', 'Quot', 'Quot.mk', 'Quot.lift',
              'Quot.ind', 'propext', 'Quot.sound', 'Classical.choice', 'Nat.add',
              'Nat.sub', 'Nat.mul', 'Nat.pow', 'Nat.gcd', 'Nat.div', 'Nat.mod',
              'Nat.beq', 'Nat.ble', 'Nat.land', 'Nat.lor', 'Nat.xor', 'Nat.shiftLeft',
              'Nat.shiftRight', 'String.ofList', 'Char.ofNat', 'List', 'eagerReduce']

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def linux(path: Path) -> str:
    return '/mnt/'+path.drive[0].lower()+str(path)[2:].replace('\\', '/')

def wsl(*args: str) -> list[str]:
    return ['wsl', '--distribution', 'Ubuntu', '--exec', *args]

def main() -> None:
    if not __debug__:
        raise SystemExit('Assertions must remain enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--threads', type=int, choices=(1, 2, 3, 4), default=4)
    args = parser.parse_args()
    for name, pin in [('lean4export', EXPORTER_PIN), ('nanoda', NANO_PIN)]:
        path = ROOT/'tmp'/name
        assert subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD']).decode().strip() == pin
        assert not subprocess.check_output(['git', '-C', str(path), 'diff', '--name-only', 'HEAD']).strip()
    info = json.loads((ROOT/'verification/linux-memory-time-20261010/am/environment/handoff-v3.json').read_text())
    compiler = '/tmp/rh-proportion-memory-20261010/lean-4.33.0-rc2-linux/bin/lean'
    compiler_hash = subprocess.check_output(wsl('sha256sum', compiler)).decode().split()[0]
    assert compiler_hash == info['lean_sha256']
    version = subprocess.check_output(wsl(compiler, '--version')).decode().strip()
    assert 'version 4.33.0-rc2' in version
    formal_receipt = ROOT/'verification/ninth-span-complete-formal-kernel.json'
    formal = json.loads(formal_receipt.read_text())
    assert formal['module_check_passed']
    module = 'RecordProportion.NinthSpan'
    source = ROOT/'RecordProportion/NinthSpan.lean'
    olean = ROOT/'.lake/build/lib/lean/RecordProportion/NinthSpan.olean'
    nano = ROOT/'tmp/kernel-tools/nanoda-target/release/nanoda_bin'
    old_nano = json.loads((ROOT/'verification/three-website-declarations-modular-nanoda.json').read_text())
    assert sha(nano) == old_nano['sha256_before']['nanoda_binary']
    scratch = ROOT/'tmp/verification/ninth-span-complete-independent-nanoda'
    scratch.mkdir(parents=True, exist_ok=True)
    tool_lib = scratch/'tool-lib'
    tool_lib.mkdir(exist_ok=True)
    (tool_lib/'Export').mkdir(exist_ok=True)
    files = {'driver_source': Path(__file__), 'source_lean': source,
             'source_olean': olean, 'nanoda_binary': nano, 'formal_receipt': formal_receipt}
    for name in formal['source_sha256']:
        path = ROOT.joinpath(*name.split('.')).with_suffix('.lean')
        assert sha(path) == formal['source_sha256'][name]
        files['source:'+name] = path
        art = ROOT/'.lake/build/lib/lean'/Path(*name.split('.')).with_suffix('.olean')
        assert sha(art) == formal['olean_sha256'][name]
        files['olean:'+name] = art
    for name in ('Export.lean', 'Export/Parse.lean', 'Main.lean'):
        files['exporter:'+name] = ROOT/'tmp/lean4export'/name
    before = {key: sha(path) for key, path in files.items()}
    start = time.monotonic()
    tools = []
    # Freshly compile the exporter in an isolated directory using pinned sources.
    for name in ('Export', 'Export.Parse'):
        path = ROOT/'tmp/lean4export'/Path(*name.split('.')).with_suffix('.lean')
        art = tool_lib.joinpath(*name.split('.')).with_suffix('.olean')
        command = wsl('env', 'LEAN_PATH='+linux(tool_lib), compiler, '-j1', '--tstack=32768',
                      '-R', linux(ROOT/'tmp/lean4export'), '-o', linux(art), linux(path))
        proc = subprocess.run(command, cwd=ROOT, capture_output=True)
        (scratch/(name+'.log')).write_bytes(proc.stdout+proc.stderr)
        tools.append({'name': name, 'command': command, 'exit_code': proc.returncode,
                      'olean_sha256': sha(art) if art.is_file() else None})
        assert proc.returncode == 0, proc.stdout.decode(errors='replace')+proc.stderr.decode(errors='replace')
        files['exporter_olean:'+name] = art
    before.update({key: sha(path) for key, path in files.items() if key.startswith('exporter_olean:')})
    export = scratch/'export.ndjson'
    export_log = scratch/'export.log'
    lookup = linux(tool_lib)+':'+linux(ROOT/'.lake/build/lib/lean')+':'+info['lean_path']
    command = wsl('env', 'LEAN_PATH='+lookup, compiler, '-j1', '--tstack=32768', '--run',
                  linux(ROOT/'tmp/lean4export/Main.lean'), module, '--', *ROOTS, *PRIMITIVES)
    print('Exporting all six new theorem dependency graphs', flush=True)
    tick = time.monotonic()
    with export.open('wb') as out, export_log.open('wb') as err:
        result = subprocess.run(command, cwd=ROOT, stdout=out, stderr=err)
    export_seconds = time.monotonic()-tick
    assert result.returncode == 0, export_log.read_text(errors='replace')
    files['export'] = export
    config = {'use_stdin': True, 'permitted_axioms': ALLOWED,
              'unpermitted_axiom_hard_error': True,
              'nat_extension': True, 'string_extension': True,
              'num_threads': args.threads, 'unsafe_permit_all_axioms': False,
              'print_success_message': True, 'print_axioms': True, 'pp_to_stdout': True}
    config_path = scratch/'nanoda-config.json'
    config_path.write_text(json.dumps(config, indent=2)+'\n', encoding='utf8', newline='\n')
    files['configuration'] = config_path
    before.update({key: sha(files[key]) for key in ('export', 'configuration')})
    log = scratch/'nanoda.log'
    metrics = scratch/'nanoda-time.txt'
    command_nano = wsl('/usr/bin/time', '-v', '-o', linux(metrics), linux(nano), linux(config_path))
    print('Independent nanoda:', args.threads, 'threads,', export.stat().st_size, 'export bytes', flush=True)
    tick = time.monotonic()
    with export.open('rb') as inp, log.open('wb') as out:
        nano_result = subprocess.run(command_nano, cwd=ROOT, stdin=inp, stdout=out, stderr=subprocess.STDOUT)
    nano_seconds = time.monotonic()-tick
    transcript = log.read_text(encoding='utf8', errors='replace')
    count = re.search(r'Checked (\d+) declarations with no errors', transcript)
    axioms = [n.split('.{')[0] for n in re.findall(r'^axiom ([^\s]+)', transcript, re.MULTILINE)]
    after = {key: sha(path) for key, path in files.items()}
    unchanged = before == after
    passed = (nano_result.returncode == 0 and count is not None and unchanged
              and set(axioms) == set(ALLOWED))
    public = ROOT/'verification/ninth-span-complete-independent-nanoda'
    public.mkdir(parents=True, exist_ok=True)
    public_files = {}
    for name, path in [('export.txt', export_log), ('nanoda.txt', log), ('nanoda-time.txt', metrics),
                       ('nanoda-config.json', config_path), ('Export.txt', scratch/'Export.log'),
                       ('Export.Parse.txt', scratch/'Export.Parse.log')]:
        target = public/name
        target.write_bytes(path.read_bytes())
        public_files[str(target.relative_to(ROOT))] = sha(target)
    record = {'formal_receipt_sha256': before['formal_receipt'], 'published_logs': public_files, 'module': module, 'roots': ROOTS, 'primitive_roots': PRIMITIVES, 'compiler': version,
              'compiler_sha256': compiler_hash,
              'pins': {'lean4export': EXPORTER_PIN, 'nanoda': NANO_PIN},
              'fresh_exporter_compilation': tools, 'export_command': command,
              'export_process_ran': True, 'export_exit_code': result.returncode,
              'export_bytes': export.stat().st_size, 'export_elapsed_seconds': export_seconds,
              'actual_nano_command': command_nano, 'actual_nano_exit_code': nano_result.returncode,
              'checked_declarations': int(count[1]) if count else None,
              'nano_elapsed_seconds': nano_seconds, 'total_elapsed_seconds': time.monotonic()-start,
              'observed_axioms': axioms, 'configuration': config,
              'sha256_before': before, 'sha256_after': after, 'inputs_unchanged': unchanged,
              'nano_check_passed': passed,
              'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log),
              'resources': metrics.read_text(encoding='utf8', errors='replace'),
              'scope': 'Fresh export and complete independent modular proof replay of all six unconditional ninth-span theorem roots',
              'official_comparator_verified': False, 'whole_submission_compiled': False,
              'resource_compliance_established': False, 'submitted': False}
    output = ROOT/'verification/ninth-span-complete-independent-nanoda.json'
    output.write_text(json.dumps(record, indent=2)+'\n', encoding='utf8', newline='\n')
    print(json.dumps({'nano_check_passed': passed, 'checked_declarations': record['checked_declarations'],
                      'nano_elapsed_seconds': nano_seconds, 'inputs_unchanged': unchanged}, indent=2), flush=True)
    raise SystemExit(0 if passed else 1)

if __name__ == '__main__':
    main()
