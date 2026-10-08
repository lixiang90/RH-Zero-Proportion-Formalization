"""Build pinned Lean modules and audit named declarations from real processes."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}

def source_snapshots(modules: list[str]) -> dict[str, str]:
    hashes = {}
    def visit(module: str) -> None:
        path = ROOT.joinpath(*module.split('.')).with_suffix('.lean')
        if not path.is_file() or module in hashes:
            return
        source = path.read_bytes()
        hashes[module] = hashlib.sha256(source).hexdigest()
        for line in source.decode('utf-8-sig').splitlines():
            if line.startswith('import '):
                for name in line[7:].split():
                    if name.startswith('RecordProportion'):
                        visit(name)
    for module in modules:
        visit(module)
    return hashes

def run(command: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, cwd=ROOT, capture_output=True,
                          text=True, encoding='utf-8', errors='replace')

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('modules', nargs='+')
    parser.add_argument('--axiom', action='append', required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--scope', required=True)
    args = parser.parse_args()
    for name in args.modules + args.axiom:
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', name):
            parser.error('Expected a Lean module or declaration identifier')
    out = (ROOT/args.output).resolve()
    if not out.is_relative_to(ROOT/'verification'):
        parser.error('Output must stay in verification/')
    lean, lake = shutil.which('lean'), shutil.which('lake')
    if not lean or not lake:
        parser.error('lean and lake must be on PATH')
    version = run([lean, '--version'])
    if version.returncode or 'version 4.33.0-rc2' not in version.stdout:
        raise SystemExit('The website-pinned Lean 4.33.0-rc2 is required')
    snapshots = source_snapshots(args.modules)
    if not all(name in snapshots for name in args.modules):
        parser.error('Module source not found')
    stem = out.stem
    audit_path = ROOT/'tmp/verification'/f'{stem}-axioms.lean'
    audit_path.parent.mkdir(parents=True, exist_ok=True)
    audit_source = ''.join(f'import {name}\n' for name in args.modules)
    audit_source += ''.join(f'#print axioms {name}\n' for name in args.axiom)
    audit_path.write_text(audit_source, encoding='utf-8', newline='\n')
    audit_hash = hashlib.sha256(audit_path.read_bytes()).hexdigest()
    command = [lake, '--no-cache', 'build'] + [f'+{m}:olean' for m in args.modules]
    print('Building:', ', '.join(args.modules), flush=True)
    start = time.monotonic()
    build = run(command)
    audit_command = [lake, 'env', 'lean', str(audit_path)]
    audit = run(audit_command) if build.returncode == 0 else None
    log_path = ROOT/'tmp/verification'/f'{stem}.log'
    log = build.stdout + build.stderr
    if audit is not None:
        log += '\nAXIOM AUDIT\n' + audit.stdout + audit.stderr
    log_path.write_text(log, encoding='utf-8', newline='\n')
    observed = {}
    if audit is not None and audit.returncode == 0:
        for name in args.axiom:
            match = re.search(r"'"+re.escape(name)+r"' depends on axioms:\s*\[([^]]*)\]", audit.stdout)
            if match:
                observed[name] = [v.strip() for v in match.group(1).split(',') if v.strip()]
            elif re.search(r"'"+re.escape(name)+r"' does not depend on any axioms", audit.stdout):
                observed[name] = []
    unchanged = snapshots == source_snapshots(args.modules)
    unchanged = unchanged and audit_hash == hashlib.sha256(audit_path.read_bytes()).hexdigest()
    audit_passed = (audit is not None and audit.returncode == 0
                    and set(observed) == set(args.axiom)
                    and all(set(v) <= ALLOWED for v in observed.values()))
    passed = build.returncode == 0 and unchanged and audit_passed
    record = {'compiler': version.stdout.strip(), 'modules': args.modules,
              'source_sha256': snapshots, 'source_unchanged_during_check': unchanged,
              'build_command': command, 'build_exit_code': build.returncode,
              'audit_command': audit_command,
              'audit_exit_code': audit.returncode if audit else None,
              'observed_axioms': observed, 'allowed_axioms': sorted(ALLOWED),
              'axiom_audit_passed': audit_passed, 'module_check_passed': passed,
              'elapsed_seconds': round(time.monotonic()-start, 2),
              'scope': args.scope, 'log': log_path.relative_to(ROOT).as_posix(),
              'whole_submission_compiled': False, 'submitted': False}
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps(record, indent=2), flush=True)
    raise SystemExit(0 if passed else 1)

if __name__ == '__main__':
    main()
