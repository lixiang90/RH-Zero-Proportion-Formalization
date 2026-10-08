"""Compile a generated single file with pinned Lean and audit selected axioms.

This is a local Lean check. It never claims official Comparator/nanoda
acceptance and does not submit anything to the website.
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
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command: list[str], env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, cwd=ROOT, env=env, capture_output=True,
                          text=True, encoding='utf-8', errors='replace')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('bundle', type=Path)
    parser.add_argument('--axiom', action='append', required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--scope', required=True)
    parser.add_argument('--contract-root', type=Path, default=Path('tmp/contract'))
    args = parser.parse_args()
    source = (ROOT/args.bundle).resolve()
    output = (ROOT/args.output).resolve()
    contract_root = (ROOT/args.contract_root).resolve()
    if not source.is_relative_to(ROOT) or not output.is_relative_to(ROOT/'verification'):
        parser.error('Bundle must stay in repository and output in verification/')
    if not contract_root.is_relative_to(ROOT):
        parser.error('Prepared contract must stay in repository')
    for name in args.axiom:
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', name):
            parser.error('Expected a Lean declaration identifier')
    manifest_path = source.with_suffix('.manifest.json')
    manifest = json.loads(manifest_path.read_text(encoding='utf-8'))
    source_hash = sha(source)
    if manifest['sha256'] != source_hash:
        parser.error('Bundle does not match its generation manifest')
    inputs = {item['path']: item['sha256'] for item in manifest['sources']}
    for path, expected in inputs.items():
        if sha(ROOT/path) != expected:
            parser.error('Source changed after generation: ' + path)
    lean, lake = shutil.which('lean'), shutil.which('lake')
    if not lean or not lake:
        parser.error('Lean and Lake must be on PATH')
    version = run([lean, '--version'])
    if version.returncode or 'version 4.33.0-rc2' not in version.stdout:
        raise SystemExit('Website-pinned Lean 4.33.0-rc2 required')
    paths = run([lake, '--no-cache', 'env', sys.executable, '-c',
                 'import os; print(os.environ.get("LEAN_PATH", ""))'])
    if paths.returncode:
        raise SystemExit(paths.stderr)
    environment = os.environ.copy()
    environment['LEAN_PATH'] = str(contract_root) + os.pathsep + paths.stdout.strip()
    spec = contract_root/'ChallengeDeps/CandidateSpec.lean'
    parent = contract_root/'ChallengeDeps.olean'
    if not spec.is_file() or not parent.is_file():
        parser.error('Prepare the exact trusted CandidateSpec and ChallengeDeps parent first')
    snapshots = {**inputs, Path(__file__).resolve().relative_to(ROOT).as_posix(): sha(Path(__file__).resolve()),
                 source.relative_to(ROOT).as_posix(): source_hash,
                 manifest_path.relative_to(ROOT).as_posix(): sha(manifest_path),
                 spec.relative_to(ROOT).as_posix(): sha(spec),
                 parent.relative_to(ROOT).as_posix(): sha(parent)}
    folder = ROOT/'tmp/verification'
    folder.mkdir(parents=True, exist_ok=True)
    stem = re.sub(r'[^A-Za-z_0-9]', '_', output.stem)
    audit = folder/(stem + '_BundleAudit.lean')
    audit.write_text(source.read_text(encoding='utf-8') + '\n' +
                     ''.join('#print axioms ' + name + '\n' for name in args.axiom),
                     encoding='utf-8', newline='\n')
    audit_hash = sha(audit)
    spec_command = [lean, '+leanprover/lean4:v4.33.0-rc2', '--root='+str(contract_root),
                    '-o', str(spec.with_suffix('.olean')), str(spec)]
    command = [lean, '+leanprover/lean4:v4.33.0-rc2', '--tstack=32768', '-j1',
               '-DstderrAsMessages=false', '-o', str(audit.with_suffix('.olean')), str(audit)]
    print('Compiling prepared specification and single file:', source.name, flush=True)
    start = time.monotonic()
    spec_run = run(spec_command, environment)
    log_path = folder/(stem + '.log')
    actual = None
    with log_path.open('w', encoding='utf-8', newline='\n') as log_file:
        log_file.write(spec_run.stdout + spec_run.stderr + '\nBUNDLE COMPILE\n')
        log_file.flush()
        if spec_run.returncode == 0:
            actual = subprocess.run(command, cwd=ROOT, env=environment,
                                    stdout=log_file, stderr=subprocess.STDOUT)
    log = log_path.read_text(encoding='utf-8', errors='replace')
    observed = {}
    if actual is not None and actual.returncode == 0:
        for name in args.axiom:
            match = re.search(r"'" + re.escape(name) + r"' depends on axioms:\s*\[([^]]*)\]", log)
            if match:
                observed[name] = [word.strip() for word in match.group(1).split(',') if word.strip()]
            elif re.search(r"'" + re.escape(name) + r"' does not depend on any axioms", log):
                observed[name] = []
    unchanged = sha(audit) == audit_hash and all(sha(ROOT/path) == expected for path,expected in snapshots.items())
    passed = (spec_run.returncode == 0 and actual is not None and actual.returncode == 0
              and unchanged and set(observed) == set(args.axiom)
              and all(set(axioms) <= ALLOWED for axioms in observed.values()))
    record = {'compiler': version.stdout.strip(), 'bundle': source.relative_to(ROOT).as_posix(),
              'bundle_bytes': source.stat().st_size, 'compiled_input': audit.relative_to(ROOT).as_posix(),
              'compiled_input_sha256': audit_hash, 'source_sha256': snapshots,
              'source_unchanged_during_check': unchanged, 'spec_command': spec_command,
              'spec_exit_code': spec_run.returncode, 'command': command,
              'exit_code': actual.returncode if actual else None, 'observed_axioms': observed,
              'single_file_lean_check_passed': passed,
              'elapsed_seconds': round(time.monotonic()-start, 2), 'scope': args.scope,
              'official_comparator_passed': False, 'independent_nanoda_passed': False,
              'whole_submission_verified': False, 'submitted': False}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps(record, indent=2), flush=True)
    raise SystemExit(0 if passed else 1)


if __name__ == '__main__':
    main()
