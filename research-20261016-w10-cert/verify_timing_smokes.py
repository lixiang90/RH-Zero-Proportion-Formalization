"""Replay timed subtree experiments using the shared pinned Lean queue."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--modules', nargs='+', default=[
        'TimedClosedTreeSmoke', 'ForcedCoverage2', 'TimedForce2Smoke'])
    parser.add_argument('--receipt', type=Path, default=HERE / 'timing-smokes-verification.json')
    args = parser.parse_args()
    runtime = json.loads((ROOT / 'tmp/setup-20261015/runtime.json').read_text())
    lib = '/var/tmp/rh-zero-20261015/w10-cert/lib'
    linux = '/mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization'
    lp = ':'.join([lib, '/var/tmp/rh-zero-20261015/research-20261016/lib',
                   '/var/tmp/rh-zero-20261015/record-verification/modular/lib',
                   runtime['lean_path']])
    digest = subprocess.run(['wsl.exe', '--distribution', 'Ubuntu', '--exec',
                             '/usr/bin/sha256sum', runtime['lean']],
                            capture_output=True, check=True).stdout.decode('utf8').split()[0]
    assert digest == 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
    record = {'scope': 'Ordinary Lean subtree timing; imports/data are excluded from marked certificate milliseconds. No global floor.',
              'compiler_sha256': digest, 'modules': [], 'passed': False}
    for module in args.modules:
        assert re.fullmatch('[A-Za-z0-9_]+', module)
        relative = 'StructuralW10Cert20261016/' + module
        source = ROOT / (relative + '.lean')
        source_digest = hashlib.sha256(source.read_bytes()).hexdigest()
        argv = ['wsl.exe', '--distribution', 'Ubuntu', '--exec', 'env',
                'LEAN_PATH=' + lp, runtime['lean'], '-j1', '--tstack=32768',
                '-DrelaxedAutoImplicit=false', '-R', linux,
                '-o', lib + '/' + relative + '.olean', linux + '/' + relative + '.lean']
        start = time.monotonic()
        result = subprocess.run(argv, capture_output=True)
        elapsed = time.monotonic() - start
        output = result.stdout.decode('utf8', errors='replace')
        log = result.stdout + result.stderr
        (HERE / ('timing-' + module.lower() + '.log')).write_bytes(log)
        marks = {key: int(value) for key, value in
                 re.findall(r'W10_TIMING\s+(\w+)\s+(\d+)', output)}
        item = {'module': relative.replace('/', '.'), 'command': argv,
                'exit_code': result.returncode, 'whole_process_seconds': elapsed,
                'source_sha256': source_digest,
                'source_unchanged': hashlib.sha256(source.read_bytes()).hexdigest() == source_digest,
                'stdout': output, 'log_sha256': hashlib.sha256(log).hexdigest(),
                'marks_milliseconds': marks,
                'synchronous_elaboration': 'set_option Elab.async false' in source.read_text(encoding='utf8'),
                'passed': result.returncode == 0 and 'sorryAx' not in output}
        if 'certificate_begin' in marks and 'certificate_end' in marks:
            label = 'certificate_seconds' if item['synchronous_elaboration'] else 'pre_async_task_mark_seconds'
            item[label] = (marks['certificate_end'] - marks['certificate_begin']) / 1000
        record['modules'].append(item)
        record['passed'] = all(m['passed'] for m in record['modules']) and len(record['modules']) == len(args.modules)
        args.receipt.write_text(json.dumps(record, indent=2) + '\n', encoding='utf8')
        print(json.dumps(item), flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)


if __name__ == '__main__':
    main()
