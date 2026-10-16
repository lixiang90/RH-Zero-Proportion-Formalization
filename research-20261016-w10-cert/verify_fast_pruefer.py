"""Ordinary pinned Lean replay of fast flow reconstruction and the real subtree.

Run only after obtaining the shared Core compilation queue.  This script does
not rerun or replace the frozen baseline receipt.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
runtime = json.loads((ROOT / 'tmp/setup-20261015/runtime.json').read_text())
lib = '/var/tmp/rh-zero-20261015/w10-cert/lib'
linux = '/mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization'
lp = ':'.join([lib, '/var/tmp/rh-zero-20261015/research-20261016/lib',
               '/var/tmp/rh-zero-20261015/record-verification/modular/lib',
               runtime['lean_path']])
record = {'scope': 'Fast interpreter soundness and the same real 63-node closed subtree; no global floor.',
          'compiler_sha256': 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
          'modules': [], 'passed': False}
for module in ['FastPruefer', 'FastClosedTreeSmoke']:
    relative = 'StructuralW10Cert20261016/' + module
    source = ROOT / (relative + '.lean')
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    argv = ['wsl.exe', '--distribution', 'Ubuntu', '--exec', 'env',
            'LEAN_PATH=' + lp, runtime['lean'], '-j1', '--tstack=32768',
            '-DrelaxedAutoImplicit=false', '-R', linux,
            '-o', lib + '/' + relative + '.olean', linux + '/' + relative + '.lean']
    start = time.monotonic()
    result = subprocess.run(argv, capture_output=True)
    elapsed = time.monotonic() - start
    output = result.stdout.decode('utf8', errors='replace')
    log = result.stdout + result.stderr
    (HERE / ('fast-' + module.lower() + '-lean.log')).write_bytes(log)
    item = {'module': relative.replace('/', '.'), 'command': argv,
            'exit_code': result.returncode, 'seconds': elapsed,
            'source_sha256': digest,
            'source_unchanged': hashlib.sha256(source.read_bytes()).hexdigest() == digest,
            'stdout': output, 'log_sha256': hashlib.sha256(log).hexdigest(),
            'passed': result.returncode == 0 and 'sorryAx' not in output}
    record['modules'].append(item)
    record['passed'] = all(m['passed'] for m in record['modules']) and len(record['modules']) == 2
    (HERE / 'fast-pruefer-verification.json').write_text(
        json.dumps(record, indent=2) + '\n', encoding='utf8')
    print(json.dumps(item), flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
