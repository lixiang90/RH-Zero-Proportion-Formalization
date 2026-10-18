"""Pinned Windows-Python interop helper, invoked only by the gated Linux owner.

No subprocess is created: runpy executes the pinned generator in this process.
The PID file lets the Linux owner terminate this exact Windows process tree if
the common deadline expires while WSL interop is active.
"""
import hashlib
import json
import os
from pathlib import Path
import runpy
import sys

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
FLATTEN = ROOT / 'research-goal-20261018-tiny-flatten-preparation-v3'
MIRROR = ROOT / 'tmp/current-s1r-tiny-20261018/production-v0'
EXPECTED = '8d866f77503210091280574f6a14fcead5461f07c156f383f1b67f78ee52ab32'

def main():
    assert os.name == 'nt' and __debug__
    assert sys.argv[1:] == ['--gated-generator-once', EXPECTED]
    assert hashlib.sha256((FLATTEN / 'prepared-files.json').read_bytes()).hexdigest() == EXPECTED
    assert MIRROR.is_dir() and not (MIRROR / 'windows-generator.pid.json').exists()
    with (MIRROR / 'windows-generator.pid.json').open('x', encoding='utf-8') as f:
        json.dump({'pid': os.getpid(), 'helper': str(Path(__file__).resolve()),
                   'generator': str(FLATTEN / 'generate_draft.py'),
                   'prepared_manifest_sha256': EXPECTED}, f)
        f.flush(); os.fsync(f.fileno())
    sys.argv = [str(FLATTEN / 'generate_draft.py'), '--generate-draft-once',
                '--prepared-sha256', EXPECTED]
    runpy.run_path(sys.argv[0], run_name='__main__')

if __name__ == '__main__':
    main()
