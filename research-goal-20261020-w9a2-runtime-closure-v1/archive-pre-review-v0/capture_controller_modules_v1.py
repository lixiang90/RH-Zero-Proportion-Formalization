"""Current Python stdlib loader metadata only; no verifier/tool main executed.

ctypes is instrumentation, not a frozen-runner import. Its baseline is recorded
separately before the exact frozen-runner stdlib imports are evaluated.
"""
import ctypes
import sys


def modules():
    kernel = ctypes.WinDLL('kernel32', use_last_error=True)
    kernel.GetCurrentProcess.restype = ctypes.c_void_p
    kernel.K32EnumProcessModules.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_void_p),
                                            ctypes.c_ulong, ctypes.POINTER(ctypes.c_ulong)]
    kernel.K32EnumProcessModules.restype = ctypes.c_int
    kernel.GetModuleFileNameW.argtypes = [ctypes.c_void_p, ctypes.c_wchar_p, ctypes.c_ulong]
    kernel.GetModuleFileNameW.restype = ctypes.c_ulong
    handles = (ctypes.c_void_p * 2048)()
    needed = ctypes.c_ulong()
    if not kernel.K32EnumProcessModules(kernel.GetCurrentProcess(), handles,
                                      ctypes.sizeof(handles), ctypes.byref(needed)):
        raise ctypes.WinError(ctypes.get_last_error())
    if needed.value > ctypes.sizeof(handles):
        raise RuntimeError('Module buffer too small; no partial success')
    paths = []
    for i in range(needed.value // ctypes.sizeof(ctypes.c_void_p)):
        path = ctypes.create_unicode_buffer(32768)
        length = kernel.GetModuleFileNameW(handles[i], path, len(path))
        if not length or length >= len(path):
            raise RuntimeError('Could not resolve the full actual module path')
        paths.append(path.value)
    return paths


instrumented_baseline = modules()

# Exact standard-library imports from the frozen v1 verifier; the verifier
# module itself is deliberately not imported, compiled or executed.
import argparse
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time
import traceback

actual_paths = modules()
native_extensions = sorted({str(Path(module.__file__).resolve())
    for module in tuple(sys.modules.values())
    if getattr(module, '__file__', None) and Path(module.__file__).suffix.lower() == '.pyd'})
baseline_keys = {str(Path(path).resolve()).casefold() for path in instrumented_baseline}
records = []
for value in actual_paths:
    path = Path(value)
    raw = path.read_bytes()
    records.append({'path': str(path), 'resolved_path': str(path.resolve()),
                    'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest(),
                    'already_loaded_by_instrumentation_baseline': str(path.resolve()).casefold() in baseline_keys})
new_modules = [row for row in records if not row['already_loaded_by_instrumentation_baseline']]
expected = {'_decimal.pyd', '_hashlib.pyd'}
found = {Path(row['path']).name.casefold() for row in new_modules}
if not expected <= found:
    raise RuntimeError('Expected actual frozen-stdlib extension modules were not observed')
runner = Path(__file__).resolve().parents[1] / 'research-goal-20261020-w9a2-verification-preparation-v1/run_verification.py'
runner_sha = hashlib.sha256(runner.read_bytes()).hexdigest()
if runner_sha != '92cc8dcf3e3c46e76490ba7bfe8d93bc10e331131eaab3b4c3ae500f80ac66a8':
    raise RuntimeError('Frozen v1 runner identity changed')
output = {'scope': 'Current Python312 process loader metadata after exact v1 stdlib imports; no verifier module or proof/tool main run.',
    'captured_at_utc': datetime.now(timezone.utc).isoformat(), 'python': sys.executable,
    'sys_version': sys.version, 'runner_sha256': runner_sha,
    'instrumentation': 'ctypes plus Kernel32 K32EnumProcessModules/GetModuleFileNameW metadata APIs only',
    'instrumentation_baseline_paths': instrumented_baseline,
    'all_actual_loaded_modules_with_instrumentation': records,
    'new_actual_modules_after_frozen_stdlib_imports': new_modules,
    'native_extension_paths_including_ctypes_instrumentation': native_extensions,
    'instrumentation_modules_are_not_claimed_as_frozen_runner_requirements': True,
    'complete_runtime_approved': False, 'compiler_export_kernel_runs': 0}
target = Path(__file__).with_name('controller-stdlib-loaded-modules.json')
with target.open('x', encoding='utf-8', newline='\n') as stream:
    json.dump(output, stream, ensure_ascii=False, indent=2)
    stream.write('\n')
    stream.flush()
    os.fsync(stream.fileno())
print(json.dumps({'path': str(target), 'sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
                  'new_modules': [{'path': row['path'], 'sha256': row['sha256']} for row in new_modules]}))
