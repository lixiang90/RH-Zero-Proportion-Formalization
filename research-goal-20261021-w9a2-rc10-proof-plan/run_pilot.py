"""Prepared single new-proof pilot. Requires a separately enabled, pinned root gate.

Uses historical proved Prefix/Core only as development imports. This never proves
new single-file resource compliance, independent-kernel success or site acceptance.
"""
import argparse
import ctypes
from ctypes import wintypes
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / 'tmp/w9a2-20261021/rc10-five-cut-pilot-v1'
LIMIT = 7 * 1024**3


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def digest(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        while b := f.read(1024 * 1024):
            h.update(b)
    return h.hexdigest()


def write_new(p, value):
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as f:
        f.write((json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode())
        f.flush()
        os.fsync(f.fileno())


def local(value):
    p = (ROOT / value).resolve()
    require(p.is_relative_to(ROOT), 'Path outside workspace')
    return p


class Counters(ctypes.Structure):
    _fields_ = [('cb', wintypes.DWORD), ('PageFaultCount', wintypes.DWORD)] + [
        (n, ctypes.c_size_t) for n in ('PeakWorkingSetSize', 'WorkingSetSize',
        'QuotaPeakPagedPoolUsage', 'QuotaPagedPoolUsage',
        'QuotaPeakNonPagedPoolUsage', 'QuotaNonPagedPoolUsage',
        'PagefileUsage', 'PeakPagefileUsage', 'PrivateUsage')]


def main():
    t0 = time.monotonic()
    ap = argparse.ArgumentParser()
    ap.add_argument('--gate', required=True)
    ap.add_argument('--gate-sha256', required=True)
    args = ap.parse_args()
    require(os.name == 'nt' and __debug__, 'Non-optimized Windows Python required')
    gp = local(args.gate)
    require(digest(gp) == args.gate_sha256, 'Gate identity changed')
    g = json.loads(gp.read_bytes())
    require(g['allow_execution'] is True and g['sole_owner'] == '/root', 'Disabled gate')
    require(g['schema'] == 'rc10-five-cut-new-proof-pilot-v1', 'Wrong scope')
    require(g['runner_sha256'] == digest(Path(__file__)), 'Runner changed')
    require(g['budget_seconds'] == 3200 and g['M_MiB'] == 6500 and g['RSS_stop_bytes'] == LIMIT,
            'Fixed limits changed')
    require(g['automatic_retries'] == 0, 'Retries prohibited')
    require(not WORK.exists(), 'Work already exists; never reuse or retry')
    WORK.mkdir(parents=True)
    r = dict(scope=g['schema'], started_UTC=datetime.now(timezone.utc).isoformat(),
             parent_pid=os.getpid(), gate_sha256=args.gate_sha256, source=g['source'],
             cached_strengthened_Core_development_import=True, single_file_resource_pass=False,
             independent_kernel_pass=False, official_acceptance=False, pilot_pass=False,
             timed_out=False, RSS_stopped=False, actual_outer_exit_requires_root_handle=True)
    proc = None
    immutable = []
    samples = []
    status = 1
    try:
        immutable.extend(((gp, args.gate_sha256), (Path(__file__).resolve(), g['runner_sha256'])))
        for key in ('lean', 'python'):
            row = g[key]
            require(digest(Path(row['path'])) == row['sha256'], key + ' identity changed')
            immutable.append((Path(row['path']), row['sha256']))
        require(Path(sys.executable).resolve() == Path(g['python']['path']).resolve(), 'Wrong Python')
        for row in g['direct_inputs']:
            p = local(row['path'])
            require(p.stat().st_size == row['bytes'] and digest(p) == row['sha256'], 'Input changed: ' + str(p))
            immutable.append((p, row['sha256']))
        src = local(g['source']['path'])
        require(0 < g['source']['bytes'] <= 8192, 'Pilot source exceeds fixed byte gate')
        require(src.stat().st_size == g['source']['bytes'] and digest(src) == g['source']['sha256'], 'Source changed')
        immutable.append((src, g['source']['sha256']))
        dest = WORK / 'source/Pilot.lean'
        dest.parent.mkdir()
        shutil.copyfile(src, dest)
        immutable.append((dest, g['source']['sha256']))
        trusted = WORK / 'trusted-lib'
        require({v['module_path'] for v in g['cached_modules']} == {
            'ChallengeDeps.olean', 'ChallengeDeps/CandidateSpec.olean',
            'StructuralW9A220261020/Prefix.olean', 'StructuralW9A220261020/Core.olean'}
            and len(g['cached_modules']) == 4, 'Wrong development import set')
        for row in g['cached_modules']:
            p = local(row['path'])
            require(p.stat().st_size == row['bytes'] and digest(p) == row['sha256'], 'Cached import changed')
            immutable.append((p, row['sha256']))
            q = (trusted / row['module_path']).resolve()
            require(q.is_relative_to(trusted.resolve()), 'Import copy escapes trusted directory')
            q.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(p, q)
            require(digest(q) == row['sha256'], 'Import copy changed')
            immutable.append((q, row['sha256']))
        packages = [local(v) for v in g['historical_package_libs']]
        require(len(packages) == 10 and all(p.is_dir() for p in packages), 'Wrong historical library paths')
        for p in packages:
            require(not (p / 'Solution/Candidate.olean').exists() and not (p / 'StructuralW9A220261020/Core.olean').exists(),
                    'Candidate/Core must not come from package libraries')
        outputs = [WORK / ('output/Pilot' + e) for e in ('.olean', '.ilean', '.c')]
        outputs[0].parent.mkdir()
        env = {'PATH': g['sdk_bin'] + ';C:/Windows/System32;C:/Windows',
               'LEAN_SYSROOT': g['sdk_root'], 'LEAN_PATH': ';'.join(map(str, [trusted] + packages)),
               'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8', 'LEAN_ABORT_ON_PANIC': '1',
               'SYSTEMROOT': 'C:/Windows', 'WINDIR': 'C:/Windows'}
        for name in ('HOME', 'USERPROFILE', 'TEMP', 'TMP'):
            p = WORK / ('home' if name in ('HOME', 'USERPROFILE') else 'temp')
            p.mkdir(exist_ok=True)
            env[name] = str(p)
        cmd = [g['lean']['path'], '-j1', '-M6500', '--tstack=262144',
               '-DrelaxedAutoImplicit=false', '-DElab.async=false', '-R', str(dest.parent),
               '-o', str(outputs[0]), '-i', str(outputs[1]), '-c', str(outputs[2]), '--json', str(dest)]
        r.update(argv=cmd, historical_package_libs=list(map(str, packages)),
                 package_trees_rehashed=False, no_official_setup=True, no_Linux_cgroup_equivalence=True)
        write_new(WORK / 'started.json', r)
        api = ctypes.WinDLL('psapi', use_last_error=True).GetProcessMemoryInfo
        api.argtypes = [wintypes.HANDLE, ctypes.POINTER(Counters), wintypes.DWORD]
        api.restype = wintypes.BOOL
        def sample(final):
            c = Counters()
            c.cb = ctypes.sizeof(c)
            require(api(wintypes.HANDLE(int(proc._handle)), ctypes.byref(c), c.cb), 'Owned-handle memory query failed')
            v = dict(elapsed_s=time.monotonic()-t0, final=final, child_pid=proc.pid,
                     peak_RSS=c.PeakWorkingSetSize, peak_commit=c.PeakPagefileUsage)
            samples.append(v)
            with (WORK / 'memory.jsonl').open('ab') as f:
                f.write((json.dumps(v) + '\n').encode())
            print(json.dumps(v), flush=True)
            return c.PeakWorkingSetSize
        with (WORK / 'stdout.jsonl').open('xb') as out, (WORK / 'stderr.log').open('xb') as err:
            require(time.monotonic()-t0 < 3200, 'Budget expired before launch')
            proc = subprocess.Popen(cmd, cwd=WORK, env=env, stdin=subprocess.DEVNULL,
                                    stdout=out, stderr=err)
            write_new(WORK / 'child.json', dict(child_pid=proc.pid, argv=cmd, owned_handle=True))
            print(json.dumps(dict(child_pid=proc.pid, parent_pid=os.getpid(), started=True)), flush=True)
            while True:
                if sample(False) >= LIMIT:
                    r['RSS_stopped'] = True
                    proc.kill()
                    break
                remaining = 3200 - (time.monotonic()-t0)
                if remaining <= 0:
                    r['timed_out'] = True
                    proc.kill()
                    break
                try:
                    proc.wait(timeout=min(30, remaining))
                    break
                except subprocess.TimeoutExpired:
                    pass
            r['actual_child_exit_code'] = proc.wait()
            final_peak = sample(True)
            require(final_peak < LIMIT, 'Final owned-process peak exceeds RSS gate')
        require(r['actual_child_exit_code'] == 0 and not r['RSS_stopped'] and not r['timed_out'], 'Child did not pass')
        for p, h in immutable:
            require(digest(p) == h, 'Copied input changed during pilot')
        require(all(p.is_file() and p.stat().st_size > 0 for p in outputs), 'Missing fresh outputs')
        r['outputs'] = [dict(path=str(p), bytes=p.stat().st_size, sha256=digest(p)) for p in outputs]
        require(time.monotonic()-t0 < 3200, 'Budget expired at final evidence')
        status = 0
    except BaseException as exc:
        r['failure'] = repr(exc)
        if proc is not None and proc.poll() is None:
            proc.kill()
            r['actual_child_exit_code'] = proc.wait()
    finally:
        r['logs'] = [dict(path=str(p), bytes=p.stat().st_size, sha256=digest(p))
                     for p in (WORK / 'stdout.jsonl', WORK / 'stderr.log', WORK / 'memory.jsonl')
                     if p.is_file()]
        if time.monotonic()-t0 >= 3200:
            status = 1
            r['timed_out'] = True
        r['pilot_pass'] = status == 0
        r.update(elapsed_s=time.monotonic()-t0, memory_samples=len(samples),
                 peak_RSS=max((v['peak_RSS'] for v in samples), default=None),
                 peak_commit=max((v['peak_commit'] for v in samples), default=None),
                 parent_exit_code_to_return_not_external_observation=status)
        write_new(WORK / 'terminal.json', r)
        # A late terminal write cannot authorize an over-budget successful return.
        # Root must additionally observe this original outer process's actual exit.
        if time.monotonic()-t0 >= 3200:
            status = 1
            r.update(pilot_pass=False, timed_out=True,
                     elapsed_s=time.monotonic()-t0,
                     parent_exit_code_to_return_not_external_observation=1)
            with (WORK / 'terminal.json').open('wb') as f:
                f.write((json.dumps(r, ensure_ascii=False, indent=2)+'\n').encode())
                f.flush()
                os.fsync(f.fileno())
        print(json.dumps(dict(terminal=str(WORK / 'terminal.json'), status=status,
                              pilot_pass=r['pilot_pass'])), flush=True)
    if time.monotonic()-t0 >= 3200:
        return 1
    return status


if __name__ == '__main__':
    raise SystemExit(main())
