from pathlib import Path
import hashlib, json, subprocess, time

ROOT = Path('E:/codex-build/RH-Zero-Proportion-Formalization')
TMP = Path('E:/codex-build/RH-Weil/tmp')
SRC = ROOT / 'RecordProportion/NinthSpanPathSoundness.lean'
OUT = ROOT / '.lake/build/lib/lean/RecordProportion/NinthSpanPathSoundness.olean'
HANDOFF = json.loads((ROOT / 'verification/linux-memory-time-20261010/am/environment/handoff-v3.json').read_text())
COMPILER = HANDOFF['lean']
LP = '/mnt/e/codex-build/RH-Zero-Proportion-Formalization/.lake/build/lib/lean:' + HANDOFF['lean_path']
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def linux(p): return '/mnt/' + str(p)[0].lower() + '/' + str(p)[3:].replace('\\', '/')

gate = subprocess.run(['wsl','-d','Ubuntu','--exec','sha256sum',COMPILER],capture_output=True,text=True)
assert gate.returncode == 0
assert gate.stdout.split()[0] == HANDOFF['lean_sha256']
before = sha(SRC)
cmd = ['wsl','-d','Ubuntu','--exec','env','LEAN_PATH='+LP,COMPILER,'-j1','--tstack=32768',
       '-R',linux(ROOT),'-o',linux(OUT),linux(SRC)]
t = time.monotonic()
res = subprocess.run(cmd,capture_output=True,text=True,encoding='utf8')
elapsed = time.monotonic() - t
log = TMP / 'ninth-span-path-compile.txt'
log.write_text(res.stdout+res.stderr,encoding='utf8')
receipt = {'status':'PASS' if res.returncode == 0 else 'FAILED', 'exit_code':res.returncode,
    'wall_seconds':elapsed, 'compiler':COMPILER, 'compiler_sha256':gate.stdout.split()[0],
    'source_sha256_before':before, 'source_sha256_after':sha(SRC),
    'olean_sha256':sha(OUT) if res.returncode == 0 else None,
    'command':cmd,'log_sha256':sha(log)}
(TMP / 'ninth-span-path-compile.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8')
print(json.dumps(receipt,indent=2))
print(res.stdout+res.stderr)
raise SystemExit(res.returncode)
