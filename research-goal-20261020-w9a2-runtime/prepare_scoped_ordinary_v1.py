"""Version only the overbroad process guard after unrelated 4.32.2 observation."""
from pathlib import Path
import ast
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
old=ROOT/'research-goal-20261020-w9a2-runtime/compile_frozen.py'
assert sha(old)=='09b7478efdc8ed380df82b7e04329cd783e347230b46ff283014e20a36822c62'
raw=old.read_bytes()
before=b'''    ps = subprocess.run(['powershell.exe', '-NoProfile', '-Command',
                         "@(Get-Process lean -ErrorAction SilentlyContinue).Count"],
                        capture_output=True, text=True, check=True)
    assert ps.stdout.strip() == '0', 'Another ordinary Lean process is active'
'''.replace(b'\n', b'\r\n') if b'\r\n' in raw else b'''    ps = subprocess.run(['powershell.exe', '-NoProfile', '-Command',
                         "@(Get-Process lean -ErrorAction SilentlyContinue).Count"],
                        capture_output=True, text=True, check=True)
    assert ps.stdout.strip() == '0', 'Another ordinary Lean process is active'
'''
after='''    # Exclude this exact pinned compiler, not unrelated user projects on other SDKs.
    # No untrusted input is interpolated into shell text; compiler path is read via env.
    probe_env = os.environ.copy()
    probe_env['W9A2_PINNED_LEAN'] = str(lean.resolve())
    probe_script = "@((Get-CimInstance Win32_Process -Filter \\\"Name='lean.exe'\\\") | Where-Object { $_.ExecutablePath -eq $env:W9A2_PINNED_LEAN }).Count"
    ps = subprocess.run(['powershell.exe', '-NoProfile', '-Command', probe_script],
                        capture_output=True, text=True, check=True, env=probe_env)
    assert ps.stdout.strip() == '0', 'Another pinned 4.33.0-rc2 Lean process is active'
'''.encode()
if b'\r\n' in raw: after=after.replace(b'\n',b'\r\n')
assert raw.count(before)==1
new=raw.replace(before,after)
ast.parse(new.decode())
runner=old.with_name('compile_frozen_scoped_v1.py')
with runner.open('xb') as f: f.write(new)
gpath=ROOT/'research-goal-20261016/gates/w9a2-ordinary-v1-20261020.json'
assert sha(gpath)=='404f40b867012947f1b08d6037fe9469488be1704377ce0e4ed2d6e8e05c178b'
gate=json.loads(gpath.read_text())
gate['runner_sha256']=sha(runner)
gate['source_files'] += [{'path':p.relative_to(ROOT).as_posix(),'sha256':sha(p)} for p in [gpath,runner,Path(__file__)]]
gate['process_guard_scope']='No other process executing this exact pinned Lean 4.33.0-rc2; unrelated user-owned 4.32.2 projects are observed and untouched.'
gate['prior_v1_entry_rejected_before_candidate_or_job_creation']=True
gate['prior_v1_entry_error']='Global Get-Process lean count included two independently running user 4.32.2 processes, PIDs3860/15312; exact ExecutablePath read via Win32_Process.'
out=gpath.with_name('w9a2-ordinary-v1b-20261020.json')
with out.open('x',encoding='utf-8',newline='\n') as f:
    json.dump(gate,f,indent=2);f.write('\n')
print(json.dumps({'runner_sha256':sha(runner),'gate_sha256':sha(out),'scope':'Same exact repaired mathematics and same five targets; only exclusion scope corrected'}))
