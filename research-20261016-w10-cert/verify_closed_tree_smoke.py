"""Ordinary Lean end-to-end replay timing of the real 63-node closed subtree."""
from pathlib import Path
import hashlib,json,subprocess,time
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).resolve().parent
source=ROOT/'StructuralW10Cert20261016/ClosedTreeSmoke.lean';digest=hashlib.sha256(source.read_bytes()).hexdigest()
runtime=json.loads((ROOT/'tmp/setup-20261015/runtime.json').read_text())
lib='/var/tmp/rh-zero-20261015/w10-cert/lib';linux='/mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization'
lp=lib+':/var/tmp/rh-zero-20261015/research-20261016/lib:/var/tmp/rh-zero-20261015/record-verification/modular/lib:'+runtime['lean_path']
argv=['wsl.exe','--distribution','Ubuntu','--exec','env','LEAN_PATH='+lp,runtime['lean'],'-j1','--tstack=32768','-DrelaxedAutoImplicit=false','-R',linux,'-o',lib+'/StructuralW10Cert20261016/ClosedTreeSmoke.olean',linux+'/StructuralW10Cert20261016/ClosedTreeSmoke.lean']
start=time.monotonic();result=subprocess.run(argv,capture_output=True);elapsed=time.monotonic()-start
stdout=result.stdout.decode('utf8',errors='replace');log=result.stdout+result.stderr;(HERE/'closed-tree-smoke-lean.log').write_bytes(log)
record={'scope':'Real 63-node closed subtree ordinary Lean and kernel evaluation, not the complete global tree.',
 'command':argv,'exit_code':result.returncode,'seconds':elapsed,'nodes':63,'numeric_leaves':32,
 'source_sha256':digest,'source_unchanged':hashlib.sha256(source.read_bytes()).hexdigest()==digest,
 'stdout':stdout,'log_sha256':hashlib.sha256(log).hexdigest(),'passed':result.returncode==0 and 'sorryAx'not in stdout}
(HERE/'closed-tree-smoke-lean.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record),flush=True)
raise SystemExit(result.returncode)
