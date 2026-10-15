"""Pinned ordinary Lean check for W10 admissibility only (no analytic floor)."""
import hashlib,json,subprocess,time,argparse
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).resolve().parent
runtime=json.loads((ROOT/'tmp/setup-20261015/runtime.json').read_text())
parser=argparse.ArgumentParser();parser.add_argument('--module',default='W10Candidate')
parser.add_argument('--receipt',default='spectral-w10-compile.json');args=parser.parse_args()
source=ROOT/('StructuralResearch20261016/'+args.module+'.lean')
source_sha=hashlib.sha256(source.read_bytes()).hexdigest()
linux_root='/mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization'
out='/var/tmp/rh-zero-20261015/research-20261016/lib/StructuralResearch20261016/'+args.module+'.olean'
lp='/var/tmp/rh-zero-20261015/research-20261016/lib:/var/tmp/rh-zero-20261015/record-verification/modular/lib:'+runtime['lean_path']
command=['wsl.exe','--distribution','Ubuntu','--exec','env','LEAN_PATH='+lp,runtime['lean'],
    '-j1','--tstack=32768','-DrelaxedAutoImplicit=false','-R',linux_root,'-o',out,
    linux_root+'/StructuralResearch20261016/'+args.module+'.lean']
started=time.monotonic();result=subprocess.run(command,capture_output=True)
def decode(data):return data.decode('utf-16-le' if data.count(b'\0')>len(data)//6 else 'utf8',errors='replace')
stdout,stderr=decode(result.stdout),decode(result.stderr)
record={'scope':'Ordinary Lean elaboration and axiom printout of rational W10 admissibility only; no local floor asserted',
    'source':'StructuralResearch20261016/'+args.module+'.lean','source_sha256':source_sha,
    'source_after_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
    'lean_sha256':runtime['lean_sha256'],'command':command,'exit_code':result.returncode,
    'elapsed_seconds':time.monotonic()-started,'stdout':stdout,'stderr':stderr,
    'status':'PASSED' if result.returncode==0 and 'sorryAx' not in stdout else 'FAILED'}
(HERE/args.receipt).write_text(json.dumps(record,indent=2)+'\n')
print(stdout);print(stderr);print(record['status'],record['elapsed_seconds'])
raise SystemExit(result.returncode)
