"""Compile the self-contained base in a trusted-package-only Lean environment.

This is a packaging/auxiliary-proof check, not complete finite coverage or a
website-ready proof.  The final upload has a separate full verifier.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
def main():
  ap=argparse.ArgumentParser();ap.add_argument('--compressed',action='store_true');args=ap.parse_args()
  cmd=[sys.executable,'-B','-X','utf8',str(HERE/'bundle.py'),'--prune','--encoded-core']
  if args.compressed:cmd.append('--compressed-base')
  subprocess.run(cmd,check=True)
  runtime=json.loads((ROOT/'verification/gram-defect-20261015/setup/runtime.json').read_text())
  src=HERE/'BundlePreflight.lean';before=hashlib.sha256(src.read_bytes()).hexdigest()
  prefix=['wsl.exe','--distribution','Ubuntu','--exec'];lib='/var/tmp/rh-zero-20261015/w10-base-preflight'
  subprocess.run(prefix+['mkdir','-p',lib],check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  linux='/mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization'
  name='compressed-preflight' if args.compressed else 'ordinary-preflight'
  resource_path=lib+'/'+name+'-resources.log'
  command=prefix+['env','LEAN_PATH='+runtime['lean_path'],'/usr/bin/time','-v','-o',resource_path,runtime['lean'],'-j1','--tstack=32768',
    '-DrelaxedAutoImplicit=false','-R',linux,'-o',lib+('/Compressed.olean' if args.compressed else '/Ordinary.olean'),
    linux+'/research-20261016-w10-cert/BundlePreflight.lean']
  start=time.monotonic()
  # Stream diagnostics to disk even if the compiler is killed before returning.
  log=HERE/(name+'.log')
  with log.open('wb') as output:
    r=subprocess.run(command,stdout=output,stderr=subprocess.STDOUT)
  seconds=time.monotonic()-start
  resources=subprocess.run(prefix+['cat',resource_path],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
  (HERE/(name+'-resources.log')).write_bytes(resources.stdout)
  result={'scope':__doc__,'passed':r.returncode==0,'exit_code':r.returncode,
    'source_sha256':before,'source_unchanged':before==hashlib.sha256(src.read_bytes()).hexdigest(),
    'source_bytes':src.stat().st_size,'seconds':seconds,'command':command,
    'resource_log_sha256':hashlib.sha256(resources.stdout).hexdigest(),
    'all_partition_checked':False,'higher_kappa_proven':False}
  (HERE/(name+'.json')).write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
  print(json.dumps({k:result[k] for k in ['passed','exit_code','source_bytes','seconds']}),flush=True)
  if r.returncode:print(log.read_bytes().decode('utf8',errors='replace')[-10000:],flush=True)
  raise SystemExit(r.returncode)
if __name__=='__main__':main()
