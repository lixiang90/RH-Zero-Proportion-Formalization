from pathlib import Path
import hashlib,json,subprocess,time,sys
sys.stdout.reconfigure(encoding='utf8')
attempt=sys.argv[1] if len(sys.argv)>1 else 'initial'
assert attempt.replace('-','').isalnum()
project=Path('E:/codex-build/RH-Weil')
formal=Path('E:/codex-build/RH-Zero-Proportion-Formalization')
handoff=json.loads((formal/'verification/linux-memory-time-20261010/am/environment/handoff-v3.json').read_text(encoding='utf8'))
linuxroot='/mnt/e/codex-build/RH-Zero-Proportion-Formalization'
lp=linuxroot+'/.lake/build/lib/lean:'+handoff['lean_path']
compiler=handoff['lean']
version=subprocess.check_output(['wsl','-d','Ubuntu','--exec',compiler,'--version'],text=True).strip()
compiler_sha=subprocess.check_output(['wsl','-d','Ubuntu','--exec','sha256sum',compiler],text=True).split()[0]
assert compiler_sha==handoff['lean_sha256']
source=formal/'RecordProportion/NinthSpanPoints.lean'
source_sha=hashlib.sha256(source.read_bytes()).hexdigest()
cmd=['wsl','-d','Ubuntu','--exec','env','LEAN_PATH='+lp,compiler,'-j1','--tstack=32768','-R',linuxroot,'-o',linuxroot+'/.lake/build/lib/lean/RecordProportion/NinthSpanPoints.olean',linuxroot+'/RecordProportion/NinthSpanPoints.lean']
started=time.monotonic()
p=subprocess.run(cmd,capture_output=True,text=True,encoding='utf8',errors='replace')
assert hashlib.sha256(source.read_bytes()).hexdigest()==source_sha
log=project/f'tmp/ninth-span-points-linux-{attempt}.log'
log.write_text(p.stdout+p.stderr,encoding='utf8',newline='\n')
result={'exit_code':p.returncode,'elapsed_seconds':time.monotonic()-started,'source_sha256':source_sha,'compiler_sha256':compiler_sha,'compiler_version':version,'command':cmd,'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()}
(project/f'tmp/ninth-span-points-linux-{attempt}.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8',newline='\n')
print(json.dumps(result,indent=2)); print(p.stdout+p.stderr)
raise SystemExit(p.returncode)
