from pathlib import Path
import hashlib,json,subprocess,time,sys
sys.stdout.reconfigure(encoding='utf8')
formal=Path('E:/codex-build/RH-Zero-Proportion-Formalization')
out=Path(__file__).resolve().parent/'lean-full';out.mkdir(exist_ok=True)
handoff=json.loads((formal/'verification/linux-memory-time-20261010/am/environment/handoff-v3.json').read_text(encoding='utf8'))
linuxroot='/mnt/e/codex-build/RH-Zero-Proportion-Formalization'
lp=linuxroot+'/.lake/build/lib/lean:'+handoff['lean_path']
compiler=handoff['lean']
source=formal/'RecordProportion/NinthSpanFiniteData.lean';sha=hashlib.sha256(source.read_bytes()).hexdigest()
assert subprocess.check_output(['wsl','-d','Ubuntu','--exec','sha256sum',compiler],text=True).split()[0]==handoff['lean_sha256']
cmd=['wsl','-d','Ubuntu','--exec','env','LEAN_PATH='+lp,compiler,'-j1','--tstack=32768',
 '-DrelaxedAutoImplicit=false','-R',linuxroot,'-o',linuxroot+'/.lake/build/lib/lean/RecordProportion/NinthSpanFiniteData.olean',
 linuxroot+'/RecordProportion/NinthSpanFiniteData.lean']
started=time.monotonic();log=out/'data-compile.log'
print('Starting full additive NinthSpanFiniteData kernel compilation.',flush=True)
with log.open('w',encoding='utf8',newline='\n') as f:
 p=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,text=True,encoding='utf8',errors='replace')
result={'exit_code':p.returncode,'elapsed_seconds':time.monotonic()-started,'source_sha256':sha,
 'source_unchanged':hashlib.sha256(source.read_bytes()).hexdigest()==sha,'compiler_sha256':handoff['lean_sha256'],
 'command':cmd,'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()}
(out/'data-audit.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8',newline='\n')
print(json.dumps(result,indent=2),flush=True)
print('\n'.join(log.read_text(encoding='utf8').splitlines()[-30:]))
raise SystemExit(p.returncode)
