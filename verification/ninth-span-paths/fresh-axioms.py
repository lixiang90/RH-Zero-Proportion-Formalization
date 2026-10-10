from pathlib import Path
import hashlib,json,re,subprocess,time

TMP=Path('E:/codex-build/RH-Weil/tmp')
ROOT=Path('E:/codex-build/RH-Zero-Proportion-Formalization')
handoff=json.loads((ROOT/'verification/linux-memory-time-20261010/am/environment/handoff-v3.json').read_text(encoding='utf8'))
roots=['cost_real_bound','check_real_bound']
audit=TMP/'ninth-span-path-fresh-audit.lean'
audit.write_text('import RecordProportion.NinthSpanPathSoundness\n'+''.join(
    '#print axioms RHWeil.RecordSubmission.NinthSpanPaths.'+name+'\n' for name in roots),encoding='utf8',newline='\n')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
source=ROOT/'RecordProportion/NinthSpanPathSoundness.lean'
olean=ROOT/'.lake/build/lib/lean/RecordProportion/NinthSpanPathSoundness.olean'
pins={'source':sha(source),'olean':sha(olean),'audit':sha(audit)}
cmd=['wsl','-d','Ubuntu','--exec','env',
    'LEAN_PATH=/mnt/e/codex-build/RH-Zero-Proportion-Formalization/.lake/build/lib/lean:'+handoff['lean_path'],
    handoff['lean'],'-j1','--tstack=32768','/mnt/e/codex-build/RH-Weil/tmp/ninth-span-path-fresh-audit.lean']
t=time.monotonic();res=subprocess.run(cmd,capture_output=True,text=True,encoding='utf8',errors='replace')
output=res.stdout+res.stderr
log=TMP/'ninth-span-path-fresh-audit.txt';log.write_text(output,encoding='utf8',newline='\n')
entries=re.findall(r"'RHWeil\.RecordSubmission\.NinthSpanPaths\.([^']+)' depends on axioms: \[([^]]*)\]",output,re.S)
parsed={name:[v.strip() for v in ax.split(',') if v.strip()] for name,ax in entries}
ok=res.returncode==0 and set(parsed)==set(roots) and all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in parsed.values())
assert pins=={'source':sha(source),'olean':sha(olean),'audit':sha(audit)}
receipt={'status':'PASS' if ok else 'FAILED','exit_code':res.returncode,'wall_seconds':time.monotonic()-t,
    'pins':pins,'axioms':parsed,'log_sha256':sha(log),'command':cmd}
(TMP/'ninth-span-path-fresh-audit.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8',newline='\n')
print(json.dumps(receipt,indent=2));print(output)
raise SystemExit(0 if ok else 1)
