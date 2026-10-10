from pathlib import Path
import hashlib,json,re,subprocess,time
root=Path('E:/codex-build/RH-Weil')
formal=Path('E:/codex-build/RH-Zero-Proportion-Formalization')
h=json.loads((formal/'verification/linux-memory-time-20261010/am/environment/handoff-v3.json').read_text(encoding='utf8'))
roots=['catalogValue_lt','catalogPack_eq','catalogTVal','oldTVal_reanchor_scaled','direct_reanchor_scaled']
audit=root/'tmp/ninth-span-points-fresh-audit.lean'
audit.write_text('import RecordProportion.NinthSpanPoints\n'+''.join('#print axioms RHWeil.RecordSubmission.NinthSpanPoints.'+name+'\n' for name in roots),encoding='utf8',newline='\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
source=formal/'RecordProportion/NinthSpanPoints.lean'
olean=formal/'.lake/build/lib/lean/RecordProportion/NinthSpanPoints.olean'
pins={'source':sha(source),'olean':sha(olean),'audit':sha(audit)}
cmd=['wsl','-d','Ubuntu','--exec','env','LEAN_PATH=/mnt/e/codex-build/RH-Zero-Proportion-Formalization/.lake/build/lib/lean:'+h['lean_path'],h['lean'],'-j1','--tstack=32768','/mnt/e/codex-build/RH-Weil/tmp/ninth-span-points-fresh-audit.lean']
t=time.monotonic();p=subprocess.run(cmd,capture_output=True,text=True,encoding='utf8',errors='replace')
text=p.stdout+p.stderr
log=root/'tmp/ninth-span-points-fresh-audit.log';log.write_text(text,encoding='utf8',newline='\n')
entries=re.findall(r"'RHWeil\.RecordSubmission\.NinthSpanPoints\.([^']+)' depends on axioms: \[([^]]*)\]",text,re.S)
parsed={name:[v.strip() for v in ax.split(',') if v.strip()] for name,ax in entries}
ok=p.returncode==0 and set(parsed)==set(roots) and all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in parsed.values())
assert pins=={'source':sha(source),'olean':sha(olean),'audit':sha(audit)}
result={'passed':ok,'exit_code':p.returncode,'elapsed_seconds':time.monotonic()-t,'pins':pins,'axioms':parsed,'log_sha256':sha(log),'command':cmd}
(root/'tmp/ninth-span-points-fresh-audit.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8',newline='\n')
print(json.dumps(result,indent=2));print(text)
raise SystemExit(0 if ok else 1)
