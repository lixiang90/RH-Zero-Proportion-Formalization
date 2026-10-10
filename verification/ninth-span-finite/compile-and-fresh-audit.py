from pathlib import Path
import hashlib,json,subprocess,time,sys
sys.stdout.reconfigure(encoding='utf8')
formal=Path('E:/codex-build/RH-Zero-Proportion-Formalization')
out=Path(__file__).resolve().parent/'lean-full';out.mkdir(exist_ok=True)
h=json.loads((formal/'verification/linux-memory-time-20261010/am/environment/handoff-v3.json').read_text(encoding='utf8'))
lr='/mnt/e/codex-build/RH-Zero-Proportion-Formalization'
lp=lr+'/.lake/build/lib/lean:'+h['lean_path']
compiler=h['lean']
assert subprocess.check_output(['wsl','-d','Ubuntu','--exec','sha256sum',compiler],text=True).split()[0]==h['lean_sha256']
results=[]
sources=[('compile',formal/'RecordProportion/NinthSpanFinite.lean',lr+'/RecordProportion/NinthSpanFinite.lean')]
audit=out/'NinthSpanFiniteFreshAudit.lean'
audit.write_text('''import RecordProportion.NinthSpanFinite
#print axioms RHWeil.RecordSubmission.NinthSpanFiniteData.allBranchGuards
#print axioms RHWeil.RecordSubmission.NinthSpanFiniteData.allBranchNumeric
#print axioms RHWeil.RecordSubmission.NinthSpanFiniteData.allPatchShapes
#print axioms RHWeil.RecordSubmission.NinthSpanFiniteData.allRepRoutes
#print axioms RHWeil.RecordSubmission.NinthSpanFiniteData.allOldOrPatch
#print axioms RHWeil.RecordSubmission.NinthSpanFinite.branchClosure_real
#print axioms RHWeil.RecordSubmission.NinthSpanFinite.patch_real_bound
#print axioms RHWeil.RecordSubmission.NinthSpanFinite.oldPath_box
#print axioms RHWeil.RecordSubmission.NinthSpanFinite.path_representative_bound
#print axioms RHWeil.RecordSubmission.NinthSpanFinite.low_pair_bound
''',encoding='utf8',newline='\n')
sources.append(('fresh-audit',audit,'/mnt/e/codex-build/RH-Weil/tmp/research-resume-20261010/proportion/lean-full/NinthSpanFiniteFreshAudit.lean'))
for phase,source,lss in sources:
 sha=hashlib.sha256(source.read_bytes()).hexdigest()
 cmd=['wsl','-d','Ubuntu','--exec','env','LEAN_PATH='+lp,compiler,'-j1','--tstack=32768',
 '-DrelaxedAutoImplicit=false','-R',lr]
 if phase=='compile':cmd+=['-o',lr+'/.lake/build/lib/lean/RecordProportion/NinthSpanFinite.olean']
 cmd+=[lss]
 log=out/('finite-'+phase+'.log');start=time.monotonic()
 with log.open('w',encoding='utf8',newline='\n') as f:
  p=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,text=True,encoding='utf8',errors='replace')
 result={'phase':phase,'exit_code':p.returncode,'elapsed_seconds':time.monotonic()-start,'source_sha256':sha,
 'source_unchanged':hashlib.sha256(source.read_bytes()).hexdigest()==sha,'compiler_sha256':h['lean_sha256'],
 'command':cmd,'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()}
 txt=log.read_text(encoding='utf8')
 result['forbidden_axiom_text_seen']=any(w in txt for w in ['sorryAx','Lean.ofReduceBool','admit'])
 results.append(result)
 (out/'finite-audit.json').write_text(json.dumps(results,indent=2)+'\n',encoding='utf8',newline='\n')
 print(json.dumps(result,indent=2),flush=True);print(txt,flush=True)
 if p.returncode or result['forbidden_axiom_text_seen']:raise SystemExit(p.returncode or 1)
