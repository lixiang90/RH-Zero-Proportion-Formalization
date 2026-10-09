from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, sys

SCRATCH = Path(r'E:\codex-build\RH-Zero-Proportion-Formalization\tmp\memory-optimization-20261010\am')
HANDOFF = Path(r'E:\codex-build\RH-Weil\tmp\linux-memory-runtime-20261010\evidence-v3\handoff-v3.json')
NATIVE = '/tmp/rh-proportion-memory-20261010/am-isolated-v3-20261010-r2'
VARIANTS = {
 'bounded8': ('AMBoundedAsync8.lean', 1503275, 'de9440bc49f7d7780ad7a6210d51f8cd0813948315d41b1b49aa8e3a48f3d18e'),
 'syncalias8': ('AMSyncAlias8.lean', 1501640, '40f0fb440a3673aa36ba81361e1db7ef31471851bae63b82d77f434605a769f5'),
}
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
def linux(p):
 p=Path(p).resolve(); return '/mnt/'+p.drive[0].lower()+p.as_posix()[2:]
def main():
 assert not sys.flags.optimize, 'Do not disable assertion gates with -O'
 handoff=json.loads(HANDOFF.read_text(encoding='utf-8'))
 assert handoff['harness_version']==3
 assert sha(handoff['harness_windows'])==handoff['harness_sha256']=='e192787f00ea5ceb0c77a06969bb832136b751337a475dd0e63619743f4d24ec'
 prepared=SCRATCH/'native-am-v3-prepared-r2'; prepared.mkdir(exist_ok=False)
 roots=[]
 for name in ['FreshMainRoots.lean','FreshAliasRoots.lean']:
  text=(SCRATCH/name).read_text(encoding='utf-8')
  assert text.splitlines()[0]=='import RecordProportion.ImportedAM'
  roots += re.findall(r'^#print axioms (\S+)\s*$', text, re.M)
 assert len(roots)==len(set(roots))==20
 audit='import RecordProportion.ImportedAM\n'+'\n'.join('#print axioms '+r for r in roots)+'\n'
 (prepared/'FreshAllRoots.lean').write_text(audit,encoding='utf-8',newline='\n')
 runner=SCRATCH/'run_am_native_v3_trial.py'; assert runner.exists()
 evidence=['candidate-batch8.json','command-boundaries-check.json','command-boundaries.tsv','ParseBoundariesLinux.lean','generate_bounded_am.py']
 expected_evidence={x:sha(SCRATCH/x) for x in evidence}
 config={
  'status':'PREPARED_NOT_CHECKED', 'prepare_only':True,
  'native_root':NATIVE, 'handoff':linux(HANDOFF), 'handoff_sha256':sha(HANDOFF),
  'harness':handoff['harness_linux'],'harness_sha256':handoff['harness_sha256'],
  'lean':handoff['lean'],'lean_sha256':handoff['lean_sha256'],
  'lean_path_baseline':handoff['lean_path'],
  'native_verification':handoff['native_verification'],
  'ir_signature_verification':handoff['ir_signature_verification'],
  'runner':NATIVE+'/run_am_native_v3_trial.py','runner_sha256':sha(runner),
  'runner_windows':linux(runner), 'prepare_driver':linux(Path(__file__)), 'prepare_driver_sha256':sha(__file__),
  'roots':roots,'allowed_axioms':['propext','Classical.choice','Quot.sound'],
  'workers':4,'tstack':32768,'compile_timeout_seconds':1200,'deps_timeout_seconds':180,'audit_timeout_seconds':180,
  'resource_memory_bytes':8589934592,'scope':'Isolated Linux cgroup component trial, not a whole official VM or website acceptance.',
  'evidence_bindings':[{ 'path':linux(SCRATCH/x),'sha256':expected_evidence[x]} for x in evidence],
  'variants':{}, 'all_overlay_roots':[]
 }
 copies=[{'src':linux(runner),'dst':NATIVE+'/run_am_native_v3_trial.py'}]
 for variant,(source_name,size,digest) in VARIANTS.items():
  source=SCRATCH/source_name; assert source.stat().st_size==size and sha(source)==digest
  imports=re.findall(r'^import (.+)$',source.read_text(encoding='utf-8'),re.M)
  assert all('RecordProportion.' not in i for i in imports)
  vr=NATIVE+'/'+variant; sr=vr+'/source'; lr=vr+'/lib'; ar=vr+'/audit-lib'
  source_native=sr+'/RecordProportion/ImportedAM.lean'; audit_native=sr+'/FreshAllRoots.lean'
  config['variants'][variant]={
   'source_root':sr,'lib_root':lr,'audit_lib_root':ar,'source':source_native,
   'source_bytes':size,'source_sha256':digest,'audit_source':audit_native,
   'audit_sha256':sha(prepared/'FreshAllRoots.lean'),
   'artifact':lr+'/RecordProportion/ImportedAM.olean', 'imports':imports,
   'compile_run_id':'am-'+variant+'-v3-compile-20261010',
   'deps_run_id':'am-'+variant+'-v3-deps-20261010',
   'audit_run_id':'am-'+variant+'-v3-audit-20261010',
   'compiled':False,'fresh_audit_checked':False,
  }
  config['all_overlay_roots'] += [lr,ar]
  copies += [{'src':linux(source),'dst':source_native},{'src':linux(prepared/'FreshAllRoots.lean'),'dst':audit_native}]
 (prepared/'config.json').write_text(json.dumps(config,indent=2)+'\n',encoding='utf-8')
 copies.append({'src':linux(prepared/'config.json'),'dst':NATIVE+'/config.json'})
 payload={'root':NATIVE,'copies':copies,'dirs':config['all_overlay_roots']+[v['source_root']+'/RecordProportion' for v in config['variants'].values()]+[v['lib_root']+'/RecordProportion' for v in config['variants'].values()]+[NATIVE+'/evidence']}
 preparation_code='''from pathlib import Path
import hashlib,json,os,shutil,sys
cfg=json.loads(sys.argv[1]); root=Path(cfg["root"]); base=Path("/tmp/rh-proportion-memory-20261010").resolve()
assert root.is_absolute() and root.resolve().is_relative_to(base) and root.resolve()!=base
root.mkdir(exist_ok=False)
for directory in cfg["dirs"]:
 p=Path(directory);assert p.resolve().is_relative_to(root.resolve());p.mkdir(parents=True,exist_ok=True)
for item in cfg["copies"]:
 src=item["src"];dst=item["dst"];target=Path(dst);assert target.resolve().is_relative_to(root.resolve());target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,target)
for p in [root,*root.rglob("*")]:os.chown(p,1000,1000)
manifest={str(p):{"bytes":p.stat().st_size,"sha256":hashlib.sha256(p.read_bytes()).hexdigest()} for p in root.rglob("*") if p.is_file()}
print(json.dumps({"status":"PREPARED_NOT_CHECKED","no_lean_invoked":True,"no_eviction_invoked":True,"files":manifest},indent=2))'''
 result=subprocess.run(['wsl','-d','Ubuntu','-u','root','--','python3','-c',preparation_code,json.dumps(payload)],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 (prepared/'prepare-native.stdout.log').write_bytes(result.stdout); (prepared/'prepare-native.stderr.log').write_bytes(result.stderr)
 assert result.returncode==0,result.stderr.decode(errors='replace')
 actual=json.loads(result.stdout)
 for variant,item in config['variants'].items():
  assert actual['files'][item['source']]['sha256']==item['source_sha256']
  assert actual['files'][item['source']]['bytes']==item['source_bytes']
  assert actual['files'][item['audit_source']]['sha256']==item['audit_sha256']
 record={'status':'PREPARED_NOT_CHECKED','native_root':NATIVE,'configuration':str(prepared/'config.json'),
         'config_sha256':sha(prepared/'config.json'),'prepare_driver_sha256':sha(__file__),
         'runner_sha256':sha(runner),'actual_native_copy':actual,
         'compile_executed':False,'eviction_executed':False,'proof_or_resource_fit_claim':False}
 (prepared/'prepared-native-trees.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
 print(json.dumps(record,indent=2))
if __name__=='__main__':main()
