from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,time,uuid
R=Path('/mnt/e/codex-build/RH-Zero-Proportion-Formalization')
D=R/'tmp/memory-optimization-20261010/finite'
H=Path('/mnt/e/codex-build/RH-Weil/tmp/linux-memory-runtime-20261010/evidence-v3/handoff-v3.json')
BASE=Path('/tmp/rh-proportion-memory-20261010')
F=BASE/'finite-micro';SRC=F/'source';LIB=F/'lib';REL=Path('tmp/memory-optimization-20261010/finite')
STEMS=['PivotGeneric','baseline','chosen','PacketGeneric','packetBaseline','packetCached','chosen49','baseline49']
PARTS=['.olean','.olean.private','.olean.server','.ir','.ir.sig']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def roots(step):
 if step in ['chosen49','baseline49']:return json.loads((D/'family-prepared.json').read_text())['families'][step]['roots']
 if step=='PivotGeneric':return ['RHWeil.RecordSubmission.FiniteCertificateData.'+n for n in ['chosen_bound_le','chosen_lower_le','integerCheck_of_chosen']]
 if step=='PacketGeneric':return ['PacketCacheProbe.basicLower_eq_packet']
 if step=='packetBaseline':return ['PacketCacheProbe.sample_'+str(i)for i in [64,65,1198]]
 if step=='packetCached':return ['PacketCacheProbe.packetEq_'+str(i)for i in [64,65,1198]]+['PacketCacheProbe.sample_'+str(i)for i in [64,65,1198]]
 return ['FinitePivotProbe.sample_'+str(i)for i in [35,54,1199]]
def prepare():
 h=json.loads(H.read_text());assert h['harness_version']==3;assert h['harness_sha256']=='e192787f00ea5ceb0c77a06969bb832136b751337a475dd0e63619743f4d24ec'
 assert sha(h['harness_linux'])==h['harness_sha256'];assert sha(h['lean'])==h['lean_sha256']
 review=json.loads((D/'source-proof-review.json').read_text());bindings=json.loads((D/'legacy-import-bindings.json').read_text())
 copied={};guards={str(H):sha(H),str(D/'source-proof-review.json'):sha(D/'source-proof-review.json'),str(D/'legacy-import-bindings.json'):sha(D/'legacy-import-bindings.json'),str(h['harness_linux']):sha(h['harness_linux']),str(h['native_verification']):sha(h['native_verification']),str(h['ir_signature_verification']):sha(h['ir_signature_verification'])}
 for stem in STEMS:
  original=D/(stem+'.lean');assert sha(original)==review['source_sha256'][stem+'.lean']
  target=SRC/REL/original.name;target.parent.mkdir(parents=True,exist_ok=True)
  if target.exists():assert sha(target)==sha(original),'Never silently replace an already prepared source'
  else:shutil.copy2(original,target)
  copied[str(target)]=sha(target);guards[str(original)]=sha(original);guards[str(target)]=sha(target)
 for stem in ['tmp/two-edge-high/twoedge','tmp/floyd_two_edge/FloydTwoEdge']:
  for part in PARTS:
   original=R/(stem+part)
   if original.exists():
    if stem+part in bindings['bindings']:assert sha(original)==bindings['bindings'][stem+part]['sha256']
    target=LIB/(stem+part);target.parent.mkdir(parents=True,exist_ok=True)
    if target.exists():assert sha(target)==sha(original)
    else:shutil.copy2(original,target)
    copied[str(target)]=sha(target);guards[str(original)]=sha(original);guards[str(target)]=sha(target)
 for name,meta in bindings['bindings'].items():
  assert sha(R/name)==meta['sha256'];guards[str(R/name)]=meta['sha256']
  if name.startswith('.lake/'):
   native=Path(h['native_root'])/name;assert sha(native)==meta['sha256'];guards[str(native)]=meta['sha256']
 for folder in [LIB,LIB/REL]:folder.mkdir(parents=True,exist_ok=True)
 for folder in [LIB,*[p for p in LIB.rglob('*')if p.is_dir()]]:os.chown(folder,1000,1000);os.chmod(folder,0o755)
 record={'status':'Exact source/legacy artifact routing prepared, no proof claim','lean_path':str(LIB)+':'+h['lean_path'],'copied':copied,'fixed_input_guards':guards,'legacy_absent_companions':{stem:[p for p in PARTS if not (R/(stem+p)).exists()]for stem in ['tmp/two-edge-high/twoedge','tmp/floyd_two_edge/FloydTwoEdge']},'handoff_sha256':sha(H),'harness_sha256':sha(h['harness_linux'])}
 (F/'routing.json').write_text(json.dumps(record,indent=2)+'\n');(D/'linux-routing.json').write_text(json.dumps(record,indent=2)+'\n')
 return h,record

def run(step,audit):
 h,routing=prepare();base_step=step.removesuffix('Repeat');assert base_step in STEMS
 original=SRC/REL/(step+'.lean')
 if base_step!=step:
  base_source=SRC/REL/(base_step+'.lean')
  if original.exists():assert sha(original)==sha(base_source)
  else:shutil.copy2(base_source,original)
 module='«tmp».«memory-optimization-20261010».finite.«'+step+'»'
 deps={'baseline':['PivotGeneric'],'chosen':['PivotGeneric'],'packetBaseline':['PacketGeneric'],'packetCached':['PacketGeneric'],'chosen49':['PivotGeneric'],'baseline49':['PivotGeneric']}.get(base_step,[])
 for dep in deps:assert (LIB/REL/(dep+'.olean')).exists(), 'Compile generic before sample'
 if audit:assert (LIB/REL/(step+'.olean')).exists(), 'Compile module before its fresh audit'
 source=original
 if audit:
  source=SRC/REL/(step+'LinuxAudit.lean')
  text='import '+module+'\nset_option Elab.async false\nset_option pp.universes true\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n'for n in roots(step))
  if source.exists():assert source.read_text()==text
  else:source.write_text(text)
 rid='finite-'+step.lower()+('-audit-' if audit else '-compile-')+time.strftime('%Y%m%d-%H%M%S',time.gmtime())+'-'+uuid.uuid4().hex[:6]
 command=[h['lean'],'-j1','--tstack=32768','-R',str(SRC),'-DstderrAsMessages=false']
 if not audit:command+=['-o',str(LIB/REL/(step+'.olean'))]
 command+=[str(source)]
 guards={**routing['fixed_input_guards'],str(source):sha(source),str(F/'routing.json'):sha(F/'routing.json'),str(Path(__file__)):sha(Path(__file__)),str(D/'family-prepared.json'):sha(D/'family-prepared.json')}
 for path in sorted(LIB.rglob('*')):
  if path.is_file()and path.name.endswith(tuple(PARTS)):guards[str(path)]=sha(path)
 argv=['python3',h['harness_linux'],'--run-id',rid,'--timeout','180','--cwd',str(SRC),'--lean-path',routing['lean_path'],'--evict-root',str(LIB)]
 for name in guards:argv+=['--bind',name]
 argv+=['--',*command]
 print(json.dumps({'LAUNCH':rid,'step':step,'audit':audit,'source_sha256':sha(source),'fresh_prefix':str(LIB)},indent=2),flush=True)
 started=time.monotonic()
 with (D/(rid+'-harness.stdout.log')).open('w')as controllerlog:
  proc=subprocess.Popen(argv,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
  for line in proc.stdout:
   controllerlog.write(line);controllerlog.flush()
   try:
    item=json.loads(line);keys=['status','file_count','after_resident_page_bytes','all_selected_pages_nonresident','elapsed_seconds','started_pid','run_id','running','seconds','memory_current_bytes','actual_exit_code','proof_succeeded','resource_fit','oom_kill_count','cgroup_peak_bytes','sampled_tree_peak_pss_bytes','inputs_unchanged']
    print(json.dumps({k:item[k]for k in keys if k in item}),flush=True)
   except (json.JSONDecodeError,TypeError):print(line.rstrip()[:1000],flush=True)
  proc.wait()
 total=time.monotonic()-started
 runfolder=BASE/'resource-runs'/rid
 if not (runfolder/'result.json').exists():
  fail={'status':'Harness preparation refused/failed; no proof result','harness_exit':proc.returncode,'launcher_wall_seconds':total,'run_id':rid,'command':argv}
  (D/(rid+'-launcher.json')).write_text(json.dumps(fail,indent=2)+'\n');print(json.dumps(fail,indent=2),flush=True);raise SystemExit(1)
 result=json.loads((runfolder/'result.json').read_text());log=(runfolder/'process.log').read_text(errors='replace')
 starts={n:int(v)for n,v in re.findall(r'START_(\w+) (\d+)',log)};ends={n:int(v)for n,v in re.findall(r'END_(\w+) (\d+)',log)}
 phases={n:(ends[n]-v)/1000 for n,v in starts.items()if n in ends};observed={}
 if audit:
  for name in roots(step):
   m=re.search("'"+re.escape(name)+r"' depends on axioms:\s*\[([^]]*)\]",log)
   if m:observed[name]=[re.sub(r'\.\{[^}]+\}$','',a.strip())for a in m.group(1).split(',')if a.strip()]
   elif "'"+name+"' does not depend on any axioms"in log:observed[name]=[]
 passed=result['proof_succeeded']and(not audit or(len(observed)==len(roots(step))and all(set(v)<={'propext','Classical.choice','Quot.sound'}for v in observed.values())))
 out=LIB/REL/(step+'.olean')
 review={'step':step,'fresh_audit':audit,'run_id':rid,'harness_exit':proc.returncode,'launcher_wall_seconds':round(total,3),'proof_seconds':result['elapsed_seconds'],'resource_fit':result['resource_fit'],'kernel_process_succeeded':result['proof_succeeded'],'strict_selected_axioms_passed':passed if audit else None,'axioms':observed,'phases_seconds':phases,'source_sha256':sha(source),'artifact_sha256':sha(out)if not audit and out.exists()and result['proof_succeeded']else None,'cold_preparation_seconds':result['scoped_eviction'].get('elapsed_seconds'),'cgroup_peak_bytes':result['cgroup_peak_bytes'],'sampled_peak_pss_bytes':result['sampled_tree_peak_pss_bytes'],'harness_sha256':sha(h['harness_linux']),'inputs_unchanged':result['inputs_unchanged'],'scope':'Fresh ordinary kernel process only; scoped cold imported-artifact cgroup component test, no exact official VM/whole-family acceptance. No independent Nano yet.'}
 for name in ['result.json','process.log','scoped-cache-eviction.json']:shutil.copy2(runfolder/name,D/(rid+'-'+name))
 (D/(rid+'-review.json')).write_text(json.dumps(review,indent=2)+'\n');(D/(step+('-linux-audit-latest.json'if audit else'-linux-compile-latest.json'))).write_text(json.dumps(review,indent=2)+'\n')
 print(json.dumps(review,indent=2),flush=True)
 if not passed:print(log[-18000:],flush=True);raise SystemExit(1)
 if not result['resource_fit']:raise SystemExit(2)

p=argparse.ArgumentParser();p.add_argument('--prepare',action='store_true');p.add_argument('--step',choices=STEMS+['baselineRepeat','chosenRepeat']);p.add_argument('--audit',action='store_true');a=p.parse_args()
if a.prepare:
 h,r=prepare();print(json.dumps({'prepared':True,'copied_files':len(r['copied']),'lean_path':r['lean_path'],'no_proof_executed':True},indent=2))
else:assert a.step;run(a.step,a.audit)
