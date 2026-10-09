"""Windows-only prospective AM evidence archive; never executes a compiler/cache action."""
from pathlib import Path
from datetime import datetime, timezone, timedelta
import gzip, hashlib, json, shutil, sys

REPO=Path(r'E:\codex-build\RH-Zero-Proportion-Formalization')
AM=REPO/'tmp/memory-optimization-20261010/am'
PREP=AM/'native-am-v3-prepared-r2'
FINITE=REPO/'tmp/memory-optimization-20261010/finite/publication-proposal-20261010'
ENV=Path(r'E:\codex-build\RH-Weil\tmp\linux-memory-runtime-20261010')
OUT=REPO/'tmp/am-publication-evidence-20261010'
CHUNK=1024*1024

def digest(path):
 h=hashlib.sha256()
 with Path(path).open('rb') as f:
  for b in iter(lambda:f.read(CHUNK),b''):h.update(b)
 return h.hexdigest()
def plain_hash(data):return hashlib.sha256(data).hexdigest()
def write_json(path,value):path=Path(path);path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(value,indent=2,ensure_ascii=False)+'\n',encoding='utf-8',newline='\n')

def main():
 assert not sys.flags.optimize,'Do not disable assertions with -O'
 assert not OUT.exists(),'Publication archive must be fresh; no overwrite/delete'
 assert OUT.resolve().is_relative_to((REPO/'tmp').resolve())
 assert PREP.is_dir() and FINITE.is_dir()
 compiled={v:json.loads((PREP/(v+'-v3-native-actual')/'compile-stage.json').read_text()) for v in ['bounded8','syncalias8']}
 assert compiled['bounded8']['source_sha256']=='de9440bc49f7d7780ad7a6210d51f8cd0813948315d41b1b49aa8e3a48f3d18e'
 assert compiled['syncalias8']['source_sha256']=='40f0fb440a3673aa36ba81361e1db7ef31471851bae63b82d77f434605a769f5'
 assert all(x['actual']['actual_exit_code']==0 and x['actual_component_resource_fit'] for x in compiled.values())
 assert compiled['bounded8']['actual']['configuration']==compiled['syncalias8']['actual']['configuration']
 OUT.mkdir()
 manifest={'status':'PROSPECTIVE_AM_PUBLICATION_EVIDENCE_ONLY','packet_id':'am-publication-evidence-20261010','gzip_policy':{'mtime':0,'filename_header':'','compression_level':6,'decompressed_bytes_and_sha256_verified':True},'files':[],'external_deduplicated_references':[],'no_compiler_or_cache_or_linux_invoked':True,'no_runtime_or_compiled_binaries_included':True,'public_repository_files_edited':False}
 def put(source,relative,compress=False,role='evidence'):
  source=Path(source);assert source.is_file() and source.suffix in ['.json','.log','.lean','.py','.txt','.tsv','.diff','.md']
  target=OUT/relative;assert target.resolve().is_relative_to(OUT.resolve());assert not target.exists()
  target.parent.mkdir(parents=True,exist_ok=True);before=digest(source);size=source.stat().st_size
  if compress:
   with source.open('rb') as fi,target.open('xb') as fo,gzip.GzipFile(filename='',mode='wb',compresslevel=6,fileobj=fo,mtime=0) as gz:
    for b in iter(lambda:fi.read(CHUNK),b''):gz.write(b)
   h=hashlib.sha256();n=0
   with gzip.open(target,'rb') as f:
    for b in iter(lambda:f.read(CHUNK),b''):h.update(b);n+=len(b)
   assert n==size and h.hexdigest()==before
   with target.open('rb') as f:header=f.read(10)
   assert header[4:8]==b'\0\0\0\0' and header[3]&8==0
  else:shutil.copyfile(source,target)
  assert digest(source)==before,'Source changed during file-only packaging'
  entry={'path':relative,'role':role,'source_origin':str(source),'archive_bytes':target.stat().st_size,'archive_sha256':digest(target),'decompressed_bytes':size,'decompressed_sha256':before,'encoding':'gzip' if compress else 'identity'}
  manifest['files'].append(entry);return entry
 def generated(relative,value,role='metadata'):
  p=OUT/relative;assert not p.exists();write_json(p,value);raw=p.read_bytes();manifest['files'].append({'path':relative,'role':role,'archive_bytes':len(raw),'archive_sha256':plain_hash(raw),'decompressed_bytes':len(raw),'decompressed_sha256':plain_hash(raw),'encoding':'identity','source_origin':'Generated solely from hash-bound archived Windows text records'})

 put(PREP/'same-linux-am-controlled-comparison.json','comparison.json',role='compact same-Linux paired component comparison')
 for variant in ['bounded8','syncalias8']:
  src=PREP/(variant+'-v3-native-actual')
  put(src/'checked-summary.json','summaries/'+variant+'.json',role='compact completed component validation')
  for phase in ['compile','deps','audit']:
   stem='runs/'+variant+'/'+phase+'/'
   for raw,new in [('process.log','process.log.gz'),('result.json','result.json.gz'),('scoped-cache-eviction.json','scoped-cache-eviction.json.gz'),('harness.stdout.log','harness.stdout.log.gz'),('harness.stderr.log','harness.stderr.log.gz')]:
    put(src/(phase+'-'+raw),stem+new,True,role='exact raw '+phase+' '+raw)
   put(PREP/(variant+'-'+phase+'-supervisor-result.json'),stem+'supervisor-result.json',role='wall-clock launch/finish and driver output hashes')
   a=json.loads((src/(phase+'-result.json')).read_text());assert a['inputs_unchanged'] and a['actual_exit_code']==0 and a['scoped_eviction']['all_selected_pages_nonresident']
  roots=json.loads((src/'audit-stage.json').read_text())['axiom_gate'];assert roots['pass'] and len(roots['roots'])==20
  assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in roots['roots'])
 for name in ['barrier-profile.json','barrier-profile-stdio-correction.json']:
  put(PREP/'bounded8-v3-native-actual'/name,'analysis/'+name,role='final monotonic proof-group timing; live stdout is lower bound')
 put(AM/'am-peak-attribution-file-only.json','analysis/peak-attribution.json',role='coarse archived-sample inference, plus-or-minus1second and async8 caveats')
 for name in ['config.json','prepared-native-trees.json','static-driver-review.json','FreshAllRoots.lean']:
  put(PREP/name,'provenance/'+name,role='exact prepared provenance, prior pending labels are historical')
 for name in ['run_am_native_v3_trial.py','prepare_am_native_v3.py','generate_bounded_am.py','review_bounded_am_static.py']:
  put(AM/name,'provenance/'+name,role='source-only archived driver/generator, not executed during packaging')
 put(AM/'bounded-am-static-integration-review.json','source-review/bounded-am-static-integration-review.json.gz',True,role='historical source-only review, superseded by actual component checks')
 put(AM/'AMSyncAlias8.lean','source-review/AMSyncAlias8.lean.gz',True,role='exact synchronous control review source')

 review=json.loads((FINITE/'review-components.json').read_text());ref=review['variants']['bounded8']['RecordProportion/ImportedAM.lean'];external=FINITE/ref['archive'];assert digest(external)==ref['gzip_sha256']
 raw=gzip.decompress(external.read_bytes());assert plain_hash(raw)==compiled['bounded8']['source_sha256'] and len(raw)==1503275
 assert digest(AM/'AMBoundedAsync8.lean')==plain_hash(raw)
 manifest['external_deduplicated_references'].append({'packet_id':'finite-publication-proposal-20261010','logical_source':'RecordProportion/ImportedAM.lean','source_origin':str(external),'archive_relative_path_in_external_packet':ref['archive'],**{k:ref[k] for k in ['gzip_sha256','gzip_bytes','decompressed_sha256','decompressed_bytes']},'reason':'Exact bounded8 source already present; do not publish a second identical gzip.'})
 for name in ['candidate-batch8.json','command-boundaries-check.json','command-boundaries.tsv','ParseBoundariesLinux.lean']:
  external=FINITE/'recipe'/name;assert digest(external)==digest(AM/name)
  manifest['external_deduplicated_references'].append({'packet_id':'finite-publication-proposal-20261010','archive_relative_path_in_external_packet':'recipe/'+name,'source_origin':str(external),'decompressed_sha256':digest(external),'decompressed_bytes':external.stat().st_size,'reason':'Exact parser/insertion provenance already present.'})

 env_files=[(ENV/'evidence-v3/handoff-v3.json','environment/handoff-v3.json',False),
  (ENV/'evidence-v3/drivers/linux_cgroup_resource_harness_v3_20261010.py','environment/linux_cgroup_resource_harness_v3_20261010.py',False),
  (ENV/'evidence/drivers/setup_linux_memory_runtime_20261010.py','environment/setup_linux_memory_runtime_20261010.py',False),
  (ENV/'evidence/metadata/native-cache-verification.json','environment/native-cache-verification.json',False),
  (ENV/'evidence/metadata/native-ir-signature-verification.json','environment/native-ir-signature-verification.json',False),
  (ENV/'evidence/metadata/pinned-windows-dependency-artifacts.json','environment/pinned-windows-dependency-artifacts.json.gz',True),
  (ENV/'evidence/metadata/pinned-ir-signature-delta.json','environment/pinned-ir-signature-delta.json.gz',True),
  (ENV/'evidence/metadata/download-ranges-result.json','environment/download-ranges-result.json',False),
  (ENV/'evidence-v3/cold-v3-summary.json','environment/cold-v3-import-summary.json',False)]
 for source,target,compressed in env_files:put(source,target,compressed,role='exact archived environment text metadata/source, no runtime/cache bytes read')
 harness_sha=digest(ENV/'evidence-v3/drivers/linux_cgroup_resource_harness_v3_20261010.py');assert harness_sha=='e192787f00ea5ceb0c77a06969bb832136b751337a475dd0e63619743f4d24ec'
 for variant,stage in compiled.items():
  before=stage['actual']['inputs_before']
  for key,name in [('native-cache-verification.json','native-cache-verification.json'),('native-ir-signature-verification.json','native-ir-signature-verification.json')]:
   matches=[v for k,v in before.items() if k.endswith('/'+key)];assert matches==[digest(ENV/'evidence/metadata'/name)]
  assert before['/mnt/e/codex-build/RH-Weil/tmp/linux_cgroup_resource_harness_v3_20261010.py']==harness_sha

 localtz=timezone(timedelta(hours=8));timeline={}
 for variant in ['bounded8','syncalias8']:
  timeline[variant]={}
  for phase in ['compile','deps','audit']:
   s=json.loads((PREP/(variant+'-'+phase+'-supervisor-result.json')).read_text());timeline[variant][phase]={'start_unix':s['start_time_unix'],'finish_unix':s['finish_time_unix'],'start_China':datetime.fromtimestamp(s['start_time_unix'],localtz).isoformat(),'finish_China':datetime.fromtimestamp(s['finish_time_unix'],localtz).isoformat(),'supervisor_wall_seconds':s['finish_time_unix']-s['start_time_unix']}
 generated('validation-phase-gap.json',{'status':'DISCLOSED_PHASE_GAP','timeline':timeline,'session_resumed_China_approximate':'2026-10-10T06:12:00+08:00','approximate_resume_time_provenance':'Trusted coordinating root task message, not a measured compiler timestamp','both_compiles_completed_before_reported_host_runtime_restart':True,'control_compilation_finished_China':timeline['syncalias8']['compile']['finish_China'],'control_deps_started_China':timeline['syncalias8']['deps']['start_China'],'control_audit_finished_China':timeline['syncalias8']['audit']['finish_China'],'control_was_not_recompiled':True,'source_and_fresh_olean_bytes_unchanged_across_gap':True,'source_sha256':compiled['syncalias8']['source_sha256'],'artifact_inventory':compiled['syncalias8']['artifact_inventory'],'interpretation':'The gap separates control compilation from subsequent fresh import/axiom checks. It does not alter recorded completed paired compile timing, CPU or memory, but must be disclosed. After restart, exact artifacts were bound and cold fresh deps/20-root audit passed.'})
 generated('packet-scope.json',{'status':'PROSPECTIVE_PUBLICATION_ONLY','scope':'Two matched ordinary-Lean AM component compile runs, exact fresh deps and20-root axiom audits. Not a complete submission/theorem advancement or website acceptance.','compiler':'Lean4.33.0-rc2 Linux, commitd8b18978322de05a8f3dba51ef03cf5461676c17','lean_binary_sha256':'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550','harness_sha256':harness_sha,'workers':4,'compiler_stack_setting':'--tstack=32768','compile_timeout_seconds':1200,'deps_audit_timeout_seconds':180,'cgroup_memory_and_memsw_bytes':8589934592,'swap':0,'cgroup_cpu_quota':'4 CPUs, quota400000/period100000','surrounding_WSL_VM_GiB':32,'both_cgroup_peaks_reached_8GiB':True,'whole_8GiB_VM_headroom_established':False,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'same_Linux_pairs':1,'wall_time_reduction_percent':18.897979321524794,'peak_PSS_difference_percent':0.7761647393494719,'significant_memory_gain_established':False,'repeatability_established':False,'live_stdout_barrier_count_only_lower_bound':True,'whole_source_verification_pending_at_packaging':True,'no_compiler_cache_runtime_binary_or_Linux_call_during_packaging':True,'input_selection':'Only required archived Windows text records; no full scratch tree copied.'})

 def line_spans(path,pattern):
  return [{'line':i+1,'text':x} for i,x in enumerate(path.read_text(encoding='utf-8-sig').splitlines()) if pattern(x)]
 generated('provenance/source-line-spans.json',{'status':'TEXT_LINE_PROVENANCE_ONLY','paths_relative_to_packet':True,'driver_execution_boundary':line_spans(AM/'run_am_native_v3_trial.py',lambda s:s.startswith('def ') or '--execute' in s or '--tstack' in s or 'fresh' in s.lower()),'bounded_source_external_reference':compiled['bounded8']['source_sha256'],'bounded_scheduler_and_restore_lines':line_spans(AM/'AMBoundedAsync8.lean',lambda s:s.startswith('elab "am_wait"') or 'IO.wait env.checked' in s or s.strip() in ['set_option Elab.async true','set_option Elab.async false']),'source_control_hash':compiled['syncalias8']['source_sha256'],'source_fresh_root_audit':'FreshAllRoots.lean has20 exact main12+alias8 roots; actual logs are gzipped under runs/.','prepared_status_note':'Original prepared config/static reviews deliberately retain historical PREPARED/PENDING fields. Completed summaries and raw exit-zero records establish only the component scope.'})
 put(Path(__file__),'provenance/prepare_publication_evidence.py',role='file-only deterministic archive builder source')

 readme='''# AM controlled component evidence

This prospective packet records one same-Linux paired experiment using the pinned Lean4.33.0-rc2 compiler and v3 harness. It is a file-only archive proposal; no public files were changed and no compiler/cache action ran during packaging.

| Component | Compile wall time | Cgroup CPU time | Sampled peak PSS |
|---|---:|---:|---:|
| bounded8 | 448.761s | 526.1086613s | 7,998,533,632B |
| synchronous alias8 | 553.329s | 533.2747335s | 8,061,101,056B |

The bounded run was18.90% faster in this single pair. PSS differed by0.78% (62,567,424B), insufficient to claim a significant memory gain or repeatability. Both observed cgroup peaks reached8GiB, so no memory headroom in a whole8GiBVM is established. The surrounding WSL VM was32GiB. Each compiler used `-j4 --tstack=32768`, a four-CPU cgroup quota, memory+memsw8GiB, no swap and a1200s compile guard. Fresh deps and20-root audits each had a180s guard.

Both variants compiled ordinarily with actual exit0, then imported the exact newly generated `RecordProportion.ImportedAM.olean` and audited all main12+alias8 roots. The identical axiom lists are subsets of `propext`, `Classical.choice`, `Quot.sound`; no new axioms, sorry/native_decide or weakened targets were introduced. Raw before/after input bindings, PSS/RSS/cgroup/CPU samples, logs and scoped cold-page residency checks are preserved under `runs/`.

Control compilation finished2026-10-10 at02:02:31 China time. A host/runtime session restart occurred afterward; the coordinating root reported a resume around06:12. Pending control deps/audit resumed at06:16 and completed06:17, using the same exact source and `.olean` hashes. There was no control recompilation. This validation-phase gap is disclosed in `validation-phase-gap.json`; it does not change the completed paired compile measurements.

`comparison.json`, `summaries/` and `packet-scope.json` state the checked scope. `analysis/` preserves finalized monotonic barrier timing and a coarse peak-sample attribution with plus-or-minus1s uncertainty. Live barrier output was buffered and only a lower bound; no individual proof is identified as a memory culprit. There are no timestamped checkpoints for synchronous source attribution.

`archive-manifest.json` binds each local record to compressed and decompressed exact byte counts and SHA256 hashes. Every gzip has `mtime=0` and an empty filename header. Full bounded8 source and parser recipes already exist byte-exactly in the finite publication proposal, and are referenced by content hashes in the manifest rather than duplicated. `source-review/AMSyncAlias8.lean.gz` supplies the additional exact control source. Root must preserve/relocate the external packet references when merging publication proposals.

The exact prepared runner/config and Windows-archived v3 harness/environment inventories are source/text provenance. Earlier prepared/static files retain their original pending labels; actual completed summaries take precedence for component validation. No Lean executables, `.olean`/IR files, cache archives or entire scratch trees are included. Whole bundled Solution, independent verifier/Comparator and website acceptance remain separate checks.
'''
 readme=readme.replace('was18','was 18').replace('by0','by 0').replace('reached8','reached 8').replace('whole8','whole 8').replace('was32','was 32').replace('a1200','a 1200').replace('a180','a 180').replace('all main12','all main 12').replace('finished2026','finished 2026').replace('at02','at 02').replace('around06','around 06').replace('at06','at 06').replace('completed06','completed 06').replace('plus-or-minus1s','plus-or-minus 1s')
 p=OUT/'README.md';p.write_text(readme,encoding='utf-8',newline='\n');raw=p.read_bytes();manifest['files'].append({'path':'README.md','role':'publication-scope reading guide','archive_bytes':len(raw),'archive_sha256':plain_hash(raw),'decompressed_bytes':len(raw),'decompressed_sha256':plain_hash(raw),'encoding':'identity','source_origin':'Generated solely from checked component records and trusted root phase-gap disclosure'})
 manifest['local_file_count']=len(manifest['files']);manifest['local_archive_bytes']=sum(x['archive_bytes'] for x in manifest['files']);manifest['local_decompressed_bytes']=sum(x['decompressed_bytes'] for x in manifest['files'])
 write_json(OUT/'archive-manifest.json',manifest)
 (OUT/'archive-manifest.sha256').write_text(digest(OUT/'archive-manifest.json')+'  archive-manifest.json\n',encoding='ascii',newline='\n')
 report={'status':'PREPARED_FILE_ONLY_PUBLICATION_PACKET','packet_root':str(OUT),'manifest_sha256':digest(OUT/'archive-manifest.json'),'files':manifest['local_file_count'],'archive_bytes_without_manifest':manifest['local_archive_bytes'],'decompressed_bytes_without_manifest':manifest['local_decompressed_bytes'],'deduplicated_reference_count':len(manifest['external_deduplicated_references']),'all_exact_byte_hashes_verified':True,'all_gzip_mtime_zero':True,'compiler_cache_binary_or_Linux_actions_executed':False,'public_files_edited':False}
 write_json(AM/'publication-evidence-preparation-result.json',report);print(json.dumps(report,indent=2))

if __name__=='__main__':main()
