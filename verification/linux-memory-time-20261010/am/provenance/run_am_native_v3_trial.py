"""Prepared-only by default. Execute one explicitly coordinated isolated Lean phase."""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess, sys, time

BASE=Path('/tmp/rh-proportion-memory-20261010')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write_json(path,data):
 path=Path(path);path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(data,indent=2)+'\n')
def inventory(variant):
 root=Path(variant['lib_root']); result={}
 for p in sorted((root/'RecordProportion').glob('ImportedAM.*')):
  if p.is_file():
   assert p.resolve().is_relative_to(root.resolve())
   result[str(p)]={'bytes':p.stat().st_size,'sha256':sha(p)}
 return result
def common_bindings(config,variant):
 return list(dict.fromkeys([variant['source'],variant['audit_source'],str(Path(__file__).resolve()),
  str(Path(__file__).resolve().parent/'config.json'),config['prepare_driver'],config['handoff'],
  config['harness'],config['lean'],config['native_verification'],config['ir_signature_verification'],
  *[x['path'] for x in config['evidence_bindings']]]))
def command(config,variant,phase,artifacts=None):
 runid=variant[phase+'_run_id'];timeout=config[phase+'_timeout_seconds']
 lean_path=config['lean_path_baseline'] if phase=='compile' else variant['lib_root']+':'+config['lean_path_baseline']
 cmd=['python3',config['harness'],'--run-id',runid,'--timeout',str(timeout),
      '--cwd',variant['source_root'],'--lean-path',lean_path]
 for bind in [*common_bindings(config,variant),*(artifacts or {}).keys()]:cmd+=['--bind',bind]
 for root in config['all_overlay_roots']:cmd+=['--evict-root',root]
 cmd+=['--',config['lean'],'-j4','--tstack=32768','-R',variant['source_root']]
 if phase=='compile':cmd+=['-o',variant['artifact'],variant['source']]
 elif phase=='deps':cmd+=['--deps',variant['audit_source']]
 else:cmd+=['-o',variant['audit_lib_root']+'/FreshAllRoots.olean',variant['audit_source']]
 return cmd

def audit_output(text,config):
 pattern=r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
 rows=[]
 for match in re.finditer(pattern,text,re.S):
  axioms=[] if match.group(2) is None else [x.strip() for x in match.group(2).split(',') if x.strip()]
  rows.append({'root':match.group(1),'axioms':axioms})
 byroot={x['root']:x['axioms'] for x in rows}
 complete=len(rows)==len(byroot)==len(config['roots']) and set(byroot)==set(config['roots'])
 allowed=set(config['allowed_axioms']);clean=all(set(row['axioms'])<=allowed for row in rows)
 return {'roots':rows,'exact_twenty_roots_present':complete,'allowed_standard_axioms_only':clean,
         'pass':complete and clean}

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--variant',choices=['bounded8','syncalias8'],required=True)
 parser.add_argument('--phase',choices=['compile','deps','audit'],default='compile')
 parser.add_argument('--execute',action='store_true')
 parser.add_argument('--authorization-note',default='')
 args=parser.parse_args()
 assert not sys.flags.optimize,'-O would disable provenance/safety gates'
 config_path=Path(__file__).resolve().parent/'config.json';config=json.loads(config_path.read_text())
 variant=config['variants'][args.variant]
 assert config['status']=='PREPARED_NOT_CHECKED' and config['workers']==4 and config['tstack']==32768
 assert config['compile_timeout_seconds']==1200
 assert Path(config['native_root']).resolve().is_relative_to(BASE.resolve())
 assert variant['artifact']==variant['lib_root']+'/RecordProportion/ImportedAM.olean'
 assert sha(__file__)==config['runner_sha256']
 assert sha(variant['source'])==variant['source_sha256'] and Path(variant['source']).stat().st_size==variant['source_bytes']
 assert sha(variant['audit_source'])==variant['audit_sha256']
 if not args.execute:
  print(json.dumps({'status':'PREPARED_NOT_CHECKED','phase':args.phase,'variant':args.variant,
        'no_lean_invoked':True,'no_eviction_invoked':True,
        'argv_template':command(config,variant,args.phase),
        'deferred_bindings':'deps/audit must additionally bind every actual newly compiled AM artifact',
        'authorization_required':'Parent must explicitly allocate this phase after sole finite proof owner releases.'},indent=2))
  return
 assert args.authorization_note.strip(),'Execute requires the coordinating root authorization note'
 assert os.geteuid()==0,'Only supervisor is root; harness proof worker uid1000'
 assert sha(config['harness'])==config['harness_sha256']
 assert sha(config['lean'])==config['lean_sha256']
 assert sha(config['handoff'])==config['handoff_sha256']
 assert sha(config['prepare_driver'])==config['prepare_driver_sha256']
 for binding in config['evidence_bindings']:assert sha(binding['path'])==binding['sha256']
 evidence=Path(config['native_root'])/'evidence'/args.variant;evidence.mkdir(parents=True,exist_ok=True)
 stage_record=evidence/(args.phase+'-stage.json');assert not stage_record.exists(),'Never overwrite an executed phase'
 resource=BASE/'resource-runs'/variant[args.phase+'_run_id'];assert not resource.exists(),'Fresh run-id required'
 before={}
 if args.phase=='compile':
  assert not inventory(variant),'No prior AM artifacts admitted to a fresh compile'
 else:
  compiled=json.loads((evidence/'compile-stage.json').read_text())
  assert compiled['actual_proof_succeeded'] and compiled['artifact_inventory'],'Fresh compile proof must have succeeded'
  before=inventory(variant);assert before==compiled['artifact_inventory'],'Fresh AM artifacts changed'
  assert variant['artifact'] in before,'Missing exact fresh .olean'
  if args.phase=='audit':
   deps=json.loads((evidence/'deps-stage.json').read_text())
   assert deps['deps_gate']['pass'],'Actual --deps must resolve exact fresh AM before axioms audit'
   assert deps['artifact_inventory']==before
 cmd=command(config,variant,args.phase,before)
 prepared={'status':'RUNNING','phase':args.phase,'variant':args.variant,'authorization_note':args.authorization_note,
           'source_sha256':variant['source_sha256'],'source_bytes':variant['source_bytes'],
           'argv':cmd,'source_root':variant['source_root'],'module':'RecordProportion.ImportedAM',
           'resource_dir':str(resource),'artifact_inventory_before':before,
           'no_old_am_artifact_copied':True,'reused_original_cached_ImportedAM':False,
           'scope':config['scope']}
 write_json(evidence/(args.phase+'-launch.json'),prepared)
 started=time.monotonic()
 result=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 (evidence/(args.phase+'-harness.stdout.log')).write_bytes(result.stdout)
 (evidence/(args.phase+'-harness.stderr.log')).write_bytes(result.stderr)
 actual=None
 for name in ['result.json','process.log','scoped-cache-eviction.json']:
  p=resource/name
  if p.exists():shutil_copy_bytes(p,evidence/(args.phase+'-'+name))
 if (resource/'result.json').exists():actual=json.loads((resource/'result.json').read_text())
 produced=inventory(variant)
 stage={**prepared,'status':'FAILED_PRESERVED','harness_exit_code':result.returncode,
        'supervisor_wall_seconds':round(time.monotonic()-started,3),'artifact_inventory':produced,
        'actual_proof_succeeded':bool(actual and actual['proof_succeeded']),
        'actual_component_resource_fit':bool(actual and actual['resource_fit']),
        'actual':actual,'completed_phase_pass':False,'official_whole_fit_claim':False,
        'website_acceptance_claim':False,'failed_outputs_deleted':False}
 if actual and actual['proof_succeeded']:
  assert variant['artifact'] in produced,'Lean success without expected fresh artifact'
  if args.phase=='compile':stage['completed_phase_pass']=True
  else:
   assert produced==before,'AM artifact changed during fresh import/audit'
   output=(resource/'process.log').read_text()
   if args.phase=='deps':
    dependency_lines=output.splitlines(); found=variant['artifact'] in dependency_lines
    other=[p for p in dependency_lines if p.endswith('/RecordProportion/ImportedAM.olean') and p!=variant['artifact']]
    stage['deps_gate']={'fresh_artifact':variant['artifact'],'exact_fresh_artifact_resolved':found,
                        'unexpected_old_am_paths':other,'pass':found and not other,
                        'all_dependency_lines':dependency_lines}
    stage['completed_phase_pass']=stage['deps_gate']['pass']
   else:
    stage['axiom_gate']=audit_output(output,config)
    stage['completed_phase_pass']=stage['axiom_gate']['pass']
 stage['status']='PASS_PROOF_AND_RESOURCE' if stage['completed_phase_pass'] and stage['actual_component_resource_fit'] else ('PASS_PROOF_RESOURCE_LIMIT' if stage['completed_phase_pass'] else 'FAILED_PRESERVED')
 stage['source_unchanged_after']=sha(variant['source'])==variant['source_sha256']
 stage['fresh_artifact_family_bound_on_import']=args.phase!='compile' and bool(before)
 write_json(stage_record,stage)
 print(json.dumps({k:v for k,v in stage.items() if k not in ['actual','argv','deps_gate']},indent=2),flush=True)
 if actual:print(json.dumps({k:actual.get(k) for k in ['actual_exit_code','elapsed_seconds','timeout','oom_kill_count','memory_limit_hit','sampled_tree_peak_rss_bytes','sampled_tree_peak_pss_bytes','sampled_tree_peak_swap_bytes','proof_succeeded','resource_fit']},indent=2),flush=True)
 raise SystemExit(0 if stage['completed_phase_pass'] else 1)

def shutil_copy_bytes(src,dst):Path(dst).write_bytes(Path(src).read_bytes())
if __name__=='__main__':main()
