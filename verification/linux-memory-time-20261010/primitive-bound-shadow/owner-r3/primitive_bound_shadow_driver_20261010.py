"""Frozen-input shadow probes; dry-run by default. Never a fresh whole proof."""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess, sys, time, types
BASE=Path('/tmp/rh-proportion-memory-20261010')
WHOLE=BASE/'whole-native-20261010-r6'
WHOLE_SHA='db28df608ce9dac67b5f94798beaa1ca9c35f28e92f49e1068cd6f30796bfd79'
CONFIG_SHA='ec3cc48754945e0fb7361bd88edced444bd8a491fce20bc6452b4a465c61afbf'
SOURCE=Path('/mnt/e/codex-build/RH-Weil/tmp/primitive-bound-shadow-probe-20261010-r2')
VARIANTS={
 'original':('PrimitiveOriginal','092c03d88e8c0ef8661209e85da9b9f9ac538c126f8e191948a101bc45cf8e63',3917),
 'explicit':('PrimitiveExplicit','6eda023d84689f7c5c86fb4a25ab57bacf1b0d6cad24334ccb474d944fe4ff5d',4010)}
PREFIX='RHWeil.RecordSubmission.FiniteCertificate.'
OLD_TARGET=PREFIX+'primitiveBound_sound'

def sha(path):
 h=hashlib.sha256()
 with Path(path).open('rb') as stream:
  for data in iter(lambda:stream.read(1048576),b''):h.update(data)
 return h.hexdigest()
def write(path,obj):Path(path).write_text(json.dumps(obj,indent=2)+'\n')
def frozen():
 path=WHOLE/'whole_candidate_native_driver_20261010.py';assert sha(path)==WHOLE_SHA
 module=types.ModuleType('frozen_whole');module.__file__=str(path)
 exec(compile(path.read_bytes(),str(path),'exec'),module.__dict__)
 config=module.load_config(types.SimpleNamespace(native_root=WHOLE,config_sha=CONFIG_SHA))
 module.prereq(config,'audit')
 return module,config
def audit_source(module,target):
 return f'''import {module}
import Comparator.Util
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option pp.universes true
open Lean Elab Command
private def usedConsts (info : Lean.ConstantInfo) : Array Lean.Name :=
  ((Comparator.runForUsedConsts info (fun n => modify (fun ns => ns.push n)) :
      StateM (Array Lean.Name) Unit).run #[]).2
run_cmd do
  let env ← Lean.getEnv
  let probe := `{target}
  let old := `{OLD_TARGET}
  let some p := env.find? probe | throwError "missing probe theorem"
  let some o := env.find? old | throwError "missing original target type"
  unless p.type == o.type do
    throwError "shadow type differs structurally from original"
  IO.eprintln "PROBE_TYPE_IDENTICAL true"
  let mut pending := #[probe]
  let mut seen : Std.HashSet Name := {{}}
  let mut axioms : Std.HashSet Name := {{}}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      if n == old then throwError "original theorem used by shadow closure"
      let some info := env.find? n | throwError "missing dependency {{n}}"
      seen := seen.insert n
      if let .axiomInfo _ := info then
        unless n == `propext || n == `Quot.sound || n == `Classical.choice do
          throwError "nonstandard axiom {{n}}"
        axioms := axioms.insert n
      pending := pending ++ usedConsts info
  IO.eprintln s!"PROBE_CLOSURE_CHECKED {{seen.size}} ORIGINAL_TARGET_PRESENT false"
  IO.eprintln s!"PROBE_STANDARD_AXIOMS {{axioms.toArray}}"
#check {target}
#print axioms {target}
'''
def stage(root):
 assert os.geteuid()==0 and root.parent==BASE and root.name.startswith('primitive-bound-shadow-')
 assert not root.exists()
 whole,config=frozen()
 compile_ledger=json.loads((WHOLE/'phase-ledgers/compile.json').read_text())
 assert compile_ledger['proof_succeeded'] and not compile_ledger['resource_fit']
 root.mkdir();bindings={}
 for variant,(module,digest,size) in VARIANTS.items():
  source=SOURCE/(module+'.lean');assert sha(source)==digest and source.stat().st_size==size
  directory=root/variant
  for relative in ('source','lib','audit-source','audit-lib','records'):(directory/relative).mkdir(parents=True)
  destination=directory/'source'/(module+'.lean');destination.write_bytes(source.read_bytes())
  target=PREFIX+'primitiveBound_sound_probe_'+variant
  audit=directory/'audit-source'/'FreshProbeAudit.lean';audit.write_text(audit_source(module,target))
  bindings[str(destination)]=digest;bindings[str(audit)]=sha(audit)
 driver=root/'primitive_bound_shadow_driver_20261010.py';driver.write_bytes(Path(__file__).read_bytes())
 plan={'scope':'Independent shadow theorem pair using explicitly reused exact r6 artifact. Compile r6 resource gate false remains; not fresh whole proof, live contract, pipeline fit or website acceptance.',
  'root':str(root),'driver_sha256':sha(driver),'whole_driver_sha256':WHOLE_SHA,'whole_config_sha256':CONFIG_SHA,
  'compile_ledger_sha256':sha(WHOLE/'phase-ledgers/compile.json'),
  'dependency_family':compile_ledger['artifact_family_after'],'tool_family':whole.family(Path(config['toolroot'])/'tool-lib'),
  'source_bindings':bindings,'compiler_sha256':whole.LEAN_SHA,'harness_sha256':whole.HARNESS_SHA,
  'root_names':{v:PREFIX+'primitiveBound_sound_probe_'+v for v in VARIANTS},
  'lean_path_tail':':'.join([str(WHOLE/'lib'),str(Path(config['toolroot'])/'tool-lib'),*config['packages']]),
  'experimental_flags':['-j4','--tstack=32768'],'timeout_seconds_each':240,
  'compile_resource_gate_inherited':False,'official_fit_claimed':False,'website_accepted':False}
 write(root/'plan.json',plan)
 for p in [root,*root.rglob('*')]:os.chown(p,1000,1000)
 print(json.dumps({'status':'STAGED_NO_PROOF_EXECUTION','root':str(root),'plan_sha256':sha(root/'plan.json'),
  'driver_sha256':sha(driver),'source_bindings':bindings},indent=2))
def load(root,plan_sha):
 assert sha(root/'plan.json')==plan_sha
 plan=json.loads((root/'plan.json').read_text());assert sha(Path(__file__))==plan['driver_sha256']
 whole,config=frozen()
 assert sha(WHOLE/'phase-ledgers/compile.json')==plan['compile_ledger_sha256']
 assert whole.family(WHOLE/'lib')==plan['dependency_family']
 assert whole.family(Path(config['toolroot'])/'tool-lib')==plan['tool_family']
 for path,digest in plan['source_bindings'].items():assert sha(path)==digest,path
 return plan,whole,config
def commands(plan,variant):
 module=VARIANTS[variant][0];directory=Path(plan['root'])/variant
 return [[str(BASE/'lean-4.33.0-rc2-linux/bin/lean'),*plan['experimental_flags'],'-R',str(directory/'source'),
  '-o',str(directory/'lib'/(module+'.olean')),str(directory/'source'/(module+'.lean'))],
  [str(BASE/'lean-4.33.0-rc2-linux/bin/lean'),*plan['experimental_flags'],'-R',str(directory/'audit-source'),
  '-o',str(directory/'audit-lib/FreshProbeAudit.olean'),str(directory/'audit-source/FreshProbeAudit.lean')]]
def worker(args):
 plan,whole,config=load(args.root,args.plan_sha)
 directory=args.root/args.variant
 env=dict(os.environ);env['LEAN_PATH']=str(directory/'lib')+':'+plan['lean_path_tail']
 tasks=[]
 for command in commands(plan,args.variant):
  start=time.monotonic();print(json.dumps({'starting':command}),flush=True)
  p=subprocess.run(command,cwd=directory/'source',env=env)
  tasks.append({'command':command,'actual_exit_code':p.returncode,'elapsed_seconds':round(time.monotonic()-start,3)})
  write(directory/'records/worker-tasks.json',tasks)
  if p.returncode:return p.returncode
 return 0
def run(args):
 plan,whole,config=load(args.root,args.plan_sha)
 if not args.execute:
  print(json.dumps({'status':'PLAN_ONLY','variant':args.variant,'commands':commands(plan,args.variant),
   'scope':plan['scope']},indent=2));return 0
 assert os.geteuid()==0 and args.authorization_note
 directory=args.root/args.variant;assert not (directory/'records/ledger.json').exists()
 assert not whole.family(directory/'lib') and not whole.family(directory/'audit-lib')
 bindings=[Path(__file__),args.root/'plan.json',WHOLE/'config.json',WHOLE/'phase-ledgers/compile.json',
  WHOLE/'whole_candidate_native_driver_20261010.py',whole.HARNESS,*map(Path,plan['source_bindings']),
  *map(Path,config['sources']),*map(Path,config['tool_config_bindings']),*map(Path,plan['dependency_family']),
  *map(Path,plan['tool_family'])]
 command=['/usr/bin/python3',str(whole.HARNESS),'--run-id',args.run_id,'--timeout','240',
  '--cwd',str(directory/'source')]
 for p in dict.fromkeys(bindings):command.extend(['--bind',str(p)])
 for p in (WHOLE/'lib',Path(config['toolroot'])/'tool-lib',directory/'lib',directory/'audit-lib'):
  command.extend(['--evict-root',str(p)])
 command.extend(['--','/usr/bin/python3',str(Path(__file__)),'--root',str(args.root),'--plan-sha',args.plan_sha,
  '--variant',args.variant,'--worker'])
 start=time.monotonic();samples=[]
 with (directory/'records/supervisor.log').open('xb') as out:
  process=subprocess.Popen(command,stdout=out,stderr=subprocess.STDOUT)
  while process.poll() is None:
   samples.append({'elapsed_seconds':round(time.monotonic()-start,3),'caller':whole.proc_memory(os.getpid()),
    'harness':whole.proc_memory(process.pid)});time.sleep(1)
  code=process.wait()
 record=BASE/'resource-runs'/args.run_id
 result=json.loads((record/'result.json').read_text()) if (record/'result.json').exists() else {'proof_succeeded':False,'resource_fit':False}
 result.update({'variant':args.variant,'supervisor_exit_code':code,'scope':plan['scope'],
  'authorization_note':args.authorization_note,'actual_phase_total_wall_seconds':round(time.monotonic()-start,3),
  'plan_sha256':args.plan_sha,'dependency_family':plan['dependency_family'],'compiler_artifacts_after':whole.family(directory/'lib'),
  'audit_artifacts_after':whole.family(directory/'audit-lib'),'outside_cgroup_samples':samples,
  'outside_cgroup_peak_pss_bytes':max((s['caller']['pss_bytes']+s['harness']['pss_bytes'] for s in samples),default=0),
  'boot_id':Path('/proc/sys/kernel/random/boot_id').read_text().strip()})
 if result['proof_succeeded']:
  text=(record/'process.log').read_text();target=plan['root_names'][args.variant]
  markers=('PROBE_TYPE_IDENTICAL true','ORIGINAL_TARGET_PRESENT false')
  match=re.search(re.escape(target)+r"' depends on axioms: \[([^\]]*)\]",text)
  actual=set() if not match else {re.sub(r'\.\{[^}]*\}$','',n.strip()) for n in match.group(1).split(',') if n.strip()}
  passed=all(x in text for x in markers) and match is not None and actual<={'propext','Quot.sound','Classical.choice'}
  result['fresh_same_type_standard_axioms_no_original_target']=passed
  if not passed:result['proof_succeeded']=False;result['audit_postcondition_error']='Missing fresh audit markers/standard axiom root'
  try:load(args.root,args.plan_sha)
  except BaseException as error:result['proof_succeeded']=False;result['provenance_postcondition_error']=repr(error)
 write(directory/'records/ledger.json',result)
 print(json.dumps({k:v for k,v in result.items() if k not in ('samples','per_process','outside_cgroup_samples','inputs_before','inputs_after','initial_cgroup','final_cgroup','dependency_family')},indent=2))
 return 0 if result['proof_succeeded'] and result['resource_fit'] else 1
def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--root',type=Path,required=True);parser.add_argument('--stage',action='store_true')
 parser.add_argument('--plan-sha');parser.add_argument('--variant',choices=VARIANTS)
 parser.add_argument('--worker',action='store_true');parser.add_argument('--execute',action='store_true')
 parser.add_argument('--run-id');parser.add_argument('--authorization-note',default='')
 args=parser.parse_args();args.root=args.root.resolve()
 if args.stage:stage(args.root);return 0
 assert args.variant and args.plan_sha
 return worker(args) if args.worker else run(args)
if __name__=='__main__':sys.exit(main())
