"""Stage/drive fresh Linux candidate checks. Default is a plan, never proof execution.

Frozen v3 measures independent local phases inside 32-GiB WSL. This driver is
not the website E2B/Landlock wrapper and cannot establish website acceptance.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess, sys, time

BASE = Path('/tmp/rh-proportion-memory-20261010')
PREPARED = Path('/mnt/e/codex-build/RH-Zero-Proportion-Formalization/tmp/memory-optimization-20261010/verifier-graph-audit/linux-verifier-prepared')
CONTRACT = Path('/mnt/e/codex-build/RH-Zero-Proportion-Formalization/tmp/memory-optimization-20261010/contract-current')
DEFAULT_SOURCE = Path('/mnt/e/codex-build/RH-Zero-Proportion-Formalization/tmp/memory-optimization-20261010/am/whole-bounded8-prepared/Solution.memory-prepared.lean')
DEFAULT_SHA = 'f40d0cb3566d4e71a6bb624a4d4375ca3ade977d3850e14e134a8a850f4abd50'
PLAN_SHA = '251161300ee0fc882656e6f7efaa8a7f74697165e049acdd4aa27f0526474fbc'
LEAN = BASE/'lean-4.33.0-rc2-linux/bin/lean'
LEAN_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
HARNESS = Path('/mnt/e/codex-build/RH-Weil/tmp/linux_cgroup_resource_harness_v3_20261010.py')
HARNESS_SHA = 'e192787f00ea5ceb0c77a06969bb832136b751337a475dd0e63619743f4d24ec'
NANO = Path('/mnt/e/codex-build/RH-Zero-Proportion-Formalization/tmp/kernel-tools/nanoda-target/release/nanoda_bin')
NANO_SHA = 'b19804767cb72bf5a317fcfc20e8af7eafdfba789dd6b24bddee2574379ff35a'
PHASES = ('tools', 'contract', 'challenge-export', 'compile', 'deps', 'audit', 'solution-export', 'core', 'nano')
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig')

def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()

def write_json(path, obj):
    Path(path).write_text(json.dumps(obj,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')

def family(root):
    return {str(p):{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(Path(root).rglob('*')) if p.is_file() and p.name.endswith(SUFFIXES)}

def proc_memory(pid):
    try:
        fields=dict(x.split(':',1) for x in Path(f'/proc/{pid}/smaps_rollup').read_text().splitlines() if ':' in x)
        return {k.lower()+'_bytes':int(fields.get(k,'0 kB').split()[0])*1024 for k in ('Rss','Pss','Swap')}
    except (FileNotFoundError,ProcessLookupError):return {'rss_bytes':0,'pss_bytes':0,'swap_bytes':0}

def clock_elapsed(clock):
    assert clock['boot_id']==Path('/proc/sys/kernel/random/boot_id').read_text().strip(),'Different Linux boot: refuse monotonic-clock reuse'
    elapsed=time.monotonic()-clock['start_monotonic']
    assert elapsed>=0,'Monotonic-clock reuse invalid'
    return elapsed

def stage(args):
    assert os.name=='posix' and os.geteuid()==0
    root=args.native_root.resolve()
    assert root.parent==BASE and root.name.startswith('whole-native-')
    assert not root.exists(),'Refuse previous stage overwrite'
    assert sha(PREPARED/'prepared-plan.json')==PLAN_SHA
    assert sha(LEAN)==LEAN_SHA and sha(HARNESS)==HARNESS_SHA
    assert sha(args.source)==args.source_sha
    data=args.source.read_bytes()
    assert len(data)<=2_000_000 and re.search(rb'^import ChallengeDeps\.CandidateSpec\s*$',data,re.M)
    # Preserve the original stager. Its optional Lake toolchain metadata has
    # a Windows CRLF mismatch; the first failed small-source stage is retained.
    # Only the exact plan's source bindings are needed for direct Lean execution.
    stager=PREPARED/'stage_native.py'
    assert sha(stager)=='967b660c34ce4e952057cfb10a8c9c9e4668ab3dea2027cbc87f164219aa869d'
    toolroot=Path(str(root).replace('whole-native-','verifier-native-'))
    assert not toolroot.exists(),'Refuse previous tool stage overwrite'
    plan=json.loads((PREPARED/'prepared-plan.json').read_text())
    copied={}
    for row in plan['source_bindings']:
        src=PREPARED/row['prepared'];assert sha(src)==row['sha256'],row['prepared']
        dest=toolroot/row['prepared'];dest.parent.mkdir(parents=True,exist_ok=True)
        dest.write_bytes(src.read_bytes());copied[row['prepared']]=row['sha256']
    for rel in ('tool-lib/Export','tool-lib/Comparator','exports','logs'):(toolroot/rel).mkdir(parents=True,exist_ok=True)
    config_bindings={}
    for rel in ('nanoda-official-default-config.json','comparator-config-candidate.json'):
        (toolroot/rel).write_bytes((PREPARED/rel).read_bytes());copied[rel]=sha(toolroot/rel)
        config_bindings[str(toolroot/rel)]=copied[rel]
    assert json.loads((toolroot/'nanoda-official-default-config.json').read_text())==plan['future_nano_command']['actual_config']
    def rewrite(v):
        if isinstance(v,dict):return {k:rewrite(x) for k,x in v.items()}
        if isinstance(v,list):return [rewrite(x) for x in v]
        if isinstance(v,str):return v.replace(plan['native_root'],str(toolroot))
        return v
    nativeplan=rewrite(plan);nativeplan['status']='STAGED_SMALL_SOURCES_ONLY_NO_COMPILATION_OR_VERIFICATION'
    write_json(toolroot/'prepared-plan.json',nativeplan)
    write_json(toolroot/'staging-result.json',{'status':'STAGED_SMALL_SOURCES_ONLY','copied_source_bindings':copied,'producer_sha256':sha(Path(__file__)),'proof_or_tools_executed':False,'optional_lake_toolchain_not_used':True})
    root.mkdir()
    for rel in ('source/Solution','source/ChallengeDeps','source/Challenge','lib/Solution','lib/ChallengeDeps','lib/Challenge','audit-source','audit-lib','phase-ledgers'):
        (root/rel).mkdir(parents=True,exist_ok=True)
    contract=json.loads((CONTRACT/'prepared-contract.json').read_text())
    assert contract['website']['commit']=='6664d243005e12e155c19775b83f53721757414b'
    assert contract['current_record_expression']=='(6735015 : ℝ) / 10000000'
    assert contract['candidate_score']=={'numerator':'66812491','denominator':'99194740'}
    bindings={}
    for row in contract['generated']:
        source=CONTRACT/row['path'];assert sha(source)==row['sha256']
        dest=root/'source'/row['path'];dest.write_bytes(source.read_bytes());bindings[str(dest)]=row['sha256']
    dest=root/'source/Solution/Candidate.lean';dest.write_bytes(data);bindings[str(dest)]=args.source_sha
    audit=root/'audit-source/FreshCandidateAudit.lean'
    targets=json.loads((PREPARED/'prepared-plan.json').read_text())['theorem_targets']
    audit.write_text('import Solution.Candidate\nset_option pp.universes true\n'+'\n'.join(f'#check {x}\n#print axioms {x}' for x in targets)+'\n',encoding='utf-8')
    bindings[str(audit)]=sha(audit)
    driver=root/'whole_candidate_native_driver_20261010.py';driver.write_bytes(Path(__file__).read_bytes())
    plan=json.loads((toolroot/'prepared-plan.json').read_text())
    config={'status':'STAGED_NO_PROOF_EXECUTION','root':str(root),'toolroot':str(toolroot),'sources':bindings,'tool_config_bindings':config_bindings,'source_sha256':args.source_sha,'source_bytes':len(data),'upstream_prepared_plan_sha256':PLAN_SHA,'native_plan_sha256':sha(toolroot/'prepared-plan.json'),'driver_sha256':sha(driver),'harness_sha256':HARNESS_SHA,'lean_sha256':LEAN_SHA,'nano_sha256':NANO_SHA,'contract':contract,'packages':plan['whole_candidate_packages_lean_path'],'targets':targets,'export_targets':plan['export_targets'],'permitted_axioms':plan['permitted_axioms'],'explicit_experimental_compiler_flags':['-j4','--tstack=32768'],'official_stack_flag_established':False,'scope':'Independent local phases, 4 CPU/8 GiB/no-swap cgroup inside 32 GiB WSL; not E2B/Landlock or website acceptance.'}
    write_json(root/'config.json',config)
    for directory in (root,toolroot):
        for p in [directory,*directory.rglob('*')]:os.chown(p,1000,1000)
    print(json.dumps({'status':'STAGED_NO_PROOF_EXECUTION','root':str(root),'config_sha256':sha(root/'config.json'),'driver_sha256':sha(driver),'source_sha256':args.source_sha,'source_bytes':len(data)},indent=2))

def load_config(args):
    path=args.native_root.resolve()/'config.json'
    assert args.config_sha and sha(path)==args.config_sha,'Supply exact staged config SHA'
    config=json.loads(path.read_text())
    assert config['driver_sha256']==sha(Path(__file__))
    assert sha(LEAN)==LEAN_SHA and sha(HARNESS)==HARNESS_SHA
    for p,expected in config['sources'].items():assert sha(p)==expected,p
    tools=Path(config['toolroot']);nativeplan=tools/'prepared-plan.json'
    assert sha(nativeplan)==config['native_plan_sha256']
    plan=json.loads(nativeplan.read_text())
    for row in plan['source_bindings']:
        assert sha(tools/row['prepared'])==row['sha256'],('Pinned tool source changed',row['prepared'])
    for p,expected in config['tool_config_bindings'].items():assert sha(p)==expected,('Pinned tool config bytes changed',p)
    assert json.loads((tools/'nanoda-official-default-config.json').read_text())==plan['future_nano_command']['actual_config'],'Official Nano configuration changed'
    assert config['export_targets']==plan['export_targets'] and len(config['export_targets'])==32
    assert config['permitted_axioms']==plan['permitted_axioms']
    return config

def phase_commands(config, phase):
    root=Path(config['root']);tools=Path(config['toolroot']);source=root/'source';lib=root/'lib'
    packages=config['packages'];fullpath=':'.join([str(lib),str(tools/'tool-lib'),*packages])
    compile_cmd=lambda s,o,base: [str(LEAN),'-j4','--tstack=32768','-R',str(base),'-o',str(o),str(s)]
    tasks=[]
    if phase=='tools':
        plan=json.loads((tools/'prepared-plan.json').read_text())
        for x in plan['direct_native_tool_builds']:
            tasks.append({'label':x['module'],'command':x['command'],'lean_path':str(tools/'tool-lib')})
    elif phase=='contract':
        for rel in ('ChallengeDeps.lean','ChallengeDeps/CandidateSpec.lean','Challenge/Candidate.lean'):
            tasks.append({'label':rel,'command':compile_cmd(source/rel,lib/rel.replace('.lean','.olean'),source),'lean_path':fullpath})
    elif phase=='compile':
        tasks=[{'label':'Solution.Candidate','command':compile_cmd(source/'Solution/Candidate.lean',lib/'Solution/Candidate.olean',source),'lean_path':fullpath}]
    elif phase=='deps':
        tasks=[{'label':'fresh-deps','command':[str(LEAN),'--deps','-R',str(source),str(source/'Solution/Candidate.lean')],'lean_path':fullpath}]
    elif phase=='audit':
        tasks=[{'label':'fresh-three-roots','command':compile_cmd(root/'audit-source/FreshCandidateAudit.lean',root/'audit-lib/FreshCandidateAudit.olean',root/'audit-source'),'lean_path':fullpath}]
    elif phase in ('challenge-export','solution-export'):
        module='Challenge.Candidate' if phase=='challenge-export' else 'Solution.Candidate'
        output=tools/'exports'/('challenge.ndjson' if phase=='challenge-export' else 'solution.ndjson')
        tasks=[{'label':module,'command':[str(LEAN),'-j1','--tstack=32768','-R',str(tools/'entry/exporter'),'--run',str(tools/'entry/exporter/Main.lean'),module,'--',*config['export_targets']],'lean_path':fullpath,'stdout_file':str(output)}]
    elif phase=='core':
        tasks=[{'label':'pinned-comparison-axioms-default-replay','command':[str(LEAN),'-j1','--tstack=32768','-R',str(tools/'entry/core'),'--run',str(tools/'entry/core/tools/ComparatorCoreAudit.lean'),str(tools/'exports/challenge.ndjson'),str(tools/'exports/solution.ndjson'),*config['targets']],'lean_path':str(tools/'tool-lib')}]
    elif phase=='nano':
        assert sha(NANO)==NANO_SHA
        tasks=[{'label':'unchanged-default-serial-nano','command':[str(NANO),str(tools/'nanoda-official-default-config.json')],'stdin_file':str(tools/'exports/solution.ndjson'),'lean_path':''}]
    return tasks

def prereq(config,phase):
    root=Path(config['root']);tools=Path(config['toolroot']);lib=root/'lib'
    if phase=='tools':assert not family(tools/'tool-lib')
    elif phase=='contract':assert not family(lib)
    else:
        for rel in ('ChallengeDeps.olean','ChallengeDeps/CandidateSpec.olean','Challenge/Candidate.olean'):assert (lib/rel).is_file(),rel
        assert json.loads((root/'phase-ledgers/contract.json').read_text())['proof_succeeded']
    if phase=='compile':assert not family(lib/'Solution'),'Fresh Solution artifact family must be empty'
    if phase=='compile':
        contract_ledger=json.loads((root/'phase-ledgers/contract.json').read_text())
        assert family(lib)==contract_ledger['artifact_family_after'],'Current contract artifact family changed after compile'
    if phase=='challenge-export':
        # Challenge export may precede Solution compile (official order) or
        # follow it in a diagnostic phase sequence; bind the actual fresh family.
        prior='compile' if (root/'phase-ledgers/compile.json').exists() else 'contract'
        prior_ledger=json.loads((root/f'phase-ledgers/{prior}.json').read_text())
        assert prior_ledger['proof_succeeded'] and family(lib)==prior_ledger['artifact_family_after'],'Fresh project artifact family changed before challenge export'
    if phase in ('deps','audit','solution-export','core','nano'):
        assert (lib/'Solution/Candidate.olean').is_file()
        compile_ledger=json.loads((root/'phase-ledgers/compile.json').read_text())
        assert compile_ledger['proof_succeeded']
        assert family(lib)==compile_ledger['artifact_family_after'],'Fresh Solution/contract artifact family changed after compile'
    if phase in ('challenge-export','solution-export','core'):
        tool_ledger=json.loads((root/'phase-ledgers/tools.json').read_text())
        assert tool_ledger['proof_succeeded']
        assert family(tools/'tool-lib')==tool_ledger['tool_family_after'],'Pinned tool artifact family changed after compile'
    if phase in ('solution-export','core','nano'):
        assert json.loads((root/'phase-ledgers/deps.json').read_text())['deps_fresh_current_contract_only']
        assert json.loads((root/'phase-ledgers/audit.json').read_text())['fresh_three_roots_standard_axioms']
    if phase in ('core','nano'):
        for name in ('challenge','solution'):
            path=tools/f'exports/{name}.ndjson';assert path.is_file()
            export_ledger=json.loads((root/f'phase-ledgers/{name}-export.json').read_text())
            assert export_ledger['proof_succeeded']
            assert export_ledger['export_file_after']=={'path':str(path),'bytes':path.stat().st_size,'sha256':sha(path)},'Export changed after generation'

def validate_result(config,phase,result,log):
    root=Path(config['root']);lib=root/'lib'
    if phase=='deps':
        text=log.read_text();required=[lib/'ChallengeDeps.olean',lib/'ChallengeDeps/CandidateSpec.olean']
        assert all(str(x) in text for x in required),'Fresh contract --deps missing'
        assert '/native-cache/tmp/contract/' not in text and '/native-cache/.lake/build/lib/lean/' not in text,'Old contract/project namespace leaked'
        result['deps_fresh_current_contract_only']=True
    if phase=='audit':
        text=log.read_text();allowed=set(config['permitted_axioms']);found=[]
        for name in config['targets']:
            match=re.search(re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",text)
            assert match,('missing fresh axioms',name)
            axioms={re.sub(r'\.\{[^}]*\}$','',x.strip()) for x in match.group(1).split(',') if x.strip()}
            assert axioms<=allowed,(name,axioms)
            found.append({'root':name,'axioms':sorted(axioms)})
        result['fresh_three_roots_standard_axioms']=True;result['axiom_roots']=found
    if phase=='core':
        text=log.read_text()
        assert 'Pinned Comparator statement, dependency and primitive comparison passed' in text
        assert 'Pinned Comparator transitive axiom check passed' in text and 'Lean default kernel replay passed' in text
        result['exact_types_primitives_axioms_default_kernel_passed']=True

def worker(args):
    config=load_config(args);assert os.getuid()==1000 and args.tasks_file
    tasks_path=Path(args.tasks_file);assert sha(tasks_path)==args.tasks_sha
    tasks=json.loads(tasks_path.read_text());root=Path(config['root']);rows=[]
    for task in tasks:
        started=time.monotonic();env=os.environ.copy();env['LEAN_PATH']=task['lean_path']
        inp=open(task['stdin_file'],'rb') if task.get('stdin_file') else None
        out=open(task['stdout_file'],'xb') if task.get('stdout_file') else None
        try:
            print(json.dumps({'starting':task['label'],'command':task['command']}),flush=True)
            p=subprocess.run(task['command'],cwd=root/'source',env=env,stdin=inp,stdout=out)
        finally:
            if inp:inp.close()
            if out:out.close()
        row={'label':task['label'],'exit_code':p.returncode,'seconds':round(time.monotonic()-started,3)};rows.append(row)
        print(json.dumps(row),flush=True)
        if p.returncode:
            write_json(root/f'phase-ledgers/{args.phase}-worker.json',{'tasks':rows,'success':False});return p.returncode
    write_json(root/f'phase-ledgers/{args.phase}-worker.json',{'tasks':rows,'success':True});return 0

def run_phase(args):
    config=load_config(args);root=Path(config['root']);tools=Path(config['toolroot'])
    tasks=phase_commands(config,args.phase)
    if not args.execute:
        print(json.dumps({'status':'PLAN_ONLY_NO_EXECUTION','phase':args.phase,'tasks':tasks,'required_authorization':True,'scope':config['scope']},indent=2));return 0
    assert os.geteuid()==0 and args.authorization_note.strip(),'Explicit parent allocation required'
    prereq(config,args.phase)
    ledger=root/f'phase-ledgers/{args.phase}.json';assert not ledger.exists(),'Never overwrite actual phase evidence'
    taskfile=root/f'phase-ledgers/{args.phase}-tasks.json';assert not taskfile.exists();write_json(taskfile,tasks);os.chown(taskfile,1000,1000)
    session=root/'pipeline-clock.json'
    if args.phase=='contract':
        assert not session.exists();write_json(session,{'start_unix':time.time(),'start_monotonic':time.monotonic(),'boot_id':Path('/proc/sys/kernel/random/boot_id').read_text().strip(),'official_inner_seconds':3200,'scope':'Actual local elapsed starts before current contract build, includes every later local cold preparation and caller delay. Tools prebuild excluded. Separate phases/reordered checks differ from official retained-strings pipeline.'})
    clock=json.loads(session.read_text()) if session.exists() else None
    elapsed=clock_elapsed(clock) if clock else 0
    remaining=3200-elapsed if clock else 3400
    if args.enforce_shared_budget:assert remaining>0,'Local shared 3200 seconds exhausted'
    timeout=min(args.timeout,remaining) if args.enforce_shared_budget else args.timeout
    assert 0<timeout<=3400
    binds=[Path(__file__),HARNESS,root/'config.json',taskfile,*map(Path,config['sources']),*map(Path,config['tool_config_bindings'])]
    binds.extend(Path(x) for x in family(root/'lib'));binds.extend(Path(x) for x in family(tools/'tool-lib'));binds.extend(Path(x) for x in family(root/'audit-lib'))
    # All source/config/tool/artifact bindings are hashed before v3's eviction.
    plan=json.loads((tools/'prepared-plan.json').read_text())
    binds.extend(tools/x['prepared'] for x in plan['source_bindings'])
    if args.phase=='nano':binds.extend([NANO,tools/'nanoda-official-default-config.json',tools/'exports/solution.ndjson'])
    if args.phase=='core':binds.extend([tools/'exports/challenge.ndjson',tools/'exports/solution.ndjson'])
    command=['/usr/bin/python3',str(HARNESS),'--run-id',args.run_id,'--timeout',str(timeout),'--cwd',str(root/'source')]
    for p in dict.fromkeys(binds):command.extend(['--bind',str(p)])
    for p in (root/'lib',root/'audit-lib',tools/'tool-lib'):command.extend(['--evict-root',str(p)])
    command.extend(['--','/usr/bin/python3',str(Path(__file__)),'--native-root',str(root),'--config-sha',args.config_sha,'--phase',args.phase,'--worker','--tasks-file',str(taskfile),'--tasks-sha',sha(taskfile)])
    outerlog=root/f'phase-ledgers/{args.phase}-supervisor.log';begin=time.monotonic();samples=[]
    with outerlog.open('xb') as log:
        process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT)
        while process.poll() is None:
            samples.append({'seconds':round(time.monotonic()-begin,3),'caller':proc_memory(os.getpid()),'harness_supervisor':proc_memory(process.pid)})
            time.sleep(1)
        code=process.wait()
    record=BASE/'resource-runs'/args.run_id
    result=json.loads((record/'result.json').read_text()) if (record/'result.json').exists() else {'proof_succeeded':False,'resource_fit':False,'status':'HARNESS_REFUSED_OR_FAILED_BEFORE_RESULT'}
    result.update({'phase':args.phase,'supervisor_exit_code':code,'authorization_note':args.authorization_note,'actual_phase_total_wall_seconds':round(time.monotonic()-begin,3),'source_sha256':config['source_sha256'],'source_bytes':config['source_bytes'],'config_sha256':args.config_sha,'resource_record_directory':str(record),'artifact_family_after':family(root/'lib'),'tool_family_after':family(tools/'tool-lib'),'outside_cgroup_memory_samples':samples,'outside_cgroup_peak_pss_bytes':max((x['caller']['pss_bytes']+x['harness_supervisor']['pss_bytes'] for x in samples),default=0),'shared_clock':clock,'actual_shared_elapsed_seconds':round(time.monotonic()-clock['start_monotonic'],3) if clock else None,'actual_shared_wall_clock_elapsed_seconds':round(time.time()-clock['start_unix'],3) if clock else None,'enforce_shared_budget':args.enforce_shared_budget,'official_fit_claimed':False,'website_accepted':False})
    if args.phase in ('challenge-export','solution-export'):
        name='challenge' if args.phase=='challenge-export' else 'solution';path=tools/f'exports/{name}.ndjson'
        if path.exists():result['export_file_after']={'path':str(path),'bytes':path.stat().st_size,'sha256':sha(path)}
    if result['proof_succeeded']:
        try:validate_result(config,args.phase,result,record/'process.log')
        except BaseException as e:result['postcondition_error']=repr(e);result['proof_succeeded']=False
    write_json(ledger,result)
    print(json.dumps({k:v for k,v in result.items() if k not in ('samples','per_process','outside_cgroup_memory_samples','artifact_family_after','tool_family_after','initial_cgroup','final_cgroup','inputs_before','inputs_after')},indent=2))
    return 0 if result['proof_succeeded'] and result['resource_fit'] else 1

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native-root',type=Path,default=BASE/'whole-native-20261010-r5')
    parser.add_argument('--source',type=Path,default=DEFAULT_SOURCE);parser.add_argument('--source-sha',default=DEFAULT_SHA)
    parser.add_argument('--stage',action='store_true');parser.add_argument('--phase',choices=PHASES)
    parser.add_argument('--config-sha');parser.add_argument('--execute',action='store_true');parser.add_argument('--authorization-note',default='')
    parser.add_argument('--run-id');parser.add_argument('--timeout',type=float,default=3200);parser.add_argument('--enforce-shared-budget',action='store_true')
    parser.add_argument('--worker',action='store_true');parser.add_argument('--tasks-file');parser.add_argument('--tasks-sha')
    args=parser.parse_args()
    if args.stage:return stage(args)
    if not args.phase:
        print(json.dumps({'status':'PLAN_ONLY_NO_EXECUTION','stage_source':str(args.source),'source_sha256':args.source_sha,'native_root':str(args.native_root),'phases':PHASES,'tools_or_proofs_executed':False},indent=2));return 0
    if args.worker:return worker(args)
    if args.execute:assert args.run_id and re.fullmatch(r'[a-z0-9][a-z0-9-]{0,60}',args.run_id)
    return run_phase(args)

if __name__=='__main__':raise SystemExit(main())
