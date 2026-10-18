"""Prepare the single Counting let/cast repair; no mathematical or Lean run."""
import ast
import difflib
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent


def item(p):
    b=p.read_bytes()
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}


def new(p,s):
    p.parent.mkdir(exist_ok=True,parents=True)
    with p.open('x',encoding='utf-8',newline='\n') as f:f.write(s)


def main():
    assert not (ROOT/'tmp/current-s1r-tiny-20261018/phase2-v0').exists()
    oldcount=ROOT/'StructuralS1RTiny20261018/Dev/Counting.lean'
    a=oldcount.read_text(encoding='utf-8')
    assert item(oldcount)['sha256']=='e1629a96ac6239ae0d216c608c99f6d929c779b8201f4835aa72b125b2923f87'
    needle='  simpa only [hcast] using hs'
    assert a.count(needle)==1
    b=a.replace(needle,'  rw [hcast] at hs\n  simpa only [N, Y, Nat.reduceSub, Nat.cast_ofNat] using hs',1)
    count=ROOT/'StructuralS1RTiny20261018/Phase2/Counting.lean';new(count,b)
    oldfinal=ROOT/'StructuralS1RTiny20261018/Phase1/Final.lean'
    fa=oldfinal.read_text(encoding='utf-8')
    fb=fa.replace('import StructuralS1RTiny20261018.Dev.Counting\n',
                  'import StructuralS1RTiny20261018.Phase2.Counting\n',1)
    assert fa!=fb
    final=ROOT/'StructuralS1RTiny20261018/Phase2/Final.lean';new(final,fb)
    runner1=HERE/'compile_phase1.py';ra=runner1.read_text(encoding='utf-8')
    rb=ra
    for x,y in {
        'Localization API-repair compile; reuse proved Core and prefix.':'Counting let/cast API-repair compile; reuse all three proved dependencies.',
        "JOB=ROOT/'tmp/current-s1r-tiny-20261018/phase1-v0'":"JOB=ROOT/'tmp/current-s1r-tiny-20261018/phase2-v0'",
        "prepared=HERE/'phase1-prepared.json'":"prepared=HERE/'phase2-prepared.json'",
        "gate['task']=='tiny-current-s1R-localization-phase1'":"gate['task']=='tiny-current-s1R-counting-phase2'",
        "assert gate['recompile_passed_Core'] is False":"assert gate['recompile_passed_Core'] is False\n    assert gate['recompile_passed_Localization'] is False",
        "'all_three_modules_completed':len(receipts)==3":"'all_two_modules_completed':len(receipts)==2",
        'passed and len(receipts)==3':'passed and len(receipts)==2',
    }.items():
        assert rb.count(x)==1,x;rb=rb.replace(x,y)
    rb=rb.replace("'Core_recompiled':False,", "'Core_recompiled':False,'Localization_recompiled':False,")
    runner=HERE/'compile_phase2.py';new(runner,rb)
    diffs=[]
    for name,x,y in [('phase2-counting.diff',a,b),('phase2-final.diff',fa,fb),('phase2-runner.diff',ra,rb)]:
        p=HERE/name;new(p,''.join(difflib.unified_diff(x.splitlines(keepends=True),y.splitlines(keepends=True),
            fromfile='frozen-phase1/'+name,tofile='phase2/'+name)));diffs.append(p)
    for p in [Path(__file__),runner]:ast.parse(p.read_text(encoding='utf-8'))
    priorpath=HERE/'phase1-prepared.json';prior=json.loads(priorpath.read_text())
    for r in prior['files']+prior['dependencies']:
        assert item(ROOT/r['path'])['sha256']==r['sha256'],r['path']
    reused=list(prior['reused_oleans'])
    p=ROOT/'tmp/current-s1r-tiny-20261018/phase1-v0/lib/StructuralS1RTiny20261018/Phase1/Localization.olean'
    r=item(p);assert r['sha256']=='bbfc39e593449e8004a48f353840129e7b407677f3b5a4ea334fd496472f02cd'
    r['relative_module_path']='StructuralS1RTiny20261018/Phase1/Localization.olean';reused.append(r)
    targets=[{'module':'StructuralS1RTiny20261018/Phase2/Counting',
        'expected_printed_roots':prior['targets'][1]['expected_printed_roots']},
        {'module':'StructuralS1RTiny20261018/Phase2/Final','expected_printed_roots':prior['targets'][2]['expected_printed_roots']}]
    gate={'authorized':False,'task':'tiny-current-s1R-counting-phase2','prepared_manifest_sha256':'ROOT_INSERT_FROZEN_SHA',
        'allowed_modules':[t['module'] for t in targets],'automatic_repairs_or_retries':0,
        'recompile_passed_prefix':False,'recompile_passed_Core':False,'recompile_passed_Localization':False,
        'manual_report_points_only':{'seconds_per_module':1200,'log_bytes':20000000},
        'no_automatic_timeout_or_logcap':True,'memory_MB':13500,'jobs':1,'stack_bytes':268435456,
        'Nano_or_Comparator_authorized':False}
    gp=HERE/'phase2-gate-template.json';new(gp,json.dumps(gate,indent=2)+'\n')
    deps=[oldcount,oldfinal,ROOT/'StructuralS1RTiny20261018/Phase1/Localization.lean',
        ROOT/'StructuralS1RTiny20261018/Dev/Core.lean',ROOT/'StructuralS1RM20261018/CurrentPrefix.lean',
        priorpath,HERE/'phase1-execution-files.json',ROOT/'tmp/current-s1r-tiny-20261018/phase1-v0/Localization.receipt.json',
        ROOT/'tmp/current-s1r-tiny-20261018/phase1-v0/Counting.log',ROOT/'tmp/setup-20261015/runtime.json']+[ROOT/r['path'] for r in reused]
    manifest={'schema':'tiny-counting-same-theorem-let-cast-repair-phase2-prepared-v1',
        'files':[item(p) for p in [count,final,runner,Path(__file__),gp]+diffs],
        'dependencies':[item(p) for p in deps],'targets':targets,'reused_oleans':reused,
        'Python_executable':prior['Python_executable'],'external_Linux_pins':prior['external_Linux_pins'],
        'same_mathematical_statements':True,'only_known_let_and_Nat_cast_normalization_repaired':True,
        'constants_tree_model_and_witnesses_changed':False,'previous_sources_and_evidence_unchanged':True,
        'prefix_Core_Localization_recompiled':False,'automatic_repairs_or_retries':0,'Lean_runs':0,
        'new_immutable_gate_required':True,'job_directory_absent':True,
        'uncropped_prefix_Core_phase1Loc_newCounting_newFinal_bytes':935224+1003097+12298+count.stat().st_size+final.stat().st_size,
        'command_template':['C:/Python314/python.exe','research-goal-20261018-tiny-runtime-preparation/compile_phase2.py',
            '--gate','ROOT_GATE','--gate-sha256','ROOT_SHA']}
    p=HERE/'phase2-prepared.json';new(p,json.dumps(manifest,indent=2)+'\n')
    print(json.dumps(item(p)));print(json.dumps({'Counting':item(count),'Final':item(final),'runner':item(runner)}))


if __name__=='__main__':main()
