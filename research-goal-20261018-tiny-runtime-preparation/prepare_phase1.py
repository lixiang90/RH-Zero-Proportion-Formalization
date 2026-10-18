"""Prepare only the four known Localization API repairs, preserving v0."""
import ast
import difflib
import hashlib
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent


def item(p):
    b=p.read_bytes()
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}


def new_text(p,s):
    p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('x',encoding='utf-8',newline='\n') as f:f.write(s)


def main():
    assert not (ROOT/'tmp/current-s1r-tiny-20261018/phase1-v0').exists()
    oldloc=ROOT/'StructuralS1RTiny20261018/Dev/Localization.lean'
    oldfinal=ROOT/'StructuralS1RTiny20261018/Dev/Final.lean'
    assert item(oldloc)['sha256']=='8d02de83edfced0a98a9b717a4b6c9de65d9ccc392d914084a59fda7b958f179'
    old=oldloc.read_text(encoding='utf-8')
    changes=[
      ('  exact add_le_add_left hs (pressure g)',
       '  simpa only [Fg, pressure, add_comm] using (add_le_add_left hs (pressure g))'),
      ('  exact add_le_add_left hs _',
       '  simpa only [add_comm] using\n    (add_le_add_left hs ((BS.getD r 0 : ℝ) * g r))')]
    new=old
    for a,b in changes:
        assert new.count(a)==1
        new=new.replace(a,b,1)
    a='    (fun k hk => by simp [rootCl, List.getD_eq_getElem?_getD, hk])'
    b='    (fun k hk => by\n      have hkn : k < 28 := by simpa [PR] using hk\n      interval_cases k <;> rfl)'
    assert new.count(a)==2
    new=new.replace(a,b)
    loc=ROOT/'StructuralS1RTiny20261018/Phase1/Localization.lean';new_text(loc,new)
    before=oldfinal.read_text(encoding='utf-8')
    after=before.replace('import StructuralS1RTiny20261018.Dev.Localization\n',
        'import StructuralS1RTiny20261018.Phase1.Localization\n',1)
    assert after!=before
    final=ROOT/'StructuralS1RTiny20261018/Phase1/Final.lean';new_text(final,after)
    runner0=HERE/'compile_dev.py'
    rt=runner0.read_text(encoding='utf-8')
    replacements={
      'One gated serial Tiny development compile; no dependency recompilation.':'One gated Tiny Localization API-repair compile; reuse proved Core and prefix.',
      "JOB=ROOT/'tmp/current-s1r-tiny-20261018/dev-v0'":"JOB=ROOT/'tmp/current-s1r-tiny-20261018/phase1-v0'",
      "prepared=HERE/'compiler-prepared.json'":"prepared=HERE/'phase1-prepared.json'",
      "gate['task']=='tiny-current-s1R-dev-ordinary-v0'":"gate['task']=='tiny-current-s1R-localization-phase1'",
      "assert gate['recompile_passed_prefix'] is False":"assert gate['recompile_passed_prefix'] is False\n    assert gate['recompile_passed_Core'] is False",
      "'all_four_modules_completed':len(receipts)==4":"'all_three_modules_completed':len(receipts)==3",
      "passed and len(receipts)==4":"passed and len(receipts)==3"}
    for a,b in replacements.items():
        assert rt.count(a)==1,a
        rt=rt.replace(a,b)
    rt=rt.replace("'prefix_recompiled':False,", "'prefix_recompiled':False,'Core_recompiled':False,")
    runner=HERE/'compile_phase1.py';new_text(runner,rt)
    for p in [Path(__file__),runner]:ast.parse(p.read_text(encoding='utf-8'))
    diffs=[]
    for name,a,b in [('phase1-localization.diff',old,new),('phase1-final.diff',before,after),
        ('phase1-runner.diff',runner0.read_text(encoding='utf-8'),rt)]:
        p=HERE/name;new_text(p,''.join(difflib.unified_diff(a.splitlines(keepends=True),b.splitlines(keepends=True),
            fromfile='frozen-v0/'+name,tofile='phase1/'+name)));diffs.append(p)
    oldprep=HERE/'compiler-prepared.json';prior=json.loads(oldprep.read_text(encoding='utf-8'))
    for r in prior['files']+prior['dependencies']:
        assert item(ROOT/r['path'])['sha256']==r['sha256'],r['path']
    reused=[dict(prior['reused_oleans'][0])]
    core=ROOT/'tmp/current-s1r-tiny-20261018/dev-v0/lib/StructuralS1RTiny20261018/Dev/Core.olean'
    cr=item(core)
    assert cr['sha256']=='1a892b6ed20f635d33cc93c3e642c950a7dc56a683d966979c70a345ea0c718a'
    cr['relative_module_path']='StructuralS1RTiny20261018/Dev/Core.olean';reused.append(cr)
    targets=[{'module':'StructuralS1RTiny20261018/Phase1/Localization','expected_printed_roots':[]},
        dict(prior['targets'][2]),{'module':'StructuralS1RTiny20261018/Phase1/Final',
        'expected_printed_roots':prior['targets'][3]['expected_printed_roots']}]
    template={'authorized':False,'task':'tiny-current-s1R-localization-phase1',
        'prepared_manifest_sha256':'ROOT_INSERT_FROZEN_SHA','allowed_modules':[t['module'] for t in targets],
        'automatic_repairs_or_retries':0,'recompile_passed_prefix':False,'recompile_passed_Core':False,
        'manual_report_points_only':{'seconds_per_module':1200,'log_bytes':20000000},
        'no_automatic_timeout_or_logcap':True,'memory_MB':13500,'jobs':1,'stack_bytes':268435456,
        'Nano_or_Comparator_authorized':False}
    templatefile=HERE/'phase1-gate-template.json';new_text(templatefile,json.dumps(template,indent=2)+'\n')
    count=ROOT/'StructuralS1RTiny20261018/Dev/Counting.lean'
    dependencies=[oldloc,oldfinal,count,ROOT/'StructuralS1RTiny20261018/Dev/Core.lean',
        ROOT/'StructuralS1RM20261018/CurrentPrefix.lean',oldprep,HERE/'dev-v0-execution-files.json',
        ROOT/'tmp/current-s1r-tiny-20261018/dev-v0/Core.receipt.json',
        ROOT/'tmp/current-s1r-tiny-20261018/dev-v0/Localization.log',
        ROOT/'tmp/setup-20261015/runtime.json']+[ROOT/r['path'] for r in reused]
    out={'schema':'tiny-localization-same-theorem-API-repair-phase1-prepared-v1',
        'files':[item(p) for p in [loc,final,runner,Path(__file__),templatefile]+diffs],
        'dependencies':[item(p) for p in dependencies],
        'targets':targets,'reused_oleans':reused,
        'Python_executable':prior['Python_executable'],'external_Linux_pins':prior['external_Linux_pins'],
        'same_mathematical_statements':True,'only_four_known_API_goals_repaired':True,
        'model_constants_tree_and_numeric_witness_changes':False,
        'original_Localization_and_Final_and_Core_unchanged':True,
        'Counting_source_unchanged_and_previously_unrun':True,
        'Core_or_prefix_recompiled':False,'automatic_repairs_or_retries':0,'Lean_runs':0,
        'job_directory_absent':True,'new_immutable_gate_required':True,
        'uncropped_prefix_Core_counting_newLocalization_newFinal_bytes':
            935224+1003097+count.stat().st_size+loc.stat().st_size+final.stat().st_size,
        'command_template':['C:/Python314/python.exe','research-goal-20261018-tiny-runtime-preparation/compile_phase1.py',
            '--gate','ROOT_GATE','--gate-sha256','ROOT_SHA']}
    p=HERE/'phase1-prepared.json';new_text(p,json.dumps(out,indent=2)+'\n')
    print(json.dumps(item(p)))
    print(json.dumps({'Localization':item(loc),'Final':item(final),'runner':item(runner)}))


if __name__=='__main__':main()
