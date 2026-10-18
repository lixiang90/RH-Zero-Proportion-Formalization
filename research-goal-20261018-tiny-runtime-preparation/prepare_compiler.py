"""Freeze source/runtime identities and AST only; never launch the compiler."""
import ast
import hashlib
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent


def item(p):
    b=p.read_bytes()
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}


def write_new(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(x,f,indent=2);f.write('\n')


def main():
    assert not (ROOT/'tmp/current-s1r-tiny-20261018/dev-v0').exists()
    modules=['Core','Localization','Counting','Final']
    sources=[ROOT/('StructuralS1RTiny20261018/Dev/'+x+'.lean') for x in modules]
    assert item(sources[0])['sha256']=='1e144c848b39c85277af45c590cb0e54e93b2f098d44f5eb40bcb2e1b8d216ac'
    assert item(sources[1])['sha256']=='8d02de83edfced0a98a9b717a4b6c9de65d9ccc392d914084a59fda7b958f179'
    assert item(sources[2])['sha256']=='e1629a96ac6239ae0d216c608c99f6d929c779b8201f4835aa72b125b2923f87'
    py=[HERE/x for x in ['prepare_dev_sources.py','snapshot_trusted_spec.py','compile_dev.py','prepare_compiler.py']]
    for p in py:ast.parse(p.read_text(encoding='utf-8'))
    manifests=[HERE/'dev-source-files.json',
        ROOT/'research-goal-20261018-tiny-localization-preparation/prepared-files.json',
        ROOT/'research-goal-20261018-tiny-counting-preparation/prepared-files.json']
    for p in manifests:
        m=json.loads(p.read_text(encoding='utf-8'))
        for key in ['files','dependencies','read_dependencies','read_only_dependencies']:
            for r in m.get(key,[]):assert item(ROOT/r['path'])['sha256']==r['sha256'],r['path']
    prefix=ROOT/'StructuralS1RM20261018/CurrentPrefix.lean'
    olean=ROOT/'tmp/current-s1r-M-20261018/phaseA1b/lib/StructuralS1RM20261018/CurrentPrefix.olean'
    reused=item(olean)
    assert reused['sha256']=='8a67fa6cd8dbf293b802471bf39fb2cc160130a263191ce1c854d16fc35db692'
    reused['relative_module_path']='StructuralS1RM20261018/CurrentPrefix.olean'
    spec=json.loads((HERE/'runtime-CandidateSpec.json').read_text(encoding='utf-8'))
    assert item(HERE/spec['source_snapshot'])['sha256']==spec['sha256']
    expected={
        'Core':[],'Localization':[],
        'Counting':['StructuralS1RTiny20261018.Counting.'+x for x in
            ['sum_range_pair_lower','summed_of_pair','actual_defect_estimate_of_pair','actual_dyadic_of_pair','actual_cumulative_of_pair']],
        'Final':['AMW.Cert.PC9TinyData.run','RiemannFail.cert_AM',
            'StructuralS1RTiny20261018.Dev.Localization.pair_floor',
            'StructuralS1RTiny20261018.Dev.Final.strict_improvement',
            'StructuralS1RTiny20261018.Dev.Final.actual_dyadic',
            'StructuralS1RTiny20261018.Dev.Final.actual_cumulative']}
    targets=[{'module':'StructuralS1RTiny20261018/Dev/'+x,'expected_printed_roots':expected[x]} for x in modules]
    gate={'schema':'tiny-current-s1R-dev-ordinary-gate-template-v1','authorized':False,
        'task':'tiny-current-s1R-dev-ordinary-v0','prepared_manifest_sha256':'ROOT_INSERT_FROZEN_SHA',
        'allowed_modules':[t['module'] for t in targets],
        'automatic_repairs_or_retries':0,'recompile_passed_prefix':False,
        'manual_report_points_only':{'seconds_per_module':1200,'log_bytes':20000000},
        'no_automatic_timeout_or_logcap':True,'memory_MB':13500,'jobs':1,'stack_bytes':268435456,
        'Nano_or_other_compiler_or_solver_authorized':False}
    write_new(HERE/'gate-template.json',gate)
    own=py+[HERE/'PLAN.zh.md',HERE/'DevCore.diff',HERE/'DevCounting.diff',
        HERE/'inherited-tail.archive.lean.txt',HERE/'runtime-CandidateSpec.snapshot.lean',
        HERE/'runtime-CandidateSpec.json',HERE/'gate-template.json']+sources
    dependencies=manifests+[prefix,olean,ROOT/'tmp/setup-20261015/runtime.json',
        ROOT/'research-goal-20261018-stageM-lean-implementation/phaseA-v0-execution-files.json']
    total=prefix.stat().st_size+sum(x.stat().st_size for x in sources)
    out={'schema':'tiny-current-prefix-reuse-four-module-compiler-prepared-v1',
        'files':[item(p) for p in own],'dependencies':[item(p) for p in dependencies],
        'targets':targets,'reused_oleans':[reused],
        'Python_executable':{'path':str(Path(sys.executable).resolve()),'sha256':hashlib.sha256(Path(sys.executable).read_bytes()).hexdigest()},
        'external_Linux_pins':{
            '/var/tmp/rh-zero-20261015/lean-4.33.0-rc2-linux/bin/lean':'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
            '/var/tmp/rh-zero-20261015/record-verification/modular/lib/ChallengeDeps.olean':'a9127aa6c9a70793124b7b08c16baac0b205c4d717a44a313de812534aa01542',
            '/var/tmp/rh-zero-20261015/record-verification/modular/lib/ChallengeDeps/CandidateSpec.olean':'670b554a94297575edfeb26036162247539f2168c5f5c1ee657c65d305f3866b',
            spec['external_path']:spec['sha256']},
        'AST_only':True,'Lean_runs':0,'new_solver_FS_kernel_or_matrix_runs':0,
        'Core_and_Localization_axioms_deferred_to_Final_transitive_audit':True,
        'uncropped_prefix_and_all_four_sources_bytes':total,'remaining_before_2MB':2000000-total,
        'actual_flattened_file_generated':False,'trusted_tiny_CandidateSpec_prepared':False,
        'official_Comparator_or_Nano_passed':False,'website_submission_ready':False,
        'no_executed_job_directory_exists':True,'new_immutable_execution_gate_required':True,
        'command_template':['C:/Python314/python.exe',
            'research-goal-20261018-tiny-runtime-preparation/compile_dev.py','--gate','ROOT_GATE','--gate-sha256','ROOT_SHA']}
    final=HERE/'compiler-prepared.json';write_new(final,out)
    print(json.dumps(item(final)))
    print(json.dumps({'source_bytes':{x.name:x.stat().st_size for x in sources},'uncropped_total':total,'remaining':2000000-total}))


if __name__=='__main__':main()
