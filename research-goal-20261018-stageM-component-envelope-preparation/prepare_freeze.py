"""M preparation: AST and raw-byte identities only, no scientific imports."""
from pathlib import Path
from hashlib import sha256
import ast
import json
import os
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
SITE=Path('C:/Users/ip/AppData/Roaming/Python/Python314/site-packages')
PYTHON_SHA='3adbbf2af609e206e3ca18cd55fc7c4b52f5c8bb8218dd99fd5a9e50d7a193cd'
def pin(p):return sha256(p.read_bytes()).hexdigest()
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}
def extrow(p):return {'path':str(p),'bytes':p.stat().st_size,'sha256':pin(p)}
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def write(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def assignment(tree,name):
    nodes=[x for x in tree.body if isinstance(x,ast.Assign)
        and any(isinstance(t,ast.Name) and t.id==name for t in x.targets)]
    assert len(nodes)==1;return ast.literal_eval(nodes[0].value)
def main():
    for name in ['preparation.json','prepared-files.json','external-runtime.json','started.json','result.json','launch.json',
        'child.json','terminal.json','failure.json','model.json','scaling.json','primary-call-started.json',
        'raw-result.json','certificate.json','exact-reconstruction.json','original-components.json',
        'known-nonempty-model-witness.json','stdout.log','stderr.log','files.json']:
        assert not (HERE/name).exists(),('preparation_must_precede_any_attempt',name)
    scripts=['envelope_model.py','discover_once.py','run_once.py','freeze_result.py','prepare_freeze.py']
    trees={};parsed=[]
    for name in scripts:
        p=HERE/name;trees[name]=ast.parse(p.read_text(encoding='utf-8'),filename=str(p))
        parsed.append({**row(p),'AST_parse_passed':True})
    deps={}
    def add(name,expected,expected_bytes=None):
        p=(ROOT/name).resolve();assert p.is_relative_to(ROOT) and pin(p)==expected
        if expected_bytes is not None:assert p.stat().st_size==expected_bytes
        if name in deps:assert deps[name]['sha256']==expected
        deps[name]=row(p)
    pins=assignment(trees['discover_once.py'],'PINS')
    for name,expected in pins.items():add(name,expected)
    for name in ['research-goal-20261018-stageI-original-affine-point/files.json',
        'research-goal-20261018-stageI-independent/audit-files.json',
        'research-goal-20261018-nonlinear-remainder-static/delivery-files.json']:
        data=load(ROOT/name)
        for field in ['files','read_only_dependencies']:
            for item in data.get(field,[]):add(item['path'],item['sha256'],item.get('bytes'))
    executable=Path(sys.executable);assert pin(executable)==PYTHON_SHA
    paths=[executable,executable.parent/'python314.dll']
    paths += [SITE/name for name in ['numpy/__init__.py','numpy/version.py',
        'numpy/_core/_multiarray_umath.cp314-win_amd64.pyd','numpy-2.5.2.dist-info/METADATA',
        'scipy/__init__.py','scipy/version.py','scipy-1.18.1.dist-info/METADATA',
        'scipy/optimize/__init__.py','scipy/optimize/_linprog.py','scipy/optimize/_linprog_highs.py',
        'scipy/optimize/_linprog_util.py','scipy/optimize/_highspy/__init__.py',
        'scipy/optimize/_highspy/_highs_wrapper.py','scipy/optimize/_highspy/_core.cp314-win_amd64.pyd',
        'scipy/optimize/_highspy/_highs_options.cp314-win_amd64.pyd']]
    for folder in ['numpy.libs','scipy.libs']:paths+=sorted((SITE/folder).glob('*.dll'))
    assert 'Version: 2.5.2\n' in (SITE/'numpy-2.5.2.dist-info/METADATA').read_text(encoding='utf-8')
    assert 'Version: 1.18.1\n' in (SITE/'scipy-1.18.1.dist-info/METADATA').read_text(encoding='utf-8')
    runtime={'schema':'M-read-only-installed-runtime-identities-v1','python_executable':str(executable),
        'python_version_observed':sys.version,'expected_numpy_version':'2.5.2','expected_scipy_version':'1.18.1',
        'files':[extrow(p) for p in paths],'copied_or_installed':False,'scientific_modules_imported':False,
        'scope':'Critical selected installed source/native/DLL identities for untrusted discovery; not a complete import-closure proof.'}
    write(HERE/'external-runtime.json',runtime)
    gate=load(HERE/'required-gate-fields.json')
    assert assignment(trees['discover_once.py'],'OPTIONS')==gate['solver_options']
    assert gate['fixed_cells']==[0,604] and gate['chart']=='id/rev' and gate['primary_linprog_calls_authorized']==1
    command=[str(executable),'-B','-X','utf8',
        'research-goal-20261018-stageM-component-envelope-preparation/run_once.py','--launch-authorized-fixed-M',
        '--gate','<ROOT_IMMUTABLE_GATE_RELATIVE_PATH>','--gate-sha256','<ROOT_GATE_SHA256>']
    prep={'schema':'M-AST-bytehash-preparation-only-v1','passed':True,'scripts':parsed,
        'read_only_dependencies':[deps[k] for k in sorted(deps)],'runtime_identity_file':row(HERE/'external-runtime.json'),
        'command_template':command,'command_template_sha256':sha256(json.dumps(command,separators=(',',':')).encode()).hexdigest(),
        'producer_parser_math_or_scipy_imports':0,'FS_extractions':0,'point_or_kernel_evaluations':0,
        'matrix_rank_or_model_constructions':0,'linprog_calls':0,'auxiliary_optimization_calls':0,'Lean_runs':0,
        'independent_checker_not_a_producer_mathematical_input':True,'immutable_root_execution_gate_required':True,
        'scope':'Only source AST, version metadata text and byte hashes observed; no mathematical preparation functions executed.'}
    write(HERE/'preparation.json',prep)
    files=[HERE/name for name in scripts+['SPEC.zh.md','required-gate-fields.json','external-runtime.json','preparation.json']]
    manifest={'schema':'M-fixed-original-component-envelope-prepared-only-v1','files':[row(p) for p in files],
        'read_only_dependencies':[deps[k] for k in sorted(deps)],'external_runtime_identity_file':row(HERE/'external-runtime.json'),
        'scientific_or_producer_imports':0,'FS_or_point_or_matrix_or_LP_or_Lean_executions':0,
        'fixed_pair_only':True,'execution_gate_pending':True,'independent_audit_not_a_producer_input':True,
        'new_global_floor_or_kappa_proven':False,'website_source_and_runtime_gate':'unknown'}
    write(HERE/'prepared-files.json',manifest)
    print(json.dumps({'prepared_only':True,'manifest':row(HERE/'prepared-files.json'),
        'owned_package_bytes':sum(p.stat().st_size for p in files),'read_only_dependencies':len(deps),
        'runtime_identity_files':len(paths),'mathematical_executions':0}))

if __name__=='__main__':main()
