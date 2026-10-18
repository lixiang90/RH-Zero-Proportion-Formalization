"""Prepare an import-layout-only runner repair. No Lean invocation."""
import ast
import difflib
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent


def item(p):
    b=p.read_bytes();return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}


def write(p,s):
    with p.open('x',encoding='utf-8',newline='\n') as f:f.write(s)


def main():
    prior=HERE/'phaseA1-prepared.json'
    assert item(prior)['sha256']=='67ab88cbd1c007aabc95cb507898dc5a8c75f29b3a7f22d87140445a1c3a64e2'
    prep=json.loads(prior.read_text(encoding='utf-8'))
    oldpath=HERE/'compile_phaseA1.py'
    assert item(oldpath)['sha256']==next(x for x in prep['files'] if x['path']==oldpath.relative_to(ROOT).as_posix())['sha256']
    old=oldpath.read_text(encoding='utf-8')
    new=old.replace('import os\n','import os\nimport shutil\n')
    new=new.replace("'stageM-actual-Lean-phaseA1'","'stageM-actual-Lean-phaseA1b'")
    new=new.replace("'phaseA1-prepared.json'","'phaseA1b-prepared.json'")
    new=new.replace("'tmp/current-s1r-M-20261018/phaseA1'","'tmp/current-s1r-M-20261018/phaseA1b'")
    anchor="    lib=job/'lib';lib.mkdir()\n"
    addition='''    # Lean selects a namespace root, not a per-module fallback across libraries.
    # Populate this isolated namespace using the already validated ordinary olean.
    for entry in prep['reused_local_olean_files']:
        source=ROOT/entry['path']
        assert sha(source)==entry['sha256']
        destination=lib/entry['relative_module_path']
        destination.parent.mkdir(parents=True,exist_ok=True)
        assert not destination.exists()
        shutil.copy2(source,destination)
        assert sha(destination)==entry['sha256']
'''
    assert new.count(anchor)==1;new=new.replace(anchor,anchor+addition)
    path=HERE/'compile_phaseA1b.py';write(path,new)
    ast.parse(new,filename=str(path))
    ast.parse(Path(__file__).read_text(encoding='utf-8'),filename=__file__)
    write(HERE/'phaseA1b-runner.diff',''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='compile_phaseA1.py',tofile='compile_phaseA1b.py')))
    folder=ROOT/'tmp/current-s1r-M-20261018/lib/StructuralS1RM20261018'
    actual=sorted(p.name for p in folder.iterdir() if p.is_file())
    assert actual==['CurrentPrefix.olean'],actual
    olean=folder/'CurrentPrefix.olean'
    info=item(olean)
    assert info['sha256']=='8a67fa6cd8dbf293b802471bf39fb2cc160130a263191ce1c854d16fc35db692'
    inventory={'directory':folder.relative_to(ROOT).as_posix(),'files':[info],
        'CurrentPrefix_sidecar_files_present':[],
        'interpretation':'The fixed ordinary compiler generated only CurrentPrefix.olean; no .ilean/.private/.server sidecar is present in this output directory. Copy the exact ordinary olean without recompilation.'}
    write(HERE/'phaseA1b-import-inventory.json',json.dumps(inventory,indent=2)+'\n')
    deps=prep['dependencies']+[item(prior),item(HERE/'phaseA1-execution-files.json')]
    # Bind the identical, previously import-blocked source as a runtime dependency.
    q=ROOT/'StructuralS1RM20261018/PhaseA1/QuantizedComponent.lean'
    deps.append(item(q))
    r={'schema':'M-phaseA1b-import-layout-only-prepared-v1',
        'files':[item(p) for p in [path,Path(__file__),HERE/'phaseA1b-runner.diff',HERE/'phaseA1b-import-inventory.json']],
        'dependencies':deps,'Python_executable':prep['Python_executable'],
        'reused_prefix_olean_sha256':info['sha256'],
        'reused_local_olean_files':[dict(info,relative_module_path='StructuralS1RM20261018/CurrentPrefix.olean')],
        'source_statements_and_proofs_changed':False,'repeat_CurrentPrefix':False,
        'targets':prep['targets'],'automatic_repairs_or_retries':0,'Lean_runs':0,
        'command_template':[prep['Python_executable']['path'],
            'research-goal-20261018-stageM-lean-implementation/compile_phaseA1b.py',
            '--gate','ROOT_GATE_PATH','--gate-sha256','ROOT_GATE_SHA'],
        'new_immutable_gate_required':True,'B2_compile_authorized':False}
    out=HERE/'phaseA1b-prepared.json';write(out,json.dumps(r,indent=2)+'\n')
    print(json.dumps(item(out)))


if __name__=='__main__':main()
