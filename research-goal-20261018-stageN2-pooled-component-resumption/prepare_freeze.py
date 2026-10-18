"""N2 preparation: AST, immutable bytes and saved scalar metadata only."""
from pathlib import Path
from hashlib import sha256
import ast
import json
import os
import sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def pin(p):
    h=sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def write(p,v):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(v,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def literal(tree,name):
    matches=[n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id==name for t in n.targets)]
    assert len(matches)==1;return ast.literal_eval(matches[0].value)
def main():
    for name in ['preparation.json','prepared-files.json','started.json','launch.json','result.json','failure.json',
        'recovery.json','progress-commits.jsonl','case-records.jsonl.gz']:
        assert not (HERE/name).exists(),('preparation_before_any_execution',name)
    names=['resume_once.py','run_once.py','prepare_freeze.py'];trees={}
    for name in names:trees[name]=ast.parse((HERE/name).read_text(encoding='utf-8'),filename=str(HERE/name))
    # Pure source identity, not importing any mathematical module/function.
    assert 'os.replace(' not in (HERE/'resume_once.py').read_text(encoding='utf-8')
    expected=literal(trees['resume_once.py'],'PINS');deps={}
    def add(name,h=None,n=None):
        p=(ROOT/name).resolve();assert p.is_relative_to(ROOT);actual=pin(p)
        if h is not None:assert actual==h,(name,actual,h)
        if n is not None:assert p.stat().st_size==n
        if name in deps:assert deps[name]['sha256']==actual
        deps[name]=row(p)
    for name,h in expected.items():
        add(name,h);package=load(ROOT/name)
        for field in ['files','read_only_dependencies','dependencies','read_only_existing_references']:
            for item in package.get(field,[]):add(item['path'],item['sha256'],item.get('bytes'))
    old=ROOT/'research-goal-20261018-stageN-complete-component-preparation'
    terminal=load(old/'terminal.json');failure=load(old/'failure.json');prefix=load(old/'prefix.json')
    assert terminal['exit_code']==1 and prefix['committed_records']==675
    assert failure['committed_records']==676 and failure['linprog_calls_started']==675
    assert terminal['inputs_unchanged_after_terminal'] and terminal['external_runtime_unchanged_after_terminal']
    runtime=load(ROOT/'research-goal-20261018-stageM-component-envelope-preparation/external-runtime.json')
    for item in runtime['files']:
        p=Path(item['path']);assert pin(p)==item['sha256'] and p.stat().st_size==item['bytes']
    assert str(Path(sys.executable))==runtime['python_executable']
    cli=[runtime['python_executable'],'-B','-X','utf8',
        'research-goal-20261018-stageN2-pooled-component-resumption/run_once.py','--launch-authorized-same-model-N2',
        '--gate','<ROOT_GATE_PATH>','--gate-sha256','<ROOT_GATE_SHA256>']
    receipt={'schema':'N2-storage-resumption-AST-and-byte-only-preparation-v1','passed':True,
        'source_files':[{**row(HERE/name),'AST_parse_passed':True} for name in names],
        'read_only_dependencies':[deps[n] for n in sorted(deps)],'external_runtime_files':runtime['files'],
        'saved_scalar_metadata':{'old_published':675,'old_in_memory_at_failure':676,'old_LP_calls':675},
        'command_template':cli,'producer_imports':0,'gzip_mathematical_packets_decoded':0,
        'recovery_math_FS_matrix_point_kernel_solver_or_Lean_executions':0,
        'immutable_execution_gate_pending':True,'source_runtime_payload_budget':'unknown'}
    write(HERE/'preparation.json',receipt)
    owned=names+['SPEC.zh.md','required-gate-fields.json','preparation.json']
    manifest={'schema':'N2-same-pooled-model-resumption-prepared-only-v1','files':[row(HERE/n) for n in owned],
        'read_only_dependencies':[deps[n] for n in sorted(deps)],'external_read_only_runtime_files':runtime['files'],
        'old_N_math_and_evidence_unchanged':True,'progress_protocol':'append_only_fsync_commit_chain_no_replace',
        'recovery_or_mathematical_executions':0,'new_solver_calls':0,'immutable_execution_gate_required':True,
        'unconditional_global_floor_or_submission_proven':False}
    write(HERE/'prepared-files.json',manifest)
    print(json.dumps({'prepared_only':True,'manifest':row(HERE/'prepared-files.json'),
        'source_files':{n:pin(HERE/n) for n in names},'dependencies':len(deps),'mathematical_executions':0}))
if __name__=='__main__':main()
