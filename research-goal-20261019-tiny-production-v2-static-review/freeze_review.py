"""Freeze independent static source review. No producer import/execution."""
import ast
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
TARGET = ROOT/'research-goal-20261019-tiny-production-preparation-v2'
PIN = 'f2ab9d281bf39769da08280f40d9369e9b9ffc2f51c57acccbb116999daa9d74'

def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''): h.update(b)
    return h.hexdigest()

def row(p):
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}

def write(name,obj):
    with (HERE/name).open('x',encoding='utf-8',newline='\n') as f:
        json.dump(obj,f,ensure_ascii=False,indent=2);f.write('\n')

def main():
    assert not (HERE/'review.json').exists() and not (HERE/'files.json').exists()
    prepared=TARGET/'prepared-files.json'
    assert sha(prepared)==PIN
    obj=json.loads(prepared.read_text(encoding='utf-8'))
    bound={str(prepared.relative_to(ROOT)):PIN}
    for r in obj['files']+obj['dependencies']:
        p=ROOT/r['path'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
        bound[r['path']]=r['sha256']
    paths=[TARGET/'run_production.py',TARGET/'windows_generate.py',TARGET/'adapt_v2.py',TARGET/'freeze_static.py']
    parsed={p.name:ast.parse(p.read_text(encoding='utf-8'),filename=str(p)) for p in paths}
    tree=parsed['run_production.py']
    methods={n.name:n.lineno for n in ast.walk(tree) if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef))}
    script=(TARGET/'run_production.py').read_text(encoding='utf-8')
    for literal in [
      "self.t0 = time.monotonic()", "self.deadline = self.t0 + BUDGET",
      "self.bind_native_tools(gate, config)", "assert not list((self.work / 'lib').rglob('*'))",
      "modules = ['ChallengeDeps', 'ChallengeDeps.CandidateSpec', 'Challenge.Candidate', 'Solution.Candidate']",
      "'num_threads': 0", "'unsafe_permit_all_axioms': False",
      "'unpermitted_axiom_hard_error': True", "self.run('nanoda'",
      "write_new(self.work / 'deadline-receipt.json', final)",
      "write_new(self.mirror / 'terminal.json'", "self.remaining()"]:
        assert literal in script,literal
    cfg=json.loads((TARGET/'configuration.json').read_text(encoding='utf-8'))
    assert cfg['flatten_prepared_sha256']=='2b77159157e500b0177c3c2294860830a495248ce3e3b216a813524032509d72'
    assert cfg['local_nanoda_threads']==0
    assert cfg['preinstalled_trusted_native_tools_required'] is True
    assert cfg['trusted_tools_recompiled_in_proof_attempt'] is False
    additional=[
      ROOT/'tmp/setup-20261015/packages/lean4export/Main.lean',
      ROOT/'tmp/setup-20261015/packages/lean4export/Export.lean',
      ROOT/'tmp/setup-20261015/packages/lean4export/Export/Parse.lean',
      ROOT/'tools/ComparatorCoreAudit.lean',
      ROOT/'research-goal-20261019-native-tools-preparation/lakefile.toml.in',
      ROOT/'research-goal-20261019-nanoda-thread-static-review/REVIEW.zh.md']
    for p in additional: bound[p.relative_to(ROOT).as_posix()]=sha(p)
    maintext=additional[0].read_text(encoding='utf-8')
    assert 'initSearchPath (← findSysroot)' in maintext and 'importModules imports {}' in maintext
    assert 'supportInterpreter = true' in additional[4].read_text(encoding='utf-8')
    assert all(sha(ROOT/name)==expected for name,expected in bound.items())
    write('review.json',{
      'schema':'native-fullcold-v2-independent-static-review-v1',
      'reviewed_prepared_sha256':PIN,'static_review_passed':True,
      'definite_scope_weakening_or_path_bug_found':False,
      'method_source_lines':methods,
      'scope':['all runner and diff/configuration/helper','fresh four-module complete cold compile',
        'native nine-source/ELF/runtime installation binding','dynamic fresh module import interface',
        'same three official roots/primitives/defaultkernel','serial Nano0 full replay',
        'one t0 before pin checks/generation through final fsynced receipts'],
      'dynamic_installation_status': 'Not executed or independently rehashed here; future gate binds root-confirmed successful installation',
      'static_success_does_not_predict_total_runtime':True,
      'runtime_or_artifact_evaluation_performed':False,'producer_imported_or_executed':False,
      'generator_Lean_export_Nano_network_math_runs':0,
      'inputs_unchanged':True,'official_website_acceptance':False,
      'new_execution_authorization_or_extra_gate_added':False})
    write('files.json',{
      'schema':'native-fullcold-v2-static-review-files-v1',
      'files':[row(HERE/'REVIEW.zh.md'),row(HERE/'freeze_review.py'),row(HERE/'review.json')],
      'read_dependencies':[row(ROOT/name) for name in sorted(bound)],
      'scope':'Independent static review only; no runtime verification or acceptance claim'})
    print(json.dumps({'static_review_passed':True,'manifest_sha256':sha(HERE/'files.json')}))

if __name__=='__main__':main()
