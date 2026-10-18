"""O static AST/byte identity and literal REG inventory, no functions imported."""
from pathlib import Path
from hashlib import sha256
import ast
import json
import os
import re
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
def write(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def literal(tree,name):
    nodes=[n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id==name for t in n.targets)]
    assert len(nodes)==1;return ast.literal_eval(nodes[0].value)
def main():
    for name in ['preparation.json','prepared-files.json','REG-literal-inventory.json','started.json','result.json','launch.json','curvature-packet.json']:
        assert not (HERE/name).exists(),('prepare_before_any_execution',name)
    names=['cellA_quantitative.py','weighted_network.py','audit_once.py','run_once.py','prepare_freeze.py']
    trees={n:ast.parse((HERE/n).read_text(encoding='utf-8'),filename=str(HERE/n)) for n in names}
    deps={}
    def add(name,h=None,n=None):
        p=(ROOT/name).resolve();assert p.is_relative_to(ROOT);actual=pin(p)
        if h is not None:assert actual==h,(name,actual,h)
        if n is not None:assert p.stat().st_size==n
        if name in deps:assert deps[name]['sha256']==actual
        deps[name]=row(p)
    pins=literal(trees['audit_once.py'],'PINS')
    for name,h in pins.items():
        add(name,h)
        if Path(name).name in ['files.json','audit-files.json']:
            for field in ['files','read_only_dependencies','dependencies']:
                for item in load(ROOT/name).get(field,[]):add(item['path'],item['sha256'],item.get('bytes'))
    text=(ROOT/'research-goal-20261018-record-source-audit/snapshot/Solution.lean').read_text(encoding='utf-8')
    match=re.search(r'(?m)^noncomputable def REG : ℕ × ℕ × List \(List ℕ\) := (.*)$',text)
    assert match;A,B,chains=ast.literal_eval(match[1]);assert len(chains)==16
    inventory={'schema':'source-existing-REG-literal-inventory-only-v1',
        'source_sha256':pins['research-goal-20261018-record-source-audit/snapshot/Solution.lean'],
        'declaration_line':text[:match.start()].count('\n')+1,
        'declaration_utf8_sha256':sha256(match[0].encode('utf-8')).hexdigest(),
        'chain_count':16,'literal_chain_lengths':[len(c) for c in chains],
        'elementary_ccell_count':sum(map(len,chains)),
        'curvature_or_guard_evaluations':0,'active_row_or_hull_selection_executions':0}
    write(HERE/'REG-literal-inventory.json',inventory)
    runtime=[]
    for name,h in literal(trees['audit_once.py'],'EXTERNAL_RUNTIME').items():
        p=Path(name);assert pin(p)==h;runtime.append({'path':str(p),'bytes':p.stat().st_size,'sha256':h})
    assert str(Path(sys.executable))==str(Path('C:/Python314/python.exe'))
    receipt={'schema':'O-fixed-curvature-AST-and-byte-only-preparation-v1','passed':True,
        'source_files':[{**row(HERE/n),'AST_parse_passed':True} for n in names],
        'read_only_dependencies':[deps[n] for n in sorted(deps)],'external_read_only_runtime_files':runtime,
        'REG_literal_inventory':inventory,'producer_imports':0,'FS_decode_or_new_FS':0,
        'point_or_kernel_or_curvature_evaluations':0,'matrix_or_linear_solve_or_LP_or_Lean_runs':0,
        'immutable_execution_gate_required':True,'conditional_analytic_transfer_pending':True}
    write(HERE/'preparation.json',receipt)
    owned=names+['SPEC.zh.md','required-gate-fields.json','REG-literal-inventory.json','preparation.json']
    manifest={'schema':'O-fixed1322606-curvature-opportunity-prepared-only-v1','files':[row(HERE/n) for n in owned],
        'read_only_dependencies':[deps[n] for n in sorted(deps)],'external_read_only_runtime_files':runtime,
        'source_REG_literal_elementary_cell_count':inventory['elementary_ccell_count'],
        'mathematical_executions':0,'fixed_anchor_or_curvature_selection_executions':0,
        'actual_quantitative_curvature_or_fixed_pair_payment_proven':False,'immutable_root_gate_pending':True,
        'whole_domain_or_unconditional_kappa_proven':False,'source_runtime_payload_budget':'unknown'}
    write(HERE/'prepared-files.json',manifest)
    print(json.dumps({'prepared_only':True,'manifest':row(HERE/'prepared-files.json'),
        'source_sha256':{n:pin(HERE/n) for n in names},'REG_literal_cells':inventory['elementary_ccell_count'],
        'dependencies':len(deps),'mathematical_executions':0}))
if __name__=='__main__':main()
