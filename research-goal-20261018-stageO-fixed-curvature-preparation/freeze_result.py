"""Byte/scalar-metadata freeze only; no curvature or network mathematical replay."""
from pathlib import Path
from hashlib import sha256
import json
import os
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
PREPARED='e6cfb7330076dccd9a11ca246c41d1ac293ac5bbf8ede2d20b91c46d60f6888f'
GATE='research-goal-20261016/gates/stageO-fixed-original-curvature-20261018.json'
GATE_SHA='f17cd64c0889038d7dad678a93960a276f585dda294d9cdd28d0edd03b69fa10'
def pin(p):
    h=sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def write(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def main():
    assert not (HERE/'files.json').exists() and not (HERE/'freeze-receipt.json').exists()
    assert pin(HERE/'prepared-files.json')==PREPARED and pin(ROOT/GATE)==GATE_SHA
    prep=load(HERE/'prepared-files.json')
    for item in prep['files']:
        p=ROOT/item['path'];assert pin(p)==item['sha256'] and p.stat().st_size==item['bytes']
    result=load(HERE/'result.json');terminal=load(HERE/'terminal.json')
    assert terminal['exit_code']==0 and terminal['child_launches']==1 and terminal['limit_stop'] is None
    assert terminal['inputs_unchanged_after_terminal'] and terminal['external_runtime_unchanged_after_terminal']
    assert result['original_REG_cell_queries']==23 and result['positive_raw_dual_anchor_rows']==result['covered_anchor_rows']==49
    assert result['conditional_fixed_pair_floor_closes'] is True and result['exact_Laplace_solve_calls']==1
    assert result['new_subdivision_kernel_anchors_FS_LP_or_Lean_runs']==0
    assert pin(HERE/'curvature-packet.json')==result['packet_sha256']==terminal['curvature_packet_sha256']
    receipt={'schema':'O-one-terminal-byte-and-saved-scalar-freeze-v1','byte_identity_passed':True,
        'session_id':38623,'parent_pid':25112,'child_pid':47068,'actual_exit_code':0,
        'original_REG_cell_queries':23,'positive_raw_dual_anchor_rows':49,'covered_anchor_rows':49,
        'stored_conditional_fixed_pair_floor_closes':True,'curvature_packet_sha256':result['packet_sha256'],
        'prepared_manifest_sha256':PREPARED,'gate_path':GATE,'gate_sha256':GATE_SHA,
        'new_math_in_freezer':False,'external_independent_math_audit_pending':True,
        'actual_Lean_transfer_or_whole_domain_or_unconditional_kappa_proven':False}
    write(HERE/'freeze-receipt.json',receipt)
    owned=[p for p in sorted(HERE.iterdir()) if p.is_file() and p.name!='files.json']
    manifest={'schema':'O-fixed1322606-original-REG-curvature-complete-one-attempt-v1','files':[row(p) for p in owned],
        'read_only_dependencies':prep['read_only_dependencies']+[row(ROOT/GATE)],
        'external_read_only_runtime_files':prep['external_read_only_runtime_files'],
        'prepared_manifest_sha256':PREPARED,'fixed_G_index':1322606,'scope':'Fixed pair conditional curvature certificate, not whole domain.',
        'external_independent_math_audit_pending':True,'automatic_retry':False,
        'actual_Lean_or_new_unconditional_ratio_or_website_acceptance_proven':False}
    write(HERE/'files.json',manifest)
    print(json.dumps({'manifest':row(HERE/'files.json'),'owned_files':len(owned),
        'owned_bytes':sum(p.stat().st_size for p in owned),'new_math_in_freezer':False}))
if __name__=='__main__':main()
