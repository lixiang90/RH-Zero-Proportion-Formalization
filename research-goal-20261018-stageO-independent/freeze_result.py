"""Freeze existing terminal evidence; hash/metadata only, no math imports."""
from hashlib import sha256
import json
import os
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def digest(p):return sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf8'))
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':digest(p)}
def main():
    assert not (HERE/'audit-files.json').exists()
    prep=load(HERE/'prepared-files.json')
    assert digest(HERE/'prepared-files.json')=='1a3778c64343e2930e94d7a4cd250b689b7b7285ed957c9c43b0d513e6cbc00c'
    for r in prep['files']+prep['read_only_dependencies']:
        p=(ROOT/r['path']).resolve();assert p.is_relative_to(ROOT)
        assert digest(p)==r['sha256'] and p.stat().st_size==r['bytes']
    started=load(HERE/'started.json');review=load(HERE/'independent-review.json');terminal=load(HERE/'terminal.json')
    assert review['passed'] is True and review['fixed_G_index']==1322606
    assert terminal['exit_code']==0 and terminal['limit_stop'] is None and terminal['child_launches']==1
    assert started['inputs_sha256']==review['inputs_sha256_start']==review['inputs_sha256_end']==terminal['inputs_sha256_end_after_terminal']
    assert review['conditional_fixed_pair_floor_closes'] is True and review['global_floor_or_new_kappa_proven'] is False
    assert review['new_linear_solve_LP_RREF_FS_anchor_kernel_Lean_runs']==0
    assert not (HERE/'failure.json').exists() and not (HERE/'stderr.log').read_bytes()
    rt=prep['runtime'];assert digest(Path(rt['executable']))==rt['sha256']
    for r in rt['additional_files']:assert digest(Path(r['path']))==r['sha256']
    deps=[{'path':p,'sha256':h,'bytes':(ROOT/p).stat().st_size} for p,h in sorted(started['inputs_sha256'].items())]
    out={'schema':'O-independent-fixed-curvature-terminal-audit-files-v1',
        'files':[row(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name!='audit-files.json'],
        'read_only_dependencies':deps,'runtime':rt,'unique_child_terminal':True,
        'passed':True,'scope':review['scope'],'conditional_fixed_pair_only':True,
        'whole_domain_floor_or_new_kappa_proven':False}
    with (HERE/'audit-files.json').open('x',encoding='utf8') as f:json.dump(out,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
    print(json.dumps({'manifest':row(HERE/'audit-files.json'),'receipt':row(HERE/'independent-review.json'),
        'files':len(out['files']),'closed_bytes':sum(r['bytes'] for r in out['files'])}))
if __name__=='__main__':main()
