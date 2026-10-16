"""Read-only stdlib audit of the exact halfspace split and two negative tests.

Reconstruct all six polynomial localizers and all 330 affine entries from
the frozen parent monomial order.  Verify the rational direction/threshold
and both quadratic witnesses equal -1.  No producer/numerical import.
Default is read-only.  --write-receipt creates an absent receipt once.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;PARENT=ROOT/'research-goal-20261017-quartic'
OUT=HERE/'split-replay.json'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def add(p,q,s=F(1)):
    out=p.copy()
    for m,v in q.items():
        z=out.get(m,F(0))+s*v
        if z:out[m]=z
        else:out.pop(m,None)
    return out
def product(p,q):
    out={}
    for m,a in p.items():
        for n,b in q.items():out=add(out,{tuple(sorted(m+n)):a*b})
    return out
def scaled(p,a):return {m:v*a for m,v in p.items() if v*a}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write-receipt',action='store_true');args=parser.parse_args();began=time.monotonic()
    if args.write_receipt:assert not OUT.exists()
    paths=[Path(__file__),HERE/'split-model.json',PARENT/'quartic-model.json.gz',PARENT/'quartic-files.json',
        PARENT/'quartic-exact-primal.json',PARENT/'quartic-result-replay.json']
    split=json.loads(paths[1].read_bytes());parent=json.loads(gzip.decompress(paths[2].read_bytes()));manifest=json.loads(paths[3].read_bytes())
    proof=json.loads(paths[4].read_bytes());replay=json.loads(paths[5].read_bytes())
    for relative,h in split['source_sha256_start'].items():
        p=ROOT/relative;assert sha(p)==h
        if p not in paths:paths.append(p)
    assert split['source_sha256_start']==split['source_sha256_end']
    for entry in manifest['package_files']+manifest['dependency_files']:assert sha(ROOT/entry['path'])==entry['sha256']
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    assert replay['status']=='strict_exact_shared_quartic_outer_relaxation_independently_verified'
    assert split['parent_manifest_sha256']==sha(PARENT/'quartic-files.json') and split['parent_compressed_model_sha256']==sha(PARENT/'quartic-model.json.gz')
    mon=[tuple(m) for m in parent['monomials']];idx={m:k for k,m in enumerate(mon)};x=list(map(F,proof['rational_714_moments']));mean=x[:9]
    integers=split['direction_integer_numerators'];norm=sum(map(abs,integers));assert norm==split['direction_L1_denominator'] and norm>0
    alpha=[F(z,norm) for z in integers];assert list(map(str,alpha))==split['alpha'] and sum(map(abs,alpha))==1
    threshold=sum(a*b for a,b in zip(alpha,mean));assert str(threshold)==split['threshold'] and -1<threshold<1
    phi={(r,):a for r,a in enumerate(alpha) if a};assert {mon[k]:F(v) for k,v in split['phi_polynomial']}==phi
    cov=[[x[idx[tuple(sorted((r,s))) ]-1]-mean[r]*mean[s] for s in range(9)] for r in range(9)]
    def form(p):return {'constant':str(p.get((),F(0))),
        'coefficients':[[idx[m]-1,str(v)] for m,v in sorted(p.items(),key=lambda z:idx[z[0]]) if m]}
    checked=0;negative=[]
    assert [b['sigma'] for b in split['branches']]==[-1,1]
    for branch in split['branches']:
        sign=branch['sigma'];width=1-sign*threshold;assert str(width)==branch['positive_normalizing_length'] and width>0
        A=scaled(add(phi,{():-threshold}),F(sign)/width);B=scaled(add({():F(1)},phi,F(-sign)),1/width)
        assert add(A,B)=={():F(1)}
        polynomials=[A,B,scaled(product(A,B),F(4))];names=['halfspace_lower','halfspace_upper','halfspace_product']
        for block,p,name in zip(branch['extra_PSD_blocks'],polynomials,names):
            assert block['size']==10 and block['name']==name
            assert {mon[k]:F(v) for k,v in block['multiplier_polynomial']}==p
            entries=[]
            for j in range(10):
                for i in range(j,10):entries.append([i,j,form(product(p,{tuple(sorted(mon[i]+mon[j])):F(1)}))])
            assert entries==block['entries'];checked+=len(entries)
        matrix=[[F(0) for _ in range(10)] for _ in range(10)]
        for i,j,f in branch['extra_PSD_blocks'][0]['entries']:
            matrix[i][j]=matrix[j][i]=F(f['constant'])+sum(F(q)*x[k] for k,q in f['coefficients'])
        w=branch['old_point_exact_negative_witness'];coordinate=w['selected_y_coordinate']
        r=[sum(cov[i][j]*alpha[j] for j in range(9))*sign/width for i in range(9)]
        assert matrix[0][0]==0 and matrix[0][1:]==r and r[coordinate]!=0
        assert str(r[coordinate])==w['B0j'] and str(matrix[coordinate+1][coordinate+1])==w['Bjj']
        assert -r[coordinate]**2==F(w['principal_2x2_determinant'])<0
        v=list(map(F,w['vector']));assert len(v)==10 and v[coordinate+1]==1
        assert v[0]==-(matrix[coordinate+1][coordinate+1]+1)/(2*r[coordinate])
        quadratic=sum(v[i]*matrix[i][j]*v[j] for i in range(10) for j in range(10))
        assert quadratic==F(w['quadratic_value'])==-1;negative.append(str(quadratic))
    assert checked==330 and not any(n.split('.')[0] in ['numpy','scipy','scs'] for n in sys.modules)
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==initial
    result={'scope':__doc__,'status':'exact_halfspace_cover_localizers_and_two_negative_witnesses_verified',
        'source_sha256_start':initial,'source_sha256_end':final,'all_sources_unchanged':True,
        'path':split['path'],'alpha':split['alpha'],'threshold':split['threshold'],'branch_count':2,
        'extra_localizers_checked':6,'affine_PSD_entries_checked':checked,'exact_old_point_quadratic_values':negative,
        'parent_constraints_unchanged':True,'parent_analytic_hypotheses_unchanged':True,'pure_stdlib_replay':True,
        'solver_calls':0,'Lean_invocations':0,'cell_exclusion_proven':False,'new_zero_proportion_proven':False,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    if args.write_receipt:OUT.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:result[k] for k in ['status','affine_PSD_entries_checked','exact_old_point_quadratic_values','elapsed_milliseconds']}),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
