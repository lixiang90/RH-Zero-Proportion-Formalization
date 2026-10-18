"""Prepared stdlib integer-certificate verifier relative to frozen F model.

No Sympy, producer import, optimization or source term reconstruction. A separate
source-level independent audit must bind this model to the original FS/rows.
"""
from pathlib import Path
from hashlib import sha256
from fractions import Fraction as F
import argparse
import json
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def pin(p):return sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def dot(a,b):return sum(x*y for x,y in zip(a,b))

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    out=HERE/'integer-certificate-replay.json'
    if args.write_receipt:assert not out.exists()
    start=time.monotonic();result=load(HERE/'result.json');assert result['passed']
    assert result['inputs_sha256_start']==result['inputs_sha256_end']
    for name,expected in result['inputs_sha256_start'].items():assert pin(ROOT/name)==expected
    model=load(HERE/'model.json');cert=load(HERE/'certificate.json')
    assert pin(HERE/'model.json')==result['model_sha256'] and pin(HERE/'certificate.json')==result['certificate_sha256']
    assert pin(HERE/'affine-components.json')==model['affine_components_sha256']
    rows=model['rows'];assert len(rows)==155 and [r['row_id'] for r in rows]==list(range(155))
    assert all(len(r['coefficients'])==10 and sum(r['coefficients'])==0 for r in rows)
    const=int(model['constant']);b=list(map(int,model['position_coefficients']));target=int(model['target'])
    assert len(b)==10 and sum(b)==0
    if cert['kind'] in ['Empty','Lower']:
        ids=cert['row_ids'];weights=list(map(int,cert['integer_weights']))
        assert ids==sorted(set(ids)) and len(ids)==len(weights)
        assert all(0<=i<155 for i in ids) and all(n>0 for n in weights)
        balance=[sum(n*rows[i]['coefficients'][k] for i,n in zip(ids,weights)) for k in range(10)]
        cost=sum(n*rows[i]['rhs'] for i,n in zip(ids,weights))
        if cert['kind']=='Empty':
            assert balance==[0]*10 and cost<0 and int(cert['integer_negative_cost'])==cost
        else:
            den=int(cert['common_denominator']);assert den>0
            assert all(den*b[k]+balance[k]==0 for k in range(10))
            lower=den*const-cost;assert lower>=den*target
            assert int(cert['weighted_integer_lower_bound'])==lower
            assert int(cert['weighted_integer_target'])==den*target
    elif cert['kind']=='Below':
        q=int(cert['point_common_denominator']);z=list(map(int,cert['integer_X']))
        assert q>0 and len(z)==10 and z[0]==0
        assert all(dot(r['coefficients'],z)<=q*r['rhs'] for r in rows)
        assert all(z[i]>=q*i*17*32768 for i in range(1,10))
        value=q*const+dot(b,z);assert value<q*target
        assert value==int(cert['objective_numerator']) and q*target==int(cert['target_numerator'])
    else:raise AssertionError('unknown certificate kind')
    if (HERE/'primary-raw-result.json').exists():
        raw=load(HERE/'primary-raw-result.json');x=[F(0)]+list(map(F,raw['primal']));mu=list(map(F,raw['dual']))
        assert len(x)==10 and len(mu)==155 and all(m>=0 for m in mu)
        assert all(dot(r['coefficients'],x)<=r['rhs'] for r in rows)
        assert all(x[i]>=i*17*32768 for i in range(1,10))
        assert all(b[k]+sum(m*r['coefficients'][k] for m,r in zip(mu,rows))==0 for k in range(10))
        assert F(raw['objective'])==dot(b,x)
        assert const+dot(b,x)==const-sum(m*r['rhs'] for m,r in zip(mu,rows))
    for name,expected in result['inputs_sha256_start'].items():assert pin(ROOT/name)==expected
    record={'schema':'fixed-F-integer-certificate-arithmetic-replay-v1','passed':True,
        'model_sha256':pin(HERE/'model.json'),'certificate_sha256':pin(HERE/'certificate.json'),
        'script_sha256':pin(Path(__file__)),'certificate_kind':cert['kind'],
        'all155_rows_or_full10_dual_balance_verified':True,'sympy_imported':False,'solver_calls':0,
        'source_level_FS_objective_and_row_reconstruction_performed':False,
        'scope':'Integer/rational certificate arithmetic relative to saved model only. Original source/FS/model identity requires separate audit; only one fixed pair is involved.',
        'new_global_joint_floor_proven':False,'new_unconditional_zero_proportion_proven':False,
        'seconds':time.monotonic()-start}
    if args.write_receipt:
        with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(record,f,indent=2);f.write('\n')
    print(json.dumps(record))

if __name__=='__main__':main()
