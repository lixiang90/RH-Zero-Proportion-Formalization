"""Stable stdlib-only verifier API for mixed minimizer covers.

make_table(table_json_or_path) prepares the independently evaluated Taylor
data once. verify(state,result,params,table) checks a correlated descent
witness against that prepared table and the exact pressure/pair parameters.
This verifies finite rational arithmetic; actual-kernel and KKT Lean bridges
remain explicit analytic obligations.
"""
from pathlib import Path
import hashlib, json
from cover_correlated_replay import ScalarReplay, SC, DS, a

def make_table(table_json_or_path):
    if isinstance(table_json_or_path,ScalarReplay):return table_json_or_path
    if isinstance(table_json_or_path,(str,Path)):
        table_json_or_path=json.loads(Path(table_json_or_path).read_bytes())
    return ScalarReplay(table_json_or_path)

def source_hashes():
    import cover_correlated_replay as helper
    return {'verifier_api_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'verifier_helper_sha256':hashlib.sha256(Path(helper.__file__).read_bytes()).hexdigest(),
      'geometry_helper_sha256':hashlib.sha256(Path(a.__file__).read_bytes()).hexdigest()}

def verify(state,result,params,table):
    scalar=make_table(table);a.closure_valid(state)
    bs=params['b_numerators'];terms=[tuple(t) for t in params['a_upper'] if t[2]]
    D=params.get('denominator',10**10);assert D==10**10
    assert len(bs)==9 and len(terms)==len(result['scalar_affine_data'])
    direction=list(map(int,result['direction']));assert len(direction)==9
    sep=123*SC//128;assert all(v>=0 or state[0][i]>sep for i,v in enumerate(direction))
    data=[scalar.check(state[0][a.INDEX[i,j]],state[1][a.INDEX[i,j]],r)
          for (i,j,w),r in zip(terms,result['scalar_affine_data'])]
    constant=2*SC*sum(b*DS*v for b,v in zip(bs,direction));error=0;coeff=[0]*9
    for (i,j,w),(anchor,m0,m1,err,kind) in zip(terms,data):
        c=sum(direction[i:j]);constant+=w*c*(2*SC*m0-m1*anchor);error+=2*SC*w*abs(c)*err
        for k in range(i,j):coeff[k]+=2*w*c*m1
    flow=result['exact_flow']
    assert constant==int(flow['constant']) and error==int(flow['error']) and coeff==list(map(int,flow['coefficient']))
    desired=[coeff[0]]+[coeff[i]-coeff[i-1] for i in range(1,9)]+[-coeff[8]];balance=[0]*10;cost=0
    for i,j,y,u in flow['flow']['nonzero_flow']:
        y=int(y);assert y>=0 and i!=j and u==a.edge_value(state,i,j)
        balance[i]+=y;balance[j]-=y;cost+=y*u
    assert balance==desired==list(map(int,flow['flow']['divergence']))
    assert cost==int(flow['flow']['cost']) and -cost==int(flow['negative_maximum'])
    upper=constant+error+cost
    assert upper==int(result['upper_numerator'])<0
    assert int(result['denominator'])==2*SC*D*DS
    return {'passed':True,'strict_integer_margin':str(-upper),'affine_terms':sum(row[4]=='affine' for row in data),
      'scalar_terms':len(data),'flow_edges':len(flow['flow']['nonzero_flow'])}
