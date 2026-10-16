"""Exact membership API for the new-window 69 coherent Gram basins.

The basin bounds are finite rational certificates, separately replayed.
Their actual-kernel Taylor/curvature bridge remains a Lean obligation.
Membership itself uses only integer inequalities on all positive-weight spans.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json
HERE=Path(__file__).parent;ROOT=HERE.parent;SC=32768
PAIRS=[(i,i+1) for i in range(9)]+[(i,j) for i in range(9) for j in range(i+2,10)]
INDEX={p:k for k,p in enumerate(PAIRS)}
_registry=None

def make_gram_registry(path=HERE/'cover-newwindow-gram.json'):
    path=Path(path);raw=path.read_bytes();doc=json.loads(raw)
    params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    assert doc['receipt']['radius']=='21/100' and doc['receipt']['patterns']==69
    terms=[(i,j) for i,j,a in params['a_upper'] if a]
    lookup={tuple(r['integer_gaps']):(k,r) for k,r in enumerate(doc['results'])}
    assert len(lookup)==69
    return {'sha256':hashlib.sha256(raw).hexdigest(),'parameter_sha256':doc['receipt']['parameter_sha256'],
      'Taylor_table_sha256':doc['receipt']['Taylor_table_sha256'],'curvature_source_sha256':doc['receipt']['curvature_source_sha256'],
      'terms':terms,'lookup':lookup}

def gram_basin(state,floor='221/25000',registry=None):
    global _registry
    if registry is None:
        if _registry is None:_registry=make_gram_registry()
        registry=_registry
    lo,hi=state
    integers=tuple((lo[i]+hi[i]+SC)//(2*SC) for i in range(9))
    item=registry['lookup'].get(integers)
    if item is None:return None
    index,row=item
    if F(row['lower_bound'])<F(floor):return None
    for i,j in registry['terms']:
        n=sum(integers[i:j]);z=INDEX[i,j]
        if 100*lo[z]<SC*(100*n-21) or 100*hi[z]>SC*(100*n+21):return None
    return {'kind':'coherent_Gram_basin','pattern_index':index,'integer_gaps':list(integers),
      'lower_bound':row['lower_bound'],'requested_floor':str(F(floor)),'radius':'21/100','Gram_certificate_sha256':registry['sha256']}

def verify(state,result,floor,registry=None):
    expected=gram_basin(state,floor,registry)
    assert expected is not None and expected==result
    return {'passed':True,'positive_weight_span_membership_checked':True,'actual_kernel_Lean_bridge_complete':False}
