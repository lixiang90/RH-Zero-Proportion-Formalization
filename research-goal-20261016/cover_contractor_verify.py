"""Independent stdlib-only verifier for KKT-only interval contractions.

Checks integer derivative combinations supported strictly inside the original
orthant, scalar Taylor errors, both flow bounds, outward rounded coordinate
bounds, and full difference-constraint closure. It preserves KKT points;
it does not claim a pointwise cover of every point in the old cell.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib
from cover_correlated_verify import make_table, verify as verify_exclusion
from cover_correlated_replay import a, SC, DS

def ceil(x):return -((-x.numerator)//x.denominator)

def flow_bound(state,coeff,flow):
    desired=[-coeff[0]]+[coeff[i-1]-coeff[i] for i in range(1,9)]+[coeff[8]]
    balance=[0]*10;cost=0
    for i,j,y,u in flow['nonzero_flow']:
        y=int(y);assert y>=0 and i!=j and u==a.edge_value(state,i,j)
        balance[i]+=y;balance[j]-=y;cost+=y*u
    assert balance==desired==list(map(int,flow['divergence'])) and cost==int(flow['cost'])
    # This is a certified lower bound for sum coeff_i*q_i. Optimality is
    # unnecessary; a nonnegative feasible flow and exact balance suffice.
    return -cost

def close(state):
    lo,hi=state
    if any(l>u for l,u in zip(lo,hi)):return None
    d=[[a.edge_value(state,i,j) for j in range(10)] for i in range(10)]
    for k in range(10):
        for i in range(10):
            for j in range(10):d[i][j]=min(d[i][j],d[i][k]+d[k][j])
    if any(d[i][i]<0 for i in range(10)):return None
    new=[[-d[j][i] for i,j in a.PAIRS],[d[i][j] for i,j in a.PAIRS]]
    a.closure_valid(new);return new

def verify_step(state,step,params,table):
    scalar=make_table(table);a.closure_valid(state)
    assert step['old_cell']==[list(state[0]),list(state[1])]
    bs=params['b_numerators'];terms=[tuple(t) for t in params['a_upper'] if t[2]]
    lower=list(state[0]);upper=list(state[1]);indices=set();sep=123*SC//128
    for cert in step['certificates']:
        i=cert['coordinate'];assert 0<=i<9 and i not in indices and state[0][i]>sep;indices.add(i)
        direction=list(map(int,cert['direction']));assert len(direction)==9
        # Both signs are permitted only at strictly interior coordinates.
        assert all(v==0 or state[0][k]>sep for k,v in enumerate(direction))
        assert len(cert['scalar_affine_data'])==len(terms)
        data=[scalar.check(state[0][a.INDEX[l,r]],state[1][a.INDEX[l,r]],row)
              for (l,r,w),row in zip(terms,cert['scalar_affine_data'])]
        C=2*SC*sum(b*DS*v for b,v in zip(bs,direction));E=0;coeff=[0]*9
        for (l,r,w),(anchor,m0,m1,err,kind) in zip(terms,data):
            c=sum(direction[l:r]);C+=w*c*(2*SC*m0-m1*anchor);E+=2*SC*w*abs(c)*err
            for k in range(l,r):coeff[k]+=2*w*c*m1
        assert C==int(cert['constant']) and E==int(cert['error']) and coeff==list(map(int,cert['coefficient']))
        tau=coeff[i];assert tau>0
        other=coeff.copy();other[i]=0
        minimum=flow_bound(state,other,cert['minimum_flow'])
        maximum=-flow_bound(state,[-v for v in other],cert['maximum_flow'])
        assert minimum==int(cert['other_minimum']) and maximum==int(cert['other_maximum'])
        real_lower=F(-E-C-maximum,tau);real_upper=F(E-C-minimum,tau)
        assert real_lower==F(cert['lower_rational']) and real_upper==F(cert['upper_rational'])
        newlo=max(state[0][i],real_lower.numerator//real_lower.denominator)
        newhi=min(state[1][i],ceil(real_upper))
        assert newlo==cert['new_lower'] and newhi==cert['new_upper']
        lower[i]=newlo;upper[i]=newhi
    assert indices
    expected=close([lower,upper]);actual=step['new_cell']
    assert expected==actual,('KKT contraction closure mismatch',expected,actual)
    return expected

def verify_chain(state,result,params,table):
    scalar=make_table(table);original=[list(state[0]),list(state[1])]
    assert len(result['steps'])==result['iterations']
    for step in result['steps']:
        assert state is not None
        state=verify_step(state,step,params,scalar)
    if result.get('excluded'):
        assert state is not None
        verify_exclusion(state,result['excluded'],params,scalar)
    return {'passed':True,'iterations':len(result['steps']),'empty':state is None,
      'newly_excluded':bool(result.get('excluded')),'final_cell':state,
      'KKT_points_only':True,'pointwise_coverage_asserted':False}

def source_hashes():
    import cover_correlated_verify as verifier
    return {'contractor_verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),**verifier.source_hashes()}
