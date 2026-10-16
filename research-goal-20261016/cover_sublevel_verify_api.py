"""Independent target-explicit verifier for sublevel contractions.

Scalar minorants are independently reassembled by the previously replayed
finite Fraction oracle checker. Geometry, all multiplier/flow inequalities,
outward rational rounding and closure are checked without any optimizer.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import cover_sublevel_verify as helper
from cover_contractor_verify import flow_bound,close
from cover_correlated_replay import a

g=helper.g

def ceil(x):return -((-x.numerator)//x.denominator)

def verify_step(state,step,target):
    target=int(target);assert step['old_cell']==state
    C,coeff,_=helper.minorant(state,step['minorant']);lower=state[0].copy();upper=state[1].copy();seen=set()
    for cert in step['certificates']:
        z=cert['axis'];sign=cert['sign'];p=cert['multiplier_numerator'];K=cert['multiplier_denominator']
        assert 0<=z<45 and sign in [1,-1] and p>0 and K>0 and (z,sign) not in seen;seen.add((z,sign))
        i,j=a.PAIRS[z]
        combined=[p*g.SC*c+(sign*K*g.DEN if i<=k<j else 0) for k,c in enumerate(coeff)]
        value=p*g.SC*C+flow_bound(state,combined,cert['flow']);assert value==int(cert['minimum_numerator'])
        bound=F(value-p*g.SC*target,K*g.DEN) if sign==1 else F(p*g.SC*target-value,K*g.DEN)
        assert bound==F(cert['bound'])
        newlo=max(lower[z],bound.numerator//bound.denominator) if sign==1 else lower[z]
        newhi=min(upper[z],ceil(bound)) if sign==-1 else upper[z]
        assert newlo==cert['new_lower'] and newhi==cert['new_upper']
        lower[z]=newlo;upper[z]=newhi
    assert seen
    refined=close([lower,upper]);assert refined==step['new_cell']
    return refined

def source_hashes():
    return {'sublevel_verifier_api_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'sublevel_verifier_helper_sha256':hashlib.sha256(Path(helper.__file__).read_bytes()).hexdigest()}
