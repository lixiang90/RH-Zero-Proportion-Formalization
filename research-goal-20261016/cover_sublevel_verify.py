"""Independent arithmetic replay for exact-flow sublevel hull contraction.

Recomputes every scalar mixture and its capacity, every flow divergence and
cost, every multiplier and outward bound, and the difference closure. No LP
or flow optimizer is called. The pinned Fraction scalar oracle is shared;
its actual-kernel Lean bridge remains an explicit analytic obligation.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,json,time
import window_global_cover as w
from cover_contractor_verify import flow_bound,close
from cover_correlated_verify import make_table,verify as verify_direction
from cover_correlated_replay import a

g=w.g;HERE=Path(__file__).parent

def ceil(x):return -((-x.numerator)//x.denominator)

def minorant(state,cert):
    lo,hi=state;a.closure_valid(state)
    assert cert['lower_bounds']==lo and cert['upper_bounds']==hi and cert['mixture_denominator']==g.LD
    mass=[0]*len(g.TERMS);C=0;coeff=[b*g.LD for b in g.BS]
    for t,p,weight0,const0,slope0 in cert['mixture']:
        weight,const,slope=map(int,[weight0,const0,slope0]);assert weight>0
        i,j,aw=g.TERMS[t];z=a.INDEX[i,j];l,u=lo[z],hi[z]
        if p==-1:assert slope==0 and const==w.constant_lower(l,u)*g.SC
        else:
            assert p>=0;pl,pu,v,sl,err=w.original_support(p)
            assert pl<=l and u<=pu and const==g.SC*v-10*sl*p-10*err*max(p-l,0) and slope==10*sl
        mass[t]+=weight;C+=weight*const
        for k in range(i,j):coeff[k]+=weight*slope
    assert all(m<=aw*(g.LD//g.D) for m,(_,_,aw) in zip(mass,g.TERMS))
    assert C==int(cert['intercept']) and coeff==list(map(int,cert['gap_coefficients']))
    value=C+flow_bound(state,coeff,cert['flow'])
    return C,coeff,value

def verify_step(state,step):
    assert step['old_cell']==state
    C,coeff,_=minorant(state,step['minorant']);lower=state[0].copy();upper=state[1].copy();seen=set()
    for cert in step['certificates']:
        z=cert['axis'];sign=cert['sign'];p=cert['multiplier_numerator'];K=cert['multiplier_denominator']
        assert 0<=z<45 and sign in [1,-1] and p>0 and K>0 and (z,sign) not in seen;seen.add((z,sign))
        i,j=a.PAIRS[z]
        combined=[p*g.SC*c+(sign*K*g.DEN if i<=k<j else 0) for k,c in enumerate(coeff)]
        value=p*g.SC*C+flow_bound(state,combined,cert['flow']);assert value==int(cert['minimum_numerator'])
        bound=F(value-p*g.SC*g.TARGET,K*g.DEN) if sign==1 else F(p*g.SC*g.TARGET-value,K*g.DEN)
        assert bound==F(cert['bound'])
        newlo=max(lower[z],bound.numerator//bound.denominator) if sign==1 else lower[z]
        newhi=min(upper[z],ceil(bound)) if sign==-1 else upper[z]
        assert newlo==cert['new_lower'] and newhi==cert['new_upper']
        lower[z]=newlo;upper[z]=newhi
    assert seen
    refined=close([lower,upper]);assert refined==step['new_cell']
    return refined

def verify(row,table):
    state=row['steps'][0]['old_cell']
    for step in row['steps']:
        assert state is not None;state=verify_step(state,step)
    result=row['result']
    if result:
        if result['kind']=='empty':assert state is None
        elif result['kind']=='stationary':assert state is not None;verify_direction(state,result['result'],w.P,table)
        else:
            assert result['kind']=='value' and state is not None
            _,_,value=minorant(state,result['result']['certificate'])
            assert value==int(result['result']['floor_numerator']) and value>=g.TARGET
    return {'passed':True,'steps':len(row['steps']),'bounds':sum(len(s['certificates']) for s in row['steps']),
      'closed':bool(result),'sublevel_points_preserved':True,'pointwise_cover':False}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-sublevel-contractor.json')
    ap.add_argument('--output',type=Path,default=HERE/'cover-sublevel-replay.json');args=ap.parse_args();start=time.monotonic()
    raw=args.input.read_bytes();doc=json.loads(raw);table=make_table(HERE/'cover_newjet.json');counts={'paths':0,'steps':0,'bounds':0,'closed':0}
    for row in doc['contractions']:
        r=verify(row,table);counts['paths']+=1
        for k in ['steps','bounds','closed']:counts[k]+=r[k]
    out={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'finite_scalar_oracle_sha256':hashlib.sha256(Path(w.__file__).read_bytes()).hexdigest(),'counts':counts,'all_passed':True,
      'actual_kernel_Lean_bridges_complete':False,'complete_global_minimizer_cover':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
