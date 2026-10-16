"""Independent finite replay of per-span epigraph sublevel contractions.

No producer, LP or min-cost optimizer is called. Each separately selected
energy minorant is rebuilt from its scalar supports/capacities. Integer flow
balances, Lagrange multipliers, outward bounds and combined closure are then
checked. Actual scalar analytic and global-cover Lean obligations remain.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,json,time
import cover_sublevel_verify as shared
from cover_contractor_verify import flow_bound,close
from cover_correlated_verify import make_table,verify as verify_direction
from cover_correlated_replay import a

g=shared.g;HERE=Path(__file__).parent

def ceil(x):return -((-x.numerator)//x.denominator)

def verify(row,target,table):
    state=row['old_cell'];a.closure_valid(state);lower=state[0].copy();upper=state[1].copy();seen=set()
    for cert in row['certificates']:
        z=cert['axis'];sign=cert['sign'];p=cert['multiplier_numerator'];K=cert['multiplier_denominator']
        assert 0<=z<45 and sign in [1,-1] and p>0 and K>0 and (z,sign) not in seen;seen.add((z,sign))
        C,coeff,_=shared.minorant(state,cert['minorant']);i,j=a.PAIRS[z]
        combined=[p*g.SC*c+(sign*K*g.DEN if i<=k<j else 0) for k,c in enumerate(coeff)]
        value=p*g.SC*C+flow_bound(state,combined,cert['flow']);assert value==int(cert['minimum_numerator'])
        bound=F(value-p*g.SC*target,K*g.DEN) if sign==1 else F(p*g.SC*target-value,K*g.DEN)
        assert bound==F(cert['bound'])
        newlo=max(lower[z],bound.numerator//bound.denominator) if sign==1 else lower[z]
        newhi=min(upper[z],ceil(bound)) if sign==-1 else upper[z]
        assert newlo==cert['new_lower'] and newhi==cert['new_upper']
        lower[z]=newlo;upper[z]=newhi
    assert seen
    refined=close([lower,upper]);assert refined==row['new_cell']
    result=row['result']
    if result:
        if result['kind']=='empty':assert refined is None
        elif result['kind']=='stationary':assert refined is not None;verify_direction(refined,result['result'],shared.w.P,table)
        else:
            assert result['kind']=='value' and refined is not None
            _,_,value=shared.minorant(refined,result['result']['certificate'])
            assert value==int(result['result']['floor_numerator']) and value>=target
    return {'bounds':len(seen),'closed':bool(result)}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-sublevel-obbt.json')
    ap.add_argument('--output',type=Path,default=HERE/'cover-sublevel-obbt-replay.json');args=ap.parse_args();start=time.monotonic()
    raw=args.input.read_bytes();doc=json.loads(raw);target=int(doc['receipt']['target_numerator']);table=make_table(HERE/'cover_newjet.json');counts={'paths':0,'bounds':0,'closed':0}
    for row in doc['contractions']:
        r=verify(row,target,table);counts['paths']+=1
        for k in ['bounds','closed']:counts[k]+=r[k]
    out={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'minorant_checker_sha256':hashlib.sha256(Path(shared.__file__).read_bytes()).hexdigest(),'counts':counts,'all_passed':True,
      'actual_kernel_Lean_bridges_complete':False,'complete_global_minimizer_cover':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
