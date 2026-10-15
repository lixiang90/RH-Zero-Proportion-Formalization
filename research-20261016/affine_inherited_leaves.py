"""Exact box-range audit against inherited certified local leaf constants.

This can only reuse an old leaf if its old constant plus an independent exact
range for the rational potential clears the target. Failed cells need new
joint LP/tangent certificates. It is not a formal new counting theorem.
"""
import hashlib,itertools,json
from pathlib import Path
from fractions import Fraction as Q
import numpy as np
import overlap_leaf_graph as leaf

def main():
    inp=Path(__file__).with_name('validate_affine_potential.json');raw=inp.read_bytes();d=json.loads(raw)
    theta={int(s):r for s,r in d['potential_numerators'].items()};den=d['denominator']
    SC=32768;H=100*SC*den
    def bounds(L,U):
        L=[max(l,Q(17,20)*SC) for l in L]
        if any(l>u for l,u in zip(L,U)):return None
        # If all values remain in a unique binary state, include exactly it.
        possibilities=[]
        for l,u in zip(L,U):
            possibilities.append([w for w,(a,b) in enumerate([(Q(17,20)*SC,Q(3,2)*SC),(Q(3,2)*SC,Q(5,2)*SC)]) if max(l,a)<=min(u,b)])
        vals=[]
        outside=any(l<Q(17,20)*SC or u>Q(5,2)*SC for l,u in zip(L,U))
        if outside:vals.append((Q(0),Q(0)))
        possible_nonzero=[]
        for state,row in theta.items():
            word=tuple((state>>i)&1 for i in range(7))
            if all(w in poss for w,poss in zip(word,possibilities)):
                possible_nonzero.append((word,row))
        count=1
        for v in possibilities:count*=len(v)
        if count>len(possible_nonzero):vals.append((Q(0),Q(0)))
        for word,row in possible_nonzero:
            low=high=Q(100*SC*row[0])
            for w,l,u,v in zip(word,L,U,row[1:]):
                a,b=[(Q(17,20)*SC,Q(3,2)*SC),(Q(3,2)*SC,Q(5,2)*SC)][w]
                ll,uu=max(l,a),min(u,b);mu=[104,197][w]
                low+=v*(100*(ll if v>=0 else uu)-mu*SC)
                high+=v*(100*(uu if v>=0 else ll)-mu*SC)
            vals.append((low,high))
        return min(v[0] for v in vals)/H,max(v[1] for v in vals)/H
    leaves=leaf.collect(10**30);results=[]
    for scale,target in [(Q(1),Q(43,5000)),(Q(3,5),Q(4299,500000)),(Q(1,2),Q(42989,5000000))]:
        failures=[];passed=outside=0
        for x in leaves:
            a=bounds(x['lo'][:7],x['hi'][:7]);b=bounds(x['lo'][1:8],x['hi'][1:8])
            if a is None or b is None:outside+=1;continue
            base=Q(x['value_num'],leaf.f.SLOPE*leaf.SCALE)
            lower=base+scale*(a[0]-b[1])
            if lower>=target:passed+=1
            else:failures.append({'root':x['root'],'pos':x['pos'],'reflected':x.get('reflected',False),
                'base':str(base),'corrected_lower':str(lower),'float_corrected_lower':float(lower),
                'lo':x['lo'],'hi':x['hi']})
        rec={'scale':str(scale),'target':str(target),'leaf_count':len(leaves),'passed':passed,
            'infeasible_with_separation':outside,'failed':len(failures),'failed_cells':failures}
        results.append(rec)
        print(json.dumps({k:v for k,v in rec.items() if k!='failed_cells'}),flush=True)
    out={'status':'exact arithmetic audit of inherited leaf lower bounds only; failed cells unresolved; not a new proof',
        'input_potential_sha256':hashlib.sha256(raw).hexdigest(),'results':results}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')

if __name__=='__main__':main()
