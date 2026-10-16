"""Exact Gram strengthening on the same five patterns and their 390 facets.

If Az=b and Ah=v, then on v^T(g-g0)=d the quadratic is at least
 C-b^Tz/4 + (d+v^Tz/2)^2/(v^Th).
Only rational identities are checked. Connecting this to the inherited
real-kernel minorants and to global coverage still requires Lean work.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,time

HERE=Path(__file__).parent;ROOT=HERE.parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def inverse_vector(L,D,v):
    n=len(D);u=[]
    for i in range(n):u.append(v[i]-sum(L[i][j]*u[j] for j in range(i)))
    w=[x/d for x,d in zip(u,D)];h=[F(0)]*n
    for i in range(n-1,-1,-1):h[i]=w[i]-sum(L[j][i]*h[j] for j in range(i+1,n))
    return h

def main():
    start=time.monotonic();path=HERE/'analytic_gram_wide_adaptive.json';receipt=HERE/'analytic_gram_wide_adaptive_replay.json'
    watch=[path,receipt,Path(__file__)];initial={p.name:sha(p) for p in watch}
    audit=json.loads(receipt.read_text());assert audit['passed'] and audit['certificate_sha256']==sha(path)
    doc=json.loads(path.read_text());chosen=sorted(doc['results'],key=lambda r:F(r['Gram_lower_bound_exact']))[:5]
    results=[]
    for row in chosen:
        A=[[F(v) for v in r] for r in row['matrix_A']];L=[[F(v) for v in r] for r in row['LDL_unit_lower']]
        D=list(map(F,row['LDL_positive_diagonal']));z=list(map(F,row['A_inverse_gradient']));q=[F(v,row['anchor_denominator']) for v in row['anchor_numerators']]
        C=F(row['Gram_lower_bound_exact']);data=[]
        for term in row['terms']:
            i,j=term['pair'];v=[F(int(i<=r<j)) for r in range(9)];h=inverse_vector(L,D,v)
            assert all(sum(A[r][s]*h[s] for s in range(9))==v[r] for r in range(9))
            denom=sum(x*y for x,y in zip(v,h));assert denom>0
            normal_shift=sum(x*y for x,y in zip(v,z))/2
            for sign in [-1,1]:
                t=F(term['center'])+sign*F(49,100);d=t-sum(q[i:j]);offset=d+normal_shift
                lower=C+offset**2/denom
                # An exact weighted Cauchy witness: A*h=v. The minimized
                # square norm equals offset^2/(v^T A^{-1} v).
                witness=[offset*x/denom for x in h]
                assert sum(x*y for x,y in zip(v,witness))==offset
                assert sum(witness[r]*A[r][s]*witness[s] for r in range(9) for s in range(9))==offset**2/denom
                data.append({'pair':[i,j],'sign':sign,'facet_value_exact':str(t),'A_inverse_normal':list(map(str,h)),
                    'normal_inverse_norm_exact':str(denom),'shifted_facet_offset_exact':str(offset),
                    'exact_lower_bound':str(lower),'lower_bound_float_display_only':float(lower),
                    'above_candidate_floor_exact':lower>=F(433,50000)})
        results.append({'integer_gaps':row['integer_gaps'],'facets':data,
            'minimum_facet_lower_bound_exact':str(min(F(z['exact_lower_bound']) for z in data))})
    all_rows=[r for x in results for r in x['facets']];final={p.name:sha(p) for p in watch};assert initial==final
    outcome={'scope':__doc__,'initial_sha256':initial,'final_sha256':final,'all_inputs_unchanged':True,
        'patterns':len(results),'facets':len(all_rows),'facets_above_candidate_floor_exact':sum(r['above_candidate_floor_exact'] for r in all_rows),
        'minimum_facet_lower_bound_exact':str(min(F(r['exact_lower_bound']) for r in all_rows)),
        'minimum_facet_lower_bound_float_display_only':min(r['lower_bound_float_display_only'] for r in all_rows),
        'results':results,'seconds':time.monotonic()-start,'real_kernel_connection_formalized':False,
        'phase_concentration_proven':False,'new_unconditional_bound_proven':False}
    (HERE/'analytic_boundary_gram.json').write_text(json.dumps(outcome,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in outcome.items() if k!='results'}),flush=True)

if __name__=='__main__':main()
