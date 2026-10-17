"""Read-only stdlib replay of the affine-position Hessian matrix construction.

Rebuild its 8100 entries directly edge by edge, rather than aggregating
matrix polynomials as in the producer.  No numerical eigenvalue premise,
producer import, optimizer or Lean.  This checks coefficients, not PSD.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;PARENT=ROOT/'research-goal-20261017-quartic'
OUT=HERE/'hessian-localizer-replay.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write-receipt',action='store_true');args=parser.parse_args();began=time.monotonic()
    if args.write_receipt:assert not OUT.exists()
    paths=[Path(__file__),HERE/'hessian-localizer-static.json'];record=json.loads(paths[1].read_bytes())
    assert record['source_sha256_start']==record['source_sha256_end']
    for relative,h in record['source_sha256_start'].items():
        p=ROOT/relative;assert sha(p)==h
        if p not in paths:paths.append(p)
    pins={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    model=json.loads(gzip.decompress((PARENT/'quartic-model.json.gz').read_bytes()));point=json.loads((PARENT/'quartic-exact-primal.json').read_bytes())
    params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    assert all(F(v,32768)>F(123,128) for v in model['cell'][0][:9]) and record['all_nine_original_gaps_strictly_free']
    mon=[tuple(m) for m in model['monomials']];idx={m:k for k,m in enumerate(mon)};mom=[F(1)]+list(map(F,point['rational_714_moments']))
    B=[[F(0) for _ in range(90)] for _ in range(90)]
    for term,edge,stored in zip([t for t in params['a_upper'] if t[2]],model['edge_packets'],record['edge_upper_packets']):
        i,j,a=term;weight=F(a,params['denominator']);assert a>=0 and stored['edge']==[i,j] and F(stored['weight'])==weight
        mu=list(map(F,edge['anchor_derivative_midpoints']));eps=list(map(F,edge['anchor_derivative_errors']));R=F(edge['radius_about_anchor']);M5=F(edge['whole_span_absolute_w5_bound'])
        c0=mu[1]+eps[1]+eps[2]*R;c1=mu[2];c2=mu[3]/2+eps[3]/2+M5*R/6
        assert [F(stored[k]) for k in ['constant_in_d','linear_in_d','quadratic_in_d']]==[c0,c1,c2]
        d={mon[k]:F(v) for k,v in edge['d_polynomial']};U={():c0}
        for m,v in d.items():U[m]=U.get(m,F(0))+c1*v
        for m,v in d.items():
            for n,w in d.items():
                key=tuple(sorted(m+n));U[key]=U.get(key,F(0))+c2*v*w
        U={m:v for m,v in U.items() if v}
        assert U=={mon[k]:F(v) for k,v in stored['upper_second_derivative_polynomial']}
        M=[[sum(v*mom[idx[tuple(sorted(m+mon[r]+mon[s]))]] for m,v in U.items()) for s in range(10)] for r in range(10)]
        for r in range(i,j):
            for s in range(i,j):
                for b in range(10):
                    for c in range(10):B[10*r+b][10*s+c]+=weight*M[b][c]
    digest=hashlib.sha256(json.dumps([[str(v) for v in row] for row in B],separators=(',',':')).encode()).hexdigest()
    assert digest==record['exact_localizer_matrix_sha256'] and record['witness'] is None and record['integer_vector_attempts']==0
    assert record['status']=='single_static_localizer_test_no_exact_separation'
    assert [[str(B[10*r][10*s]) for s in range(9)] for r in range(9)]==record['constant_direction_mean_submatrix']
    assert not any(n.split('.')[0] in ['numpy','scipy','scs'] for n in sys.modules)
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==pins
    out={'scope':__doc__,'status':'exact_affine_position_Hessian_coefficients_and_8100_entries_verified',
        'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,'edge_packets':41,
        'matrix_size':90,'matrix_entries_checked':8100,'exact_matrix_sha256':digest,'pure_stdlib_replay':True,
        'exact_negative_witness_obtained':False,'exact_PSD_of_pseudomoment_localizer_proved':False,
        'optimizer_calls':0,'Lean_invocations':0,'cell_exclusion_proven':False,'new_zero_proportion_proven':False,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    if args.write_receipt:OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['status','matrix_entries_checked','exact_negative_witness_obtained','elapsed_milliseconds']}))
if __name__=='__main__':main()
