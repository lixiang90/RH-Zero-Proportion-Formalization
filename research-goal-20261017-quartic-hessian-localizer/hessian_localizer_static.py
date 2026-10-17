"""One static affine-position Hessian necessary-condition test.

At the one frozen 714-moment point, use only the parent's common anchor
jets/radii/w5 bounds to build a quadratic matrix upper bound for actual
Hess F.  All nine coordinates must be strictly free.  Its affine-position
90x90 localizer is a new minimizer condition.  Exactly one eigh and at
most one fixed integer-vector quantization, no optimizer or new samples.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip,hashlib,json,os,sys,time
os.environ['OPENBLAS_NUM_THREADS']='1'
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;PARENT=ROOT/'research-goal-20261017-quartic'
sys.path.insert(0,str(ROOT/'tmp/goal-20261016/python-sdp'))
import numpy as np
OUT=HERE/'hessian-localizer-static.json'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def add(p,q,s=F(1)):
    out=p.copy()
    for m,v in q.items():
        z=out.get(m,F(0))+s*v
        if z:out[m]=z
        else:out.pop(m,None)
    return out
def product(p,q):
    out={}
    for m,a in p.items():
        for n,b in q.items():out=add(out,{tuple(sorted(m+n)):a*b})
    return out


def main():
    assert not OUT.exists();began=time.monotonic()
    paths=[Path(__file__),PARENT/'quartic-files.json',PARENT/'quartic-model.json.gz',PARENT/'quartic-build.json',
        PARENT/'quartic-exact-primal.json',PARENT/'quartic-result-replay.json',ROOT/'research-20261016-followup/window_reweight_rational.json']
    pins={p.relative_to(ROOT).as_posix():sha(p) for p in paths};manifest=json.loads(paths[1].read_bytes())
    for entry in manifest['package_files']+manifest['dependency_files']:assert sha(ROOT/entry['path'])==entry['sha256']
    raw=gzip.decompress(paths[2].read_bytes());model=json.loads(raw);build=json.loads(paths[3].read_bytes());proof=json.loads(paths[4].read_bytes());replay=json.loads(paths[5].read_bytes());params=json.loads(paths[6].read_bytes())
    assert hashlib.sha256(raw).hexdigest()==build['model_uncompressed_sha256'] and sha(paths[2])==build['model_compressed_sha256']
    assert proof['status']=='strict_exact_shared_quartic_outer_relaxation_feasible' and replay['status']=='strict_exact_shared_quartic_outer_relaxation_independently_verified'
    assert model['path']==proof['path']=='r001000001000100110011001'
    lower=model['cell'][0][:9];assert all(F(v,32768)>F(123,128) for v in lower)
    mon=[tuple(m) for m in model['monomials']];idx={m:k for k,m in enumerate(mon)};basis=mon[:10]
    moments=[F(1)]+list(map(F,proof['rational_714_moments']));terms=[tuple(t) for t in params['a_upper'] if t[2]]
    H=[[{} for _ in range(9)] for _ in range(9)];packets=[]
    for (i,j,numerator),edge in zip(terms,model['edge_packets']):
        assert edge['edge']==[i,j] and numerator>=0
        d={mon[k]:F(v) for k,v in edge['d_polynomial']};d2=product(d,d)
        mu=list(map(F,edge['anchor_derivative_midpoints']));eps=list(map(F,edge['anchor_derivative_errors']));R=F(edge['radius_about_anchor']);M5=F(edge['whole_span_absolute_w5_bound'])
        constant=mu[1]+eps[1]+eps[2]*R;linear=mu[2];quadratic=(mu[3]+eps[3])/2+M5*R/6
        U=add(add({():constant},d,linear),d2,quadratic);weight=F(numerator,params['denominator'])
        packets.append({'edge':[i,j],'weight':str(weight),'constant_in_d':str(constant),'linear_in_d':str(linear),
            'quadratic_in_d':str(quadratic),'upper_second_derivative_polynomial':[[idx[m],str(v)] for m,v in sorted(U.items(),key=lambda z:idx[z[0]])]})
        for r in range(i,j):
            for s in range(i,j):H[r][s]=add(H[r][s],U,weight)
    B=[[F(0) for _ in range(90)] for _ in range(90)]
    for r in range(9):
        for s in range(r,9):
            polynomial=H[r][s]
            for a in range(10):
                for b in range(10):
                    suffix=basis[a]+basis[b]
                    value=sum(v*moments[idx[tuple(sorted(m+suffix))]] for m,v in polynomial.items())
                    B[r*10+a][s*10+b]=value;B[s*10+b][r*10+a]=value
    assert all(B[i][j]==B[j][i] for i in range(90) for j in range(90))
    matrixhash=hashlib.sha256(json.dumps([[str(v) for v in row] for row in B],separators=(',',':')).encode()).hexdigest()
    eigen,vectors=np.linalg.eigh(np.array([[float(v) for v in row] for row in B]))
    witness=None
    if eigen[0]<0:
        vector=vectors[:,0];integers=[int(round(float(v)*4096/float(np.max(np.abs(vector))))) for v in vector];assert any(integers)
        value=sum(F(integers[i])*B[i][j]*integers[j] for i in range(90) for j in range(90))
        # A single attempt only; do not change precision or select another vector.
        witness={'quantization':'minimal eigenvector, maxabs ->4096, nearest integer once','integer_vector':integers,
            'exact_quadratic_value':str(value),'strictly_negative_exact':value<0,
            'affine_vector_rows':[integers[10*r:10*(r+1)] for r in range(9)],
            'contains_nonconstant_position_coefficients':any(integers[i] for i in range(90) if i%10)}
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==pins
    out={'scope':__doc__,'status':'affine_position_Hessian_localizer_exactly_separates_frozen_714_point' if witness and witness['strictly_negative_exact'] else 'single_static_localizer_test_no_exact_separation',
        'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,'path':model['path'],
        'point_source':'quartic-exact-primal.json unadjusted714 moments, not either split-side numerical hint',
        'all_nine_original_gaps_strictly_free':True,'gap_lower_bounds':list(map(str,[F(v,32768) for v in lower])),
        'SEP':'123/128','edge_upper_packets':packets,'matrix_size':90,'matrix_variable_order':'gap_direction r=0..8, affine basis 1,y0,...,y8',
        'exact_localizer_matrix_sha256':matrixhash,'eigenvalues_hint':eigen.tolist(),'eigh_calls':1,'integer_vector_attempts':int(witness is not None),'witness':witness,
        'actual_analytic_hypotheses':['same frozen actual anchor jets and whole-parent w5 bounds as quartic package',
            'candidate is a twice differentiable actual local minimum in all nine free physical gap coordinates',
            'nonnegative pair weights and current parent span/radius bounds'],
        'formula':'Ue=mu2+mu3*d+mu4*d²/2+eps2+eps3*R+(eps4/2+M5*R/6)*d² >= actual w second derivative',
        'necessary_condition':'actual free minimum: Hess F PSD, so Hplus=sum a Ue e e^T PSD; for every affine vector v(y), v^T Hplus v>=0',
        'constant_direction_mean_submatrix':[[str(B[10*r][10*s]) for s in range(9)] for r in range(9)],
        'new_actual_scalar_positions':0,'optimizer_calls':0,'Lean_invocations':0,'cell_exclusion_proven':False,
        'new_zero_proportion_proven':False,'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'status':out['status'],'minimum_eigenvalue_hint':float(eigen[0]),'maximum_eigenvalue_hint':float(eigen[-1]),
        'integer_vector_attempts':out['integer_vector_attempts'],'exact_quadratic_value_hint':float(F(witness['exact_quadratic_value'])) if witness else None,
        'elapsed_milliseconds':out['elapsed_milliseconds']}),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
