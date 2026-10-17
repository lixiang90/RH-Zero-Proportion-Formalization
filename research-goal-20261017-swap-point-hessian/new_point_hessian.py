"""One frozen-Hessian-localizer test at the new eight-swap714 point.

No coefficient changes, old-point retest, solver or joint-model creation.
Build the same90x90 Hplus localizer from frozen edge polynomials. Exactly
one eigh; if negative, one maxabs4096 integer-vector quantization and an
exact quadratic check in two algebraically equivalent forms. Positive
floating eigenvalues are not an exact PSD proof.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip,hashlib,json,math,os,sys,time

os.environ['OPENBLAS_NUM_THREADS']='1'
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
sys.path.insert(0,str(ROOT/'tmp/goal-20261016/python-sdp'))
import numpy as np

OLD=ROOT/'research-goal-20261017-quartic-hessian-localizer'
NEW=ROOT/'research-goal-20261017-swap-family-quartic'
OUT=HERE/'new-point-hessian.json';MARKER=HERE/'eigh-started.json';HINT=HERE/'eigh-once-hint.json'
POINT_SHA='f0498ca408bd6b594aeab44cc4594cb698aa6ae8c8ca53c5347b1d6c35090095'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def canonical(v):return json.dumps(v,separators=(',',':'),allow_nan=False).encode()


def main():
    assert not OUT.exists() and not MARKER.exists() and not HINT.exists();began=time.monotonic()
    paths=[Path(__file__),OLD/'hessian-localizer-static.json',OLD/'hessian-localizer-replay.json',
      OLD/'hessian-localizer-files.json',NEW/'swap-family-cone.json',NEW/'swap-family-exact-primal.json',
      ROOT/'research-goal-20261017-quartic/quartic-model.json.gz',ROOT/'research-20261016-followup/window_reweight_rational.json']
    guards={p.relative_to(ROOT).as_posix():sha(p)for p in paths};assert sha(paths[5])==POINT_SHA
    record=json.loads(paths[1].read_bytes());prior=json.loads(paths[2].read_bytes())
    assert prior['status']=='exact_affine_position_Hessian_coefficients_and_8100_entries_verified'
    assert record['source_sha256_start']==record['source_sha256_end']
    assert prior['exact_matrix_sha256']==record['exact_localizer_matrix_sha256']
    for name,h in record['source_sha256_start'].items():
        assert sha(ROOT/name)==h;guards[name]=h
    cone=json.loads(paths[4].read_bytes());point=json.loads(paths[5].read_bytes())
    assert cone['phase']=='completed_single_shared_quartic_eight_swap_SCS' and cone['all_sources_unchanged']
    assert cone['input_sha256_start']==cone['input_sha256_end']
    for name,h in cone['input_sha256_start'].items():assert sha(ROOT/name)==h;guards[name]=h
    assert point['status']=='strict_exact_shared_quartic_eight_swap_outer_relaxation_feasible' and point['all_sources_unchanged']
    assert point['source_sha256_start']==point['source_sha256_end']
    for name,h in point['source_sha256_start'].items():assert sha(ROOT/name)==h;guards[name]=h
    assert cone['scalar_variables']==715 and cone['energy_slack_index']==714 and cone['PSD_sizes']==[55]+[10]*46
    assert 90 not in cone['PSD_sizes'] and cone['unsoftened_global_competitor_rows']==8
    raw=cone['raw_primal_hint'];assert len(raw)==715 and all(math.isfinite(float(x))for x in raw)
    converted=[F(str(float(x)))for x in raw[:714]]
    assert converted==list(map(F,point['rational_714_moments'])) and F(point['energy_slack'])==0
    moments=[F(1)]+converted
    model=json.loads(gzip.decompress(paths[6].read_bytes()));params=json.loads(paths[7].read_bytes())
    assert model['path']==point['path']==cone['path']==record['path']=='r001000001000100110011001'
    assert all(F(v,32768)>F(123,128)for v in model['cell'][0][:9])
    mon=list(map(tuple,model['monomials']));index={m:i for i,m in enumerate(mon)};basis=[()]+[(r,)for r in range(9)]
    assert len(mon)==len(moments)==715 and mon[:10]==basis
    B=[[F(0)for _ in range(90)]for _ in range(90)];polys=[]
    terms=[t for t in params['a_upper']if t[2]];assert len(terms)==len(record['edge_upper_packets'])==41
    for term,stored in zip(terms,record['edge_upper_packets']):
        i,j,a=term;assert a>0 and stored['edge']==[i,j];weight=F(a,params['denominator']);assert F(stored['weight'])==weight
        U={mon[k]:F(v)for k,v in stored['upper_second_derivative_polynomial']};assert all(len(m)<=2 for m in U)
        polys.append((i,j,weight,U))
        M=[[sum((v*moments[index[tuple(sorted(m+basis[b]+basis[c]))]]for m,v in U.items()),F(0))for c in range(10)]for b in range(10)]
        for r in range(i,j):
            for s in range(i,j):
                for b in range(10):
                    for c in range(10):B[10*r+b][10*s+c]+=weight*M[b][c]
    assert all(B[i][j]==B[j][i]for i in range(90)for j in range(90))
    matrix_sha=hashlib.sha256(canonical([[str(v)for v in row]for row in B])).hexdigest()
    point_sha=hashlib.sha256(canonical(list(map(str,converted)))).hexdigest()
    # A durable one-attempt marker prevents an accidental second decomposition.
    MARKER.write_bytes(canonical({'scope':'exactly one eigh authorized for this fixed new point','source_sha256':sha(Path(__file__)),
      'matrix_sha256':matrix_sha,'rational714_sha256':point_sha})+b'\n')
    eigen,vectors=np.linalg.eigh(np.array([[float(v)for v in row]for row in B]))
    assert all(math.isfinite(float(v))for v in eigen)
    vector=vectors[:,0];HINT.write_bytes(canonical({'matrix_sha256':matrix_sha,'rational714_sha256':point_sha,
      'eigenvalues_hint':eigen.tolist(),'minimum_eigenvector_hint':vector.tolist(),'eigh_calls':1})+b'\n')
    witness=None
    if eigen[0]<0:
        largest=float(np.max(np.abs(vector)));assert largest>0
        integers=[int(round(float(v)*4096/largest))for v in vector];assert any(integers)
        value=sum((F(integers[i])*B[i][j]*integers[j]for i in range(90)for j in range(90)),F(0))
        # Independent contraction: E sum_e a_e U_e (sum_{r in edge}v_r(y))^2.
        direct=F(0)
        for i,j,weight,U in polys:
            z={b:sum(integers[10*r+s]for r in range(i,j))for s,b in enumerate(basis)}
            for m,u in U.items():
                for b,v in z.items():
                    for c,w in z.items():direct+=weight*u*v*w*moments[index[tuple(sorted(m+b+c))]]
        assert direct==value
        witness={'quantization':'minimum eigenvector, maxabs4096, nearest integer once','integer_vector':integers,
          'exact_quadratic_value':str(value),'same_value_from_direct_edge_polynomials':str(direct),
          'strictly_negative_exact':value<0,'nonconstant_affine_coefficients':any(integers[k]for k in range(90)if k%10)}
    for name,h in guards.items():assert sha(ROOT/name)==h,('changed source',name)
    separated=bool(witness and witness['strictly_negative_exact'])
    result={'scope':__doc__,'status':'new_eight_swap_point_exactly_separated_by_frozen_Hessian_localizer'if separated else'new_eight_swap_point_one_Hessian_test_no_exact_separation',
      'source_sha256_start':guards,'source_sha256_end':guards,'all_sources_unchanged':True,'path':model['path'],
      'point_source':paths[5].relative_to(ROOT).as_posix(),'point_source_sha256':POINT_SHA,
      'conversion':'Fraction(str(float(raw_primal_hint[:714]))) once, energy slack fixed0; no repair/projection',
      'rational714_sha256':point_sha,'original_solver_energy_slack_hint':raw[714],'energy_slack_used':'0',
      'only_new_point_tested':True,'frozen_Hessian_polynomial_record_sha256':sha(paths[1]),
      'frozen_Hessian_polynomials_unchanged':True,'matrix_size':90,'matrix_entries':8100,
      'matrix_order':'physical gap direction r0..8, affine basis1,y0,...,y8','exact_matrix_sha256':matrix_sha,
      'minimum_eigenvalue_hint':float(eigen[0]),'maximum_eigenvalue_hint':float(eigen[-1]),'eigh_calls':1,
      'integer_vector_attempts':int(witness is not None),'witness':witness,'new_point_exactly_separated':separated,
      'positive_float_eigenvalues_are_not_exact_PSD_proof':True,'Hessian_condition_included_in_eight_swap_SCS':False,
      'all_nine_physical_gaps_strictly_free':True,'actual_Hessian_and_table_premises_same_as_frozen_package':True,
      'optimizer_calls':0,'joint_model_constructed':False,'Lean_invocations':0,'cell_exclusion_proven':False,
      'new_zero_proportion_proven':False,'seconds':time.monotonic()-began,'numpy_version':np.__version__}
    OUT.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'status':result['status'],'minimum_eigenvalue_hint':float(eigen[0]),'maximum_eigenvalue_hint':float(eigen[-1]),
      'integer_vector_attempts':result['integer_vector_attempts'],'strictly_negative_exact':separated,
      'exact_quadratic_hint':float(F(witness['exact_quadratic_value']))if witness else None,
      'matrix_sha256':matrix_sha,'source_sha256':sha(Path(__file__)),'receipt_sha256':sha(OUT),'seconds':result['seconds']}),flush=True)


if __name__=='__main__':
    assert __debug__
    main()
