"""One exact covariance-directed halfspace disjunction of the frozen cell.

One largest-eigenvector hint, quantized once to small integers and L1
normalized.  The final split, covering identity, all six localizers and
two strict negative old-point witnesses are entirely rational.  No solver
or actual-kernel sampling occurs in this static construction.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip,hashlib,json,os,sys,time
os.environ['OPENBLAS_NUM_THREADS']='1'
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;PARENT=ROOT/'research-goal-20261017-quartic'
sys.path.insert(0,str(ROOT/'tmp/goal-20261016/python-sdp'))
import numpy as np
OUT=HERE/'split-model.json'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def put(p,m,v):
    z=p.get(m,F(0))+v
    if z:p[m]=z
    else:p.pop(m,None)
def add(p,q,s=F(1)):
    out=p.copy()
    for m,v in q.items():put(out,m,s*v)
    return out
def times(p,q):
    out={}
    for m,v in p.items():
        for n,w in q.items():put(out,tuple(sorted(m+n)),v*w)
    return out
def scale(p,s):return {m:v*s for m,v in p.items() if v*s}


def main():
    assert not OUT.exists();began=time.monotonic()
    paths=[Path(__file__),PARENT/'quartic-files.json',PARENT/'quartic-model.json.gz',PARENT/'quartic-build.json',
        PARENT/'quartic-exact-primal.json',PARENT/'quartic-result-replay.json']
    pins={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    manifest=json.loads(paths[1].read_bytes())
    for entry in manifest['package_files']+manifest['dependency_files']:assert sha(ROOT/entry['path'])==entry['sha256']
    raw=gzip.decompress(paths[2].read_bytes());model=json.loads(raw);build=json.loads(paths[3].read_bytes());proof=json.loads(paths[4].read_bytes());replay=json.loads(paths[5].read_bytes())
    assert hashlib.sha256(raw).hexdigest()==build['model_uncompressed_sha256'] and sha(paths[2])==build['model_compressed_sha256']
    assert replay['status']=='strict_exact_shared_quartic_outer_relaxation_independently_verified'
    x=list(map(F,proof['rational_714_moments']));mon=[tuple(m) for m in model['monomials']];index={m:k for k,m in enumerate(mon)}
    mean=x[:9];cov=[[x[index[tuple(sorted((r,s))) ]-1]-mean[r]*mean[s] for s in range(9)] for r in range(9)]
    eig,vec=np.linalg.eigh(np.array([[float(v) for v in row] for row in cov]));v=vec[:,-1]
    integers=[int(round(float(z)*16/float(np.max(np.abs(v))))) for z in v]
    assert any(integers)
    if next(z for z in integers if z)!=abs(next(z for z in integers if z)):integers=[-z for z in integers]
    norm=sum(map(abs,integers));alpha=[F(z,norm) for z in integers];threshold=sum(a*y for a,y in zip(alpha,mean))
    assert sum(map(abs,alpha))==1 and -1<threshold<1
    phi={(r,):a for r,a in enumerate(alpha) if a};values=[F(1)]+x
    def pack(p):return [[index[m],str(v)] for m,v in sorted(p.items(),key=lambda z:index[z[0]])]
    def form(p):return {'constant':str(p.get((),F(0))),
        'coefficients':[[index[m]-1,str(v)] for m,v in sorted(p.items(),key=lambda z:index[z[0]]) if m]}
    def block(name,g):
        entries=[];basis=mon[:10]
        for j in range(10):
            for i in range(j,10):entries.append([i,j,form(times(g,{tuple(sorted(basis[i]+basis[j])):F(1)}))])
        return {'name':name,'size':10,'multiplier_polynomial':pack(g),'entries':entries}
    branches=[]
    for sigma in [-1,1]:
        length=1-sigma*threshold
        A=scale(add(phi,{():-threshold}),F(sigma)/length)
        B=scale(add({():F(1)},phi,F(-sigma)),1/length)
        assert add(A,B)=={():F(1)}
        blocks=[block('halfspace_lower',A),block('halfspace_upper',B),block('halfspace_product',scale(times(A,B),F(4)))]
        matrix=[[F(0) for _ in range(10)] for _ in range(10)]
        for i,j,f in blocks[0]['entries']:
            matrix[i][j]=matrix[j][i]=F(f['constant'])+sum(F(q)*x[k] for k,q in f['coefficients'])
        assert matrix[0][0]==0
        r=[sum(cov[i][j]*alpha[j] for j in range(9))*sigma/length for i in range(9)]
        assert matrix[0][1:]==r and any(r)
        j=next(i for i,z in enumerate(r) if z);negative_vector=[F(0)]*10
        negative_vector[0]=-(matrix[j+1][j+1]+1)/(2*r[j]);negative_vector[j+1]=F(1)
        quadratic=sum(negative_vector[i]*matrix[i][k]*negative_vector[k] for i in range(10) for k in range(10));assert quadratic==-1
        branches.append({'sigma':sigma,'halfspace':'phi<=threshold' if sigma==-1 else 'phi>=threshold',
            'positive_normalizing_length':str(length),'extra_PSD_blocks':blocks,
            'old_point_exact_negative_witness':{'block':'halfspace_lower','B00':'0','selected_y_coordinate':j,
                'B0j':str(r[j]),'Bjj':str(matrix[j+1][j+1]),'principal_2x2_determinant':str(-r[j]**2),
                'vector':list(map(str,negative_vector)),'quadratic_value':'-1'}})
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==pins
    out={'scope':__doc__,'status':'exact_two_halfspace_models_and_old_point_separation_constructed','path':model['path'],
        'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,
        'parent_manifest_sha256':sha(PARENT/'quartic-files.json'),'parent_compressed_model_sha256':sha(PARENT/'quartic-model.json.gz'),
        'direction_discovery':'one eigendecomposition of exact-point 9x9 covariance in float; scale maximal eigenvector to maxabs16, nearest integers once; first nonzero made positive; L1 normalize',
        'direction_numpy_version':np.__version__,'covariance_eigenvalues_hint':eig.tolist(),'largest_eigenvector_hint':v.tolist(),
        'direction_integer_numerators':integers,'direction_L1_denominator':norm,'alpha':list(map(str,alpha)),
        'threshold':str(threshold),'exact_first_moments':list(map(str,mean)),'phi_polynomial':pack(phi),'branches':branches,
        'covering_identity':'For every real y, phi(y)<=threshold or phi(y)>=threshold, by le_total.',
        'localizer_validity':'On a chosen halfspace and the parent cube, A=sigma*(phi-threshold)/(1-sigma*threshold)>=0; B=(1-sigma*phi)/(1-sigma*threshold)>=0; A+B=1; 4AB>=0.',
        'original_analytic_premises_unchanged':True,'use_entire_parent_span_for_Taylor':True,'no_child_anchor_requirement':True,
        'nonconstant_moments':714,'unchanged_linear_rows':5795,'parent_PSD_sizes':model['PSD_sizes'],'additional_PSD_sizes_per_branch':[10,10,10],
        'actual_F_or_KKT_counterexample':False,'cell_exclusion_proven':False,'solver_calls':0,'Lean_invocations':0,
        'new_actual_scalar_positions':0,'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'status':out['status'],'integer_direction':integers,'denominator':norm,'threshold':str(threshold),
        'threshold_hint':float(threshold),'two_old_point_quadratic_values':['-1','-1'],'milliseconds':out['elapsed_milliseconds']}),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
