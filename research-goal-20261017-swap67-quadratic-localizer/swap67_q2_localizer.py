"""One fixed swap67 quadratic upper localizer at the new exact714 point.

Compress each signed scalar quartic as c3*d3<=abs(c3)*R*d2 and
c4*d4<=max(c4,0)*R2*d2, obtaining Q2>=D4>=F(Tg)-F(g).
At a global minimizer Q2>=0, so E[Q2*(1,y)*(1,y)^T] must be PSD.
Exactly one 10x10 eigh; if negative, one fixed integer quantization and
exact Fraction quadratic check. No optimizer, new kernel input, or Lean.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip,hashlib,json,os,sys,time
os.environ['OPENBLAS_NUM_THREADS']='1'
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
FAMILY=ROOT/'research-goal-20261017-swap-family-quartic'
sys.path.insert(0,str(ROOT/'tmp/goal-20261016/python-sdp'))
import numpy as np
OUT=HERE/'swap67-q2-localizer.json'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def add(p,q,c=F(1)):
    p=p.copy()
    for m,a in q.items():
        v=p.get(m,F(0))+c*a
        if v:p[m]=v
        else:p.pop(m,None)
    return p
def mul(p,q):
    out={}
    for m,a in p.items():
        for n,b in q.items():out=add(out,{tuple(sorted(m+n)):a*b})
    return out

def main():
    assert not OUT.exists();began=time.monotonic()
    paths=[Path(__file__),FAMILY/'swap-family-files.json',FAMILY/'swap-family-normalized.json.gz',
        FAMILY/'swap-family-normalized-build.json',FAMILY/'swap-family-exact-primal.json',
        FAMILY/'swap-family-result-replay.json',ROOT/'StructuralGoal20261016/WindowGlobalCompetitor.lean',
        ROOT/'research-goal-20261017-swap67-quartic/swap67-quartic-static.json']
    pins={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    manifest=json.loads(paths[1].read_bytes())
    for row in manifest['package_files']+manifest['dependency_files']:assert sha(ROOT/row['path'])==row['sha256']
    raw=gzip.decompress(paths[2].read_bytes());family=json.loads(raw);build=json.loads(paths[3].read_bytes())
    assert sha(paths[2])==build['packet_compressed_sha256'] and hashlib.sha256(raw).hexdigest()==build['packet_uncompressed_sha256']
    proof=json.loads(paths[4].read_bytes());replay=json.loads(paths[5].read_bytes());single=json.loads(paths[7].read_bytes())
    assert proof['exact_eight_swap_quartic_outer_relaxation_feasible'] and replay['passed']
    mon=[tuple(m) for m in family['monomials']];idx={m:k for k,m in enumerate(mon)};basis=mon[:10]
    moments=[F(1)]+list(map(F,proof['rational_714_moments']));assert len(moments)==len(mon)==715
    item=family['maps'][6];assert item['swap_zero_based']==[6,7] and item['difference_upper_quartic']==single['difference_upper_quartic']
    def unpack(p):return {mon[k]:F(v) for k,v in p}
    def pack(p):return [[idx[m],str(v)] for m,v in sorted(p.items(),key=lambda z:idx[z[0]])]
    def expect(p):return sum(v*moments[idx[m]] for m,v in p.items())
    pressure=unpack(item['pressure_difference_polynomial']);quartic=pressure;quadratic=pressure;packets=[]
    for edge in item['changed_edge_packets']:
        weight=F(edge['weight']);assert weight>0
        for side,sign in [('new',1),('old',-1)]:
            packet=family['scalar_packets'][edge[side+'_scalar_packet']]
            d=unpack(packet['d_polynomial']);R=F(packet['radius_about_anchor']);mu=list(map(F,packet['anchor_derivative_midpoints']));eps=list(map(F,packet['anchor_derivative_errors']));M5=F(packet['whole_span_absolute_w5_bound'])
            assert R>0 and all(e>=0 for e in eps) and M5>=0
            cs=[sign*mu[0]+eps[0]+eps[1]*R,sign*mu[1],sign*mu[2]/2+eps[2]/2+eps[3]*R/6,
                sign*mu[3]/6,sign*mu[4]/24+eps[4]/24+M5*R/120]
            powers=[{():F(1)}]
            for _ in range(4):powers.append(mul(powers[-1],d))
            p4={}
            for j in range(5):p4=add(p4,powers[j],cs[j])
            target=unpack(packet['scalar_upper_quartic']) if sign==1 else {m:-v for m,v in unpack(packet['scalar_lower_quartic']).items()}
            assert p4==target
            c2=cs[2]+abs(cs[3])*R+max(cs[4],F(0))*R**2
            p2=add(add({():cs[0]},d,cs[1]),powers[2],c2)
            # Exact factorized difference certificate; each factor is
            # nonnegative when |d|<=R.
            remainder={}
            remainder=add(remainder,powers[2],abs(cs[3])*R+max(cs[4],F(0))*R**2)
            remainder=add(remainder,powers[3],-cs[3]);remainder=add(remainder,powers[4],-cs[4])
            assert add(p2,p4,F(-1))==remainder
            quadratic=add(quadratic,p2,weight);quartic=add(quartic,p4,weight)
            packets.append({'edge':edge['edge'],'side':side,'sign':sign,'scalar_packet_id':packet['id'],'weight':str(weight),
                'radius':str(R),'d_polynomial':pack(d),'signed_quartic_coefficients_in_d':list(map(str,cs)),
                'upper_quadratic_coefficients_in_d':[str(cs[0]),str(cs[1]),str(c2)],
                'upper_quadratic_polynomial':pack(p2),'quadratic_minus_signed_quartic':pack(remainder)})
    assert pack(quartic)==item['difference_upper_quartic'] and len(packets)==16 and all(len(m)<=2 for m in quadratic)
    matrix=[[F(0) for _ in range(10)] for _ in range(10)]
    for i in range(10):
        for j in range(i,10):
            value=sum(v*moments[idx[tuple(sorted(m+basis[i]+basis[j]))]] for m,v in quadratic.items())
            matrix[i][j]=matrix[j][i]=value
    matrixhash=hashlib.sha256(json.dumps([[str(v) for v in row] for row in matrix],separators=(',',':')).encode()).hexdigest()
    eigen,vectors=np.linalg.eigh(np.array([[float(v) for v in row] for row in matrix]));witness=None
    if eigen[0]<0:
        v=[int(round(float(x)*10**6)) for x in vectors[:,0]];assert any(v)
        value=sum(F(v[i])*matrix[i][j]*v[j] for i in range(10) for j in range(10))
        witness={'fixed_quantization_scale':10**6,'integer_vector':v,'exact_quadratic_value':str(value),'strictly_negative':value<0}
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==pins
    out={'scope':__doc__,'status':'fixed_swap67_quadratic_upper_localizer_evaluated_once',
        'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,'path':family['path'],
        'swap_zero_based':[6,7],'underlying_gap_variables':9,'unchanged_moment_count':715,'basis':[list(m) for m in basis],
        'signed_scalar_reductions':packets,'pressure_difference_polynomial':pack(pressure),'quartic_upper_difference':pack(quartic),
        'quadratic_upper_difference':pack(quadratic),'Q2_minus_D4':pack(add(quadratic,quartic,F(-1))),
        'new_point_expected_D4':str(expect(quartic)),'new_point_expected_Q2':str(expect(quadratic)),
        'localizer_matrix':[[str(v) for v in row] for row in matrix],'localizer_matrix_sha256':matrixhash,
        'eigh_calls':1,'minimum_eigenvalue_hint':float(eigen[0]),'maximum_eigenvalue_hint':float(eigen[-1]),
        'integer_vector_attempts':int(witness is not None),'exact_negative_vector':witness,
        'new_exact714_separated':bool(witness and witness['strictly_negative']),
        'positive_float_eigenvalues_are_not_exact_PSD_claim':True,'actual_scalar_enclosures_newly_Lean_proved':False,
        'new_actual_kernel_inputs':0,'solver_calls':0,'Lean_invocations':0,'cell_exclusion_proven':False,'new_zero_proportion_proven':False,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'status':out['status'],'expected_D4':float(expect(quartic)),'expected_Q2':float(expect(quadratic)),
        'minimum_eigenvalue_hint':out['minimum_eigenvalue_hint'],'maximum_eigenvalue_hint':out['maximum_eigenvalue_hint'],
        'integer_vector_attempts':out['integer_vector_attempts'],'new_exact714_separated':out['new_exact714_separated'],
        'elapsed_milliseconds':out['elapsed_milliseconds']}),flush=True)
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
