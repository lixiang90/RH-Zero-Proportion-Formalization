"""Prepared F only: one exact primal LP on original pair1/5 + real Ordered.

No model is loaded by the default command. A new written root gate must bind
the frozen inputs and primary/conditional auxiliary call budgets. Sympy is a
discovery tool only: all certificates are independently exact checked here.
"""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
from math import lcm,gcd
import argparse
import gzip
import importlib.util
import json
import os
import sys
import time
import traceback

sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
E=ROOT/'research-goal-20261018-stageE-floor-dbm'
E_PIN='73b1cc1367b32cd769712370defef03288d625b4ab04c02df56ffe4b92b3b21a'
POINT_PIN='e227a288007a8dbb984d0b69b5d367d34595b653ccd2da83e2226806751c746c'
STATIC=ROOT/'research-goal-20261018-stageF-static-review/review-files.json'
STATIC_PIN='5647a5fc023dfe06a994f1de7464414b6c18918a161086bccf3ea2ec870c572d'
AFFINE=ROOT/'research-goal-20261018-fixed-joint-affine/evaluate_once.py'
AFFINE_PIN='55311de8fb0851368c2bd5684f6ddc1441b35313122bd31a739bfb9c3195bd76'
SIMPLEX=Path('C:/Users/ip/AppData/Roaming/Python/Python314/site-packages/sympy/solvers/simplex.py')
SIMPLEX_PIN='a5e46fe38683337d14ff4c24f3166fdede8cfdca66fdaf610402e2cabef39dd6'
Q=32768
R=1024
D=10**9
V=10**10
SA=10**20
KAPPA=Q*V*R
CN=893616123055294719
C_N=893766123055294719
TARGET=4*KAPPA*C_N

def pin(p):
    h=sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    return h.hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def rel(p):return p.relative_to(ROOT).as_posix()
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode('ascii')+b'\n'
def write_new(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def dot(a,b):return sum(x*y for x,y in zip(a,b))

def inputs(gate_path,gate_sha):
    assert gate_path.is_relative_to(ROOT) and pin(gate_path)==gate_sha
    g=load(gate_path)
    assert g['primary_simplex_calls_authorized']==1
    aux=g['conditional_farkas_calls_authorized'];assert type(aux) is int and aux in [0,1]
    assert g['max_simplex_calls']==1+aux
    assert g['stageE_producer_manifest_sha256']==E_PIN
    assert g['static_manifest_sha256']==STATIC_PIN
    assert g['prefix_exception_id']==1 and g['suffix_exception_id']==5 and g['orientation']=='id/id'
    assert int(g['c_numerator'])==C_N and int(g['denominator'])==SA
    limits=g['resource_limits']
    assert 0<limits['elapsed_seconds']<=300 and 0<limits['closed_output_bytes']<=20000000
    refs={rel(gate_path):gate_sha,rel(AFFINE):AFFINE_PIN}
    for p in [Path(__file__),HERE/'run_once.py',HERE/'verify_certificate.py']:refs[rel(p)]=pin(p)
    manifests=[(E/'files.json',E_PIN),
        (ROOT/g['stageE_independent_manifest_path'],g['stageE_independent_manifest_sha256']),
        (STATIC,STATIC_PIN)]
    for p,expected in manifests:
        assert p.is_relative_to(ROOT) and pin(p)==expected;refs[rel(p)]=expected
        package=load(p)
        for field in ['files','package_files','read_only_dependencies','dependency_files','dependencies','read_only_existing_references']:
            for row in package.get(field,[]):
                q=ROOT/row['path'];assert q.is_relative_to(ROOT) and pin(q)==row['sha256']
                if 'bytes' in row:assert q.stat().st_size==row['bytes']
                if row['path'] in refs:assert refs[row['path']]==row['sha256']
                refs[row['path']]=row['sha256']
    assert pin(AFFINE)==AFFINE_PIN and pin(SIMPLEX)==SIMPLEX_PIN
    p=E/'first-underpaid-feasible.json';assert pin(p)==POINT_PIN;point=load(p)
    assert point['orientation']=='id/id' and point['case_ordinal']==1192
    assert point['prefix_exception_id']==1 and point['suffix_exception_id']==5
    assert point['X_scale']==20*Q and point['ordered_conditions_hold'] is False
    return g,refs,point

def integer(f):
    f=F(f);assert f.denominator==1
    return f.numerator

def assemble(point):
    """Only called after the new authorization; never during preparation."""
    spec=importlib.util.spec_from_file_location('frozen_original_affine_for_fixed_F',AFFINE)
    aff=importlib.util.module_from_spec(spec);spec.loader.exec_module(aff)
    model=aff.parser.load_model();aff.math.configure(model)
    assert model['CN']==CN and model['SA']==SA
    traces={};wanted={point['prefix_cell']['root'],point['suffix_cell']['root']}
    with gzip.open(aff.BASE/'baseline-events.jsonl.gz','rt',encoding='ascii') as f:
        for line in f:
            event=json.loads(line)
            if event['root'] in wanted:traces[event['root'],event['pos']]=event
    windows=[aff.evaluate_window(point['prefix_cell'],0,point,model,traces),
             aff.evaluate_window(point['suffix_cell'],1,point,model,traces)]
    physical_constant=sum(F(w['global9_affine_constant']) for w in windows)
    physical_gap_coeff=[sum(F(w['global9_gap_coefficients'][r]) for w in windows) for r in range(9)]
    const=integer(2*SA*KAPPA*physical_constant)
    gap_coeff=[integer(F(2*SA*KAPPA,20*Q)*c) for c in physical_gap_coeff]
    objective=[0]*10
    for r,c in enumerate(gap_coeff):objective[r]-=c;objective[r+1]+=c
    assert sum(objective)==0
    # Independent reconstruction from saved original natural mterm components.
    direct_const=0;direct_gap=[0]*9
    for w in windows:
        off=w['offset']
        for r,b in enumerate(model['BS']):direct_gap[off+r]+=D*R*b
        for t in w['terms']:
            a=t['external_weight_numerator'];slope=t['mslT']-2*D*t['mwT']
            direct_const+=2*Q*a*t['mvT']+20*a*(t['mcpT']-t['mcnT']-slope*t['original_L0'])
            i,j=t['edge']
            for r in range(i,j):direct_gap[off+r]+=a*slope
    assert const==direct_const and gap_coeff==direct_gap
    x=point['X_integer_potential']
    assert const+dot(objective,x)==2*SA*KAPPA*sum(F(w['affine_value_at_fixed_point']) for w in windows)
    rows=[]
    def add(vector,rhs,kind,metadata):
        assert len(vector)==10 and sum(vector)==0 and all(type(a) is int for a in vector)
        rows.append({'row_id':len(rows),'coefficients':vector,'rhs':rhs,'kind':kind,**metadata})
    for off,cell in [(0,point['prefix_cell']),(1,point['suffix_cell'])]:
        st=cell['state'];lower=st['L']+st['A'];upper=st['U']+st['B']
        for k,((i,j),l,u) in enumerate(zip(aff.math.ALL,lower,upper)):
            a=[0]*10;a[off+i]-=1;a[off+j]+=1
            add(a,20*u,'original_upper',{'offset':off,'original_span_index':k,'original_span':[i,j]})
            add([-t for t in a],-20*l,'original_lower',{'offset':off,'original_span_index':k,'original_span':[i,j]})
    for r in range(9):
        a=[0]*10;a[r]=1;a[r+1]=-1
        add(a,-17*Q,'original_separation',{'gap':r})
    for off in [0,1]:
        a=[0]*10;a[off]-=1;a[off+1]+=1;a[off+7]+=1;a[off+8]-=1
        add(a,0,'true_ordered_four_point',{'offset':off})
    assert len(rows)==155 and TARGET==4*KAPPA*C_N
    for k,e in enumerate(point['all153_edges']):
        a=[0]*10;a[e['u']]-=1;a[e['v']]+=1
        assert rows[k]['coefficients']==a and rows[k]['rhs']==e['bound']
    assert dot(rows[153]['coefficients'],x)>0 and dot(rows[154]['coefficients'],x)>0
    packet={'schema':'fixed-F155-original-affine-LP-model-v1','source_sha256':aff.parser.SOURCE_SHA,
        'original_pair':{'prefix_exception_id':1,'suffix_exception_id':5,'orientation':'id/id'},
        'rows':rows,'constant':str(const),'position_coefficients':list(map(str,objective)),
        'gap_coefficients':list(map(str,gap_coeff)),'target':str(TARGET),
        'objective_identity':'C+b*X = 2*SA*KAPPA*(A_left+A_right)',
        'scales':{'Q':Q,'R':R,'D':D,'V':V,'SA':SA,'KAPPA':KAPPA},
        'target_c_numerator':C_N,'denominator':SA,'gauge_X0':0,
        'variable_count_after_gauge':9,'all_row_coefficient_sums_and_objective_sum_zero':True,
        'nonnegative_variables_implied_by_sep':'Xi >= i*17*32768 >0 for i=1,...,9',
        'former_E_point_is_not_a_feasible_F_primal':True,
        'original_affine_engine_sha256':AFFINE_PIN,'kernel_values_evaluated':0}
    return packet,windows

def fraction(value):
    # _simplex fills nonbasic primal/dual slots with literal Python int0.
    if type(value) is int:return F(value)
    assert value.is_Rational is True,('non_rational_solver_return',repr(value))
    n,d=value.as_numer_denom();return F(int(n),int(d))

def common_integers(values,include_denominator=True):
    denom=lcm(*(x.denominator for x in values)) if values else 1
    nums=[integer(x*denom) for x in values]
    divisor=denom if include_denominator else 0
    for x in nums:divisor=gcd(divisor,abs(x))
    if divisor>1:
        if include_denominator:denom//=divisor
        nums=[x//divisor for x in nums]
    return denom,nums

def validate_primary(raw,packet):
    o,x,y=raw;o=fraction(o);x=list(map(fraction,x));y=list(map(fraction,y))
    rows=packet['rows'];b=list(map(int,packet['position_coefficients']));const=int(packet['constant'])
    assert len(x)==9 and len(y)==155
    point=[F(0)]+x
    assert all(point[i]>=i*17*Q for i in range(1,10))
    assert all(dot(r['coefficients'],point)<=r['rhs'] for r in rows)
    assert o==dot(b,point) and all(mu>=0 for mu in y)
    balance=[b[i]+sum(mu*r['coefficients'][i] for mu,r in zip(y,rows)) for i in range(10)]
    assert balance==[0]*10
    dual=F(const)-sum(mu*r['rhs'] for mu,r in zip(y,rows))
    assert dual==const+o
    support=[i for i,mu in enumerate(y) if mu]
    if dual>=TARGET:
        den,nums=common_integers(y)
        assert all(den*b[i]+sum(n*r['coefficients'][i] for n,r in zip(nums,rows))==0 for i in range(10))
        cost=den*const-sum(n*r['rhs'] for n,r in zip(nums,rows))
        assert cost>=den*TARGET
        cert={'kind':'Lower','row_ids':support,'integer_weights':[str(nums[i]) for i in support],
            'common_denominator':str(den),'weighted_integer_lower_bound':str(cost),
            'weighted_integer_target':str(den*TARGET),'exact_lower_bound':str(dual),
            'all155_primal_rows_and_full10_dual_balance_checked':True,'support_count':len(support)}
    else:
        q,z=common_integers(point)
        assert z[0]==0 and all(dot(r['coefficients'],z)<=q*r['rhs'] for r in rows)
        num=q*const+dot(b,z);assert num<q*TARGET
        cert={'kind':'Below','point_common_denominator':str(q),'integer_X':list(map(str,z)),
            'objective_numerator':str(num),'target_numerator':str(q*TARGET),
            'exact_model_value':str(dual),'exact_model_minus_target':str(dual-TARGET),
            'all155_rows_checked':True,'is_actual_energy_counterexample':False}
    return cert,{'primal':list(map(str,point)),'dual':list(map(str,y)),
        'exact_solver_objective_without_constant':str(o),'exact_full_minimum':str(dual),
        'all155_primal_rows_verified':True,'all155_dual_weights_nonnegative':True,
        'full10_balance_b_plus_muA_zero':True,'exact_primal_dual_values_equal':True}

def validate_farkas(raw,packet):
    o,lam,_dual=raw;o=fraction(o);lam=list(map(fraction,lam));rows=packet['rows']
    assert len(lam)==155 and all(x>=0 for x in lam) and o==0
    assert all(sum(v*r['coefficients'][i] for v,r in zip(lam,rows))==0 for i in range(10))
    cost=sum(v*r['rhs'] for v,r in zip(lam,rows));assert cost<=-1
    _den,nums=common_integers(lam,False)
    assert all(sum(v*r['coefficients'][i] for v,r in zip(nums,rows))==0 for i in range(10))
    icost=sum(v*r['rhs'] for v,r in zip(nums,rows));assert icost<0
    ids=[i for i,v in enumerate(nums) if v]
    return {'kind':'Empty','row_ids':ids,'integer_weights':[str(nums[i]) for i in ids],
        'integer_negative_cost':str(icost),'support_count':len(ids),
        'full10_balance_verified':True,'nonnegative_weights_verified':True,
        'auxiliary_Farkas_normalized_cost':str(cost)}

def solve(gate_path,gate_sha):
    assert __debug__
    for n in ['started.json','result.json','failure.json','model.json','primary-call-started.json']:
        assert not (HERE/n).exists(),('existing_attempt',n)
    start=time.monotonic();refs={};stage='input_guards';calls=0;primary_status=None;certificate=None;checks=None
    try:
        gate,refs,point=inputs(gate_path,gate_sha)
        write_new(HERE/'started.json',{'schema':'fixed-F-exact-LP-start-v1','pid':os.getpid(),'time_unix':time.time(),
            'inputs_sha256':refs,'runtime_simplex_path':str(SIMPLEX),'runtime_simplex_sha256':SIMPLEX_PIN,
            'primary_calls_authorized':1,'conditional_auxiliary_calls_authorized':gate['conditional_farkas_calls_authorized'],
            'pair':{'prefix':1,'suffix':5,'orientation':'id/id'}})
        print(json.dumps({'stage':'fixed_F_model_build_live','pid':os.getpid()}),flush=True)
        stage='original_affine_model_assembly';packet,windows=assemble(point)
        write_new(HERE/'affine-components.json',{'windows':windows,'source_affine_engine_sha256':AFFINE_PIN})
        packet['affine_components_sha256']=pin(HERE/'affine-components.json');write_new(HERE/'model.json',packet)
        stage='exact_runtime_import'
        import sympy
        from sympy import Matrix
        from sympy.solvers.simplex import _simplex,InfeasibleLPError,UnboundedLPError
        assert sympy.__version__=='1.14.0' and pin(SIMPLEX)==SIMPLEX_PIN
        rows=packet['rows'];A=[r['coefficients'][1:] for r in rows];rhs=[r['rhs'] for r in rows]
        b=list(map(int,packet['position_coefficients']))[1:]
        stage='primary_exact_simplex';calls+=1
        write_new(HERE/'primary-call-started.json',{'call_number':calls,'pid':os.getpid(),'time_unix':time.time(),
            'model_sha256':pin(HERE/'model.json'),'solver':'sympy1.14.0._simplex','variables':9,'rows':155,
            'runtime_sha256':SIMPLEX_PIN,'matrix_direction':'Ax<=rhs, x>=0; minimize b*x',
            'sign_authority':'independent b+mu*A=0 and C-mu*rhs checks, not the docstring'})
        try:
            raw=_simplex(Matrix(A),Matrix(rhs),Matrix([b]))
        except InfeasibleLPError as exc:
            primary_status='reported_infeasible'
            write_new(HERE/'primary-infeasible.json',{'call_number':1,'exception':type(exc).__name__,
                'message':str(exc),'mathematical_empty_certificate_yet':False})
        except UnboundedLPError as exc:
            primary_status='reported_unbounded'
            write_new(HERE/'primary-unbounded.json',{'call_number':1,'exception':type(exc).__name__,
                'message':str(exc),'theoretical_compactness_means_status_not_accepted':True})
        else:
            primary_status='returned_exact_primal_and_dual'
            write_new(HERE/'primary-raw-result.json',{'call_number':1,'objective':str(raw[0]),
                'primal':list(map(str,raw[1])),'dual':list(map(str,raw[2]))})
            stage='validate_primary_primal_dual';certificate,checks=validate_primary(raw,packet)
        if primary_status=='reported_infeasible' and gate['conditional_farkas_calls_authorized']==1:
            stage='conditional_auxiliary_Farkas_exact_simplex';calls+=1
            assert calls==2 and calls<=gate['max_simplex_calls']
            AT=Matrix(A).T
            auxA=AT.tolist()+(-AT).tolist()+[rhs];auxrhs=[0]*18+[-1]
            write_new(HERE/'auxiliary-call-started.json',{'call_number':calls,'pid':os.getpid(),
                'time_unix':time.time(),'condition':'only primary InfeasibleLPError',
                'variables':155,'rows':19,'matrix':'A^T*lambda=0,d*lambda<=-1,lambda>=0,objective0',
                'model_sha256':pin(HERE/'model.json'),'runtime_sha256':SIMPLEX_PIN})
            try:auxraw=_simplex(Matrix(auxA),Matrix(auxrhs),Matrix([[0]*155]))
            except (InfeasibleLPError,UnboundedLPError) as exc:
                write_new(HERE/'auxiliary-unconfirmed.json',{'call_number':2,'exception':type(exc).__name__,
                    'message':str(exc),'no_certificate':True})
            else:
                write_new(HERE/'auxiliary-raw-result.json',{'call_number':2,'objective':str(auxraw[0]),
                    'lambda':list(map(str,auxraw[1])),'dual':list(map(str,auxraw[2]))})
                stage='validate_exact_Farkas';certificate=validate_farkas(auxraw,packet)
        stage='closed_outputs'
        after={name:pin(ROOT/name) for name in refs};assert refs==after and pin(SIMPLEX)==SIMPLEX_PIN
        assert calls<=gate['max_simplex_calls']
        if certificate:write_new(HERE/'certificate.json',certificate)
        result={'schema':'fixed-F-exact-LP-discovery-v1','passed':certificate is not None,'pid':os.getpid(),
            'seconds':time.monotonic()-start,'inputs_sha256_start':refs,'inputs_sha256_end':after,
            'runtime_simplex_sha256_start':SIMPLEX_PIN,'runtime_simplex_sha256_end':pin(SIMPLEX),
            'sympy_version':sympy.__version__,'primary_calls':1,'conditional_auxiliary_calls':calls-1,
            'actual_simplex_calls':calls,'primary_status':primary_status,
            'outcome':certificate['kind'] if certificate else 'inconclusive_no_exact_certificate',
            'certificate_sha256':pin(HERE/'certificate.json') if certificate else None,
            'model_sha256':pin(HERE/'model.json'),'checks':checks,
            'fixed_pair':{'prefix_exception_id':1,'suffix_exception_id':5,'orientation':'id/id'},
            'new_kernel_queries':0,'new_FS_or_tangents_or_thresholds':0,'float_solver_calls':0,'Lean_runs':0,
            'all_other_exception_pairs_handled':False,'new_global_joint_floor_proven':False,
            'new_unconditional_zero_proportion_proven':False,'complete_source_and_runtime_budget':'unknown',
            'scope':'Empty/Lower closes only this fixed pair of original affine models. Below only refutes that affine lower model, never actual F. Solver status alone is not a certificate.',
            'independent_source_model_and_certificate_review_pending':True,'automatic_retry_allowed':False}
        write_new(HERE/'result.json',result)
        print(json.dumps({'passed':result['passed'],'outcome':result['outcome'],'pid':os.getpid(),
            'simplex_calls':calls,'seconds':result['seconds']}),flush=True)
    except BaseException as exc:
        write_new(HERE/'failure.json',{'passed':False,'stage':stage,'pid':os.getpid(),
            'seconds':time.monotonic()-start,'simplex_calls_started':calls,'error':repr(exc),
            'traceback':traceback.format_exc(),'inputs_sha256_start':refs,'automatic_retry_allowed':False})
        raise

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--execute-authorized-fixed-F',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');args=ap.parse_args()
    if not args.execute_authorized_fixed_F:
        print(json.dumps({'prepared_only':True,'models_loaded':0,'simplex_calls':0,'new_written_gate_required':True}));return
    assert args.gate and args.gate_sha256
    solve((ROOT/args.gate).resolve(),args.gate_sha256)

if __name__=='__main__':main()
