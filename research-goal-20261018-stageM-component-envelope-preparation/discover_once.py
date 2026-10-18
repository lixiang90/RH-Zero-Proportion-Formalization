"""Prepared M: one scaled SciPy/HiGHS discovery, exact raw certificates only.

Default CLI does not load the source model or construct a matrix. Preparation
must only AST-parse this file. A separate immutable root gate is required.
"""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
import argparse
import gzip
import importlib.util
import json
import math as stdmath
import os
import sys
import time
import traceback

sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
I=ROOT/'research-goal-20261018-stageI-original-affine-point'
BASE=ROOT/'research-goal-20261018-record-baseline-replay'
B=ROOT/'research-goal-20261018-stageB-classification'
PINS={
 'research-goal-20261018-stageI-original-affine-point/files.json':'afaece4fee2e74d064258f689faff64d9732c53f8a412d0c71f6140d7653f482',
 'research-goal-20261018-stageI-original-affine-point/evaluate_once.py':'9170d9f229a0e8c4c659812467abdac163008ef89049123d58254bbb8e47e724',
 'research-goal-20261018-stageI-independent/audit-files.json':'2e0e18319ceabada6e2466ecfabc2d19b63d8c5282dc98099315a4131f4d538e',
 'research-goal-20261018-stageI-independent/independent-review.json':'5dad6eb61c2807078cea3dc3b50d5036542ac0ba7fe3c61bde6dc6952bfff915',
 'research-goal-20261018-stageJ-independent/audit-files.json':'32de2e9381d1c103209c89b8f007d29815746a398c5c3d197f7762a727f55005',
 'research-goal-20261018-stageJ-independent/independent-review.json':'57abac20579238798df6eed99bf211cf019b75bddc0617d760c6297faea61ec1',
 'research-goal-20261018-nonlinear-remainder-static/delivery-files.json':'15418d3c8ef19489d26f15bd9ccb6e522e63e888498e01e430323b14dc226cdc'
}
METHOD='highs-ds'
OPTIONS={'presolve':True,'time_limit':180.0,'maxiter':100000,
    'primal_feasibility_tolerance':1e-7,'dual_feasibility_tolerance':1e-7,'threads':1}
def pin(p):
    h=sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    return h.hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def rel(p):return p.relative_to(ROOT).as_posix()
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False).encode('ascii')+b'\n'
def write(p,x):
    with p.open('xb') as f:f.write(canonical(x));f.flush();os.fsync(f.fileno())
def checked(name):
    p=(ROOT/name).resolve();assert p.is_relative_to(ROOT);return p
def import_frozen(p,name):
    spec=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def pin_package(p,expected,refs):
    assert pin(p)==expected;refs[rel(p)]=expected;data=load(p)
    for field in ['files','read_only_dependencies','read_only_existing_references','dependencies']:
        for item in data.get(field,[]):
            q=checked(item['path']);assert pin(q)==item['sha256']
            if 'bytes' in item:assert q.stat().st_size==item['bytes']
            if rel(q) in refs:assert refs[rel(q)]==item['sha256']
            refs[rel(q)]=item['sha256']
def runtime_hashes(runtime,verify=True):
    result={}
    for row in runtime['files']:
        p=Path(row['path']);assert p.is_absolute();current=pin(p)
        if verify:assert current==row['sha256'] and p.stat().st_size==row['bytes']
        result[str(p)]=current
    return result
def limit(start):
    if time.monotonic()-start>270:raise RuntimeError('soft_elapsed270_no_retry')
    if sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())>19000000:raise RuntimeError('soft_output19MB_no_retry')
def inputs(gate_path,gate_sha):
    assert gate_path.is_relative_to(ROOT) and pin(gate_path)==gate_sha;g=load(gate_path)
    assert g['component_envelope_LP_passes_authorized']==1 and g['primary_linprog_calls_authorized']==1
    assert g['auxiliary_optimization_calls_authorized']==0
    assert g['fixed_cells']==[0,604] and g['chart']=='id/rev' and g['sample_G_index']==2417
    assert g['target_c_numerator']=='893766123055294719' and g['denominator']=='100000000000000000000'
    assert g['resource_limits']=={'elapsed_seconds':300,'closed_output_bytes':20000000}
    assert g['work_limits']=={'elapsed_seconds':270,'closed_output_bytes':19000000}
    assert g['solver_method']==METHOD and g['solver_options']==OPTIONS
    assert g['new_FS_anchors_kernel_points_or_Lean_authorized']==0
    assert g['retry_or_precision_or_support_change_allowed'] is False
    refs={rel(gate_path):gate_sha}
    for name,expected in PINS.items():assert pin(checked(name))==expected;refs[name]=expected
    pin_package(HERE/'prepared-files.json',g['prepared_manifest_sha256'],refs)
    pin_package(I/'files.json',PINS[rel(I/'files.json')],refs)
    pin_package(ROOT/'research-goal-20261018-stageI-independent/audit-files.json',
        PINS['research-goal-20261018-stageI-independent/audit-files.json'],refs)
    pin_package(ROOT/'research-goal-20261018-nonlinear-remainder-static/delivery-files.json',
        PINS['research-goal-20261018-nonlinear-remainder-static/delivery-files.json'],refs)
    assert load(ROOT/'research-goal-20261018-stageI-independent/independent-review.json')['passed'] is True
    assert load(ROOT/'research-goal-20261018-stageJ-independent/independent-review.json')['passed'] is True
    runtime=load(HERE/'external-runtime.json');external=runtime_hashes(runtime)
    assert str(Path(sys.executable))==runtime['python_executable']
    return g,refs,runtime,external

def assemble_after_gate(alg):
    original=import_frozen(I/'evaluate_once.py','frozen_original_I_for_M')
    parser=import_frozen(BASE/'packing_parser_v3.py','frozen_parser_for_M')
    math=import_frozen(BASE/'record_math.py','frozen_math_for_M')
    source=parser.load_model();math.configure(source)
    assert source['CN']==alg.CN and source['SA']==alg.SA
    cells={}
    with gzip.open(B/'exception-cells.jsonl.gz','rt',encoding='ascii') as f:
        for line in f:
            c=json.loads(line);cid=c['exception_id']
            if cid not in alg.CELL_IDS:continue
            expected=original.FIXED_CELLS[cid]
            for key in ['root','path','position','end','state_sha256']:assert c[key]==expected[key]
            witness=c['witness']
            assert witness['consumed_payload_bits']==expected['payload_bits']
            assert witness['decoded_semantic_sha256']==expected['semantic_sha256']
            assert witness['packed_payload_sha256']==expected['payload_sha256']
            assert c['coordinate_scale']==alg.Q and c['separation']=='17/20' and c['state']['M']==0
            cells[cid]=c
    assert set(cells)==set(alg.CELL_IDS)
    wanted={c['root'] for c in cells.values()};traces={}
    with gzip.open(BASE/'baseline-events.jsonl.gz','rt',encoding='ascii') as f:
        for line in f:
            event=json.loads(line)
            if event['root'] in wanted:traces[event['root'],event['pos']]=event
    windows=[original.extract_original_affine(cells[cid],source,math,traces)[0] for cid in alg.CELL_IDS]
    model=alg.assemble(windows,cells,source,math.ALL)
    sample=load(ROOT/'research-goal-20261018-stageG-complete-classification/first-unresolved-sample.json')
    assert sample['index']==2417 and sample['chart']=='id/rev' and sample['X_scale']==20*alg.Q
    known=alg.epigraph_point(model,list(map(F,sample['X_integer_potential'])))
    known_check=alg.primal_check(model,known);assert known_check['valid']
    assert all(v.denominator==1 for v in known)
    write(HERE/'original-components.json',{'original_windows':windows,'source_sha256':parser.SOURCE_SHA,
        'source_identity_and_original_FS_guards_checked':True,'new_FS_or_anchors':0})
    write(HERE/'known-nonempty-model-witness.json',{'original_G_index':2417,'chart':'id/rev',
        'raw77':list(map(str,known)),'all_model_rows_verified':True,
        'purpose':'Existing physical point with T=max original components proves nonempty model, not an actual F value or optimum.'})
    return model

def safe_native(value):
    if isinstance(value,dict):return {str(k):safe_native(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):return [safe_native(v) for v in value]
    if hasattr(value,'tolist'):return safe_native(value.tolist())
    if isinstance(value,float):return value if stdmath.isfinite(value) else str(value)
    if value is None or isinstance(value,(str,bool,int)):return value
    if hasattr(value,'item'):return safe_native(value.item())
    return repr(value)

def support_and_bases(raw,model,alg):
    x=raw.get('x');marg=raw.get('ineqlin',{}).get('marginals')
    if not isinstance(x,list) or len(x)!=77 or not all(isinstance(v,(int,float)) and stdmath.isfinite(v) for v in x):
        return None,'no_finite_native_primal'
    if not isinstance(marg,list) or len(marg)!=len(model['rows']) or not all(isinstance(v,(int,float)) and stdmath.isfinite(v) for v in marg):
        return None,'no_finite_native_inequality_dual'
    nu=[-float(v) for v in marg];positive=[i for i,v in enumerate(nu) if v>0]
    native_X=[F(0)]+[F.from_float(float(v))*20*alg.Q for v in x[:9]]
    bases=[];all_terms_have_positive=True
    for term in model['terms']:
        candidates=[r for r in term['component_rows'] if nu[r]>0]
        if candidates:base=max(candidates,key=lambda r:(nu[r],-r))
        else:
            all_terms_have_positive=False
            base=max(term['component_rows'],key=lambda r:(alg.dot(model['rows'][r]['position10'],native_X)-model['rows'][r]['bound'],-r))
        bases.append(base)
    extra=[r for r in positive if r>=155 and r not in bases]
    geo=[r for r in positive if r<155]
    return {'native_nu':nu,'positive_rows':positive,'base_rows':bases,'extra_component_rows':extra,
        'positive_geometry_rows':geo,'all_terms_have_positive_mass_hint':all_terms_have_positive,
        'native_X':native_X,'native_negative_dual_rows':[i for i,v in enumerate(nu) if v<0]},None

def reconstruct(raw,model,alg):
    plan,reason=support_and_bases(raw,model,alg)
    if plan is None:return {'reason':reason,'exact_dual':None,'exact_primal':None}
    rows=model['rows'];bases=plan['base_rows'];extras=plan['extra_component_rows'];geo=plan['positive_geometry_rows']
    unknown=geo+extras;dual=None;dual_reason=None;dual_rank=None
    if plan['native_negative_dual_rows']:dual_reason='negative_native_dual_hint'
    elif not plan['all_terms_have_positive_mass_hint']:dual_reason='missing_term_positive_dual_hint'
    elif len(unknown)>9:dual_reason='fixed_positive_support_has_more_than9_eliminated_unknowns'
    else:
        constant=list(map(F,model['objective_position10']))
        for term,base in zip(model['terms'],bases):
            for v in range(10):constant[v]+=2*term['weight_numerator']*rows[base]['position10'][v]
        columns=[]
        for rid in unknown:
            row=rows[rid]
            if rid<155:columns.append(row['position10'])
            else:
                base=rows[bases[row['epigraph_index']]]
                columns.append([v-w for v,w in zip(row['position10'],base['position10'])])
        matrix=[[column[v] for column in columns] for v in range(1,10)]
        solution,dual_rank=alg.exact_rref(matrix,[-v for v in constant[1:]],len(unknown),[F(0)]*len(unknown))
        if solution is None:dual_reason='fixed_support_exact_balance_inconsistent'
        else:
            mu=[F(0)]*len(rows)
            for rid,value in zip(unknown,solution):mu[rid]=value
            for term,base in zip(model['terms'],bases):
                mu[base]=2*term['weight_numerator']-sum(mu[r] for r in term['component_rows'] if r!=base)
            checks=alg.dual_check(model,mu)
            dual={'raw_row_weights':list(map(str,mu)),'checks':checks,'rank':dual_rank,
                'eliminated_unknown_rows':unknown,'all_68_T_mass_equations_used':True,
                'free_unknowns_predeclared_zero':True}
            if not checks['valid']:dual_reason='exact_dual_nonnegative_or_full78_balance_failed'
    # One complementary-face reconstruction, free physical coordinates equal
    # their original native scaled dyadics. No precision/support retry.
    pm=[];pr=[]
    for rid in geo:pm.append(rows[rid]['position10'][1:]);pr.append(rows[rid]['bound'])
    for rid in extras:
        row=rows[rid];base=rows[bases[row['epigraph_index']]]
        pm.append([a-b for a,b in zip(row['position10'][1:],base['position10'][1:])])
        pr.append(row['bound']-base['bound'])
    physical,prank=alg.exact_rref(pm,pr,9,plan['native_X'][1:]);primal=None
    if physical is not None:
        point=alg.epigraph_point(model,[F(0)]+physical);checks=alg.primal_check(model,point)
        primal={'raw77':list(map(str,point)),'checks':checks,'position_reconstruction_rank':prank,
            'free_coordinates':'exact dyadic native scaled coordinates; no denominator search',
            'epigraph_coordinates':'exact max of the fixed original components'}
    plan_record={k:v for k,v in plan.items() if k not in ['native_nu','native_X']}
    return {'support_plan':plan_record,'eliminated_unknown_count':len(unknown),'dual_reason':dual_reason,
        'primal_reason':None if physical is not None else 'complementary_position_equations_inconsistent',
        'exact_dual':dual,'exact_primal':primal,'alternate_support_or_precision_trials':0}

def execute(gate_path,gate_sha):
    assert __debug__
    for name in ['started.json','result.json','failure.json','model.json','primary-call-started.json','raw-result.json']:
        assert not (HERE/name).exists(),('existing_attempt',name)
    start=time.monotonic();stage='gate_and_input_hashes';refs={};external={};calls=0;runtime=None
    try:
        _gate,refs,runtime,external=inputs(gate_path,gate_sha)
        write(HERE/'started.json',{'schema':'M-one-component-envelope-start-v1','pid':os.getpid(),'time_unix':time.time(),
            'inputs_sha256':refs,'external_runtime_sha256_start':external,'primary_calls_authorized':1,'auxiliary_calls_authorized':0})
        limit(start);stage='original_components_and_raw_model'
        alg=import_frozen(HERE/'envelope_model.py','M_envelope_definitions_after_gate')
        model=assemble_after_gate(alg);write(HERE/'model.json',model);limit(start)
        stage='scaled_runtime_import'
        import numpy as np
        import scipy
        from scipy.optimize import linprog
        assert np.__version__=='2.5.2' and scipy.__version__=='1.18.1'
        assert runtime_hashes(runtime)==external
        variable_scales=[20*alg.Q]*9+[alg.KAPPA]*68
        row_scales=[20*alg.Q if row['epigraph_index'] is None else alg.KAPPA for row in model['rows']]
        A=np.asarray([[float(F(v*s,rs)) for v,s in zip(alg.dense77(row),variable_scales)]
            for row,rs in zip(model['rows'],row_scales)],dtype=float)
        b=np.asarray([float(F(row['bound'],rs)) for row,rs in zip(model['rows'],row_scales)],dtype=float)
        c=np.asarray([float(F(v*s,alg.OBJECTIVE_SCALE)) for v,s in zip(alg.objective(model),variable_scales)],dtype=float)
        assert A.shape==(len(model['rows']),77) and np.isfinite(A).all() and np.isfinite(b).all() and np.isfinite(c).all()
        write(HERE/'scaling.json',{'variable_raw_equals_scale_times_native':list(map(str,variable_scales)),
            'row_divisors':list(map(str,row_scales)),'objective_divisor':str(alg.OBJECTIVE_SCALE),
            'native_dual_to_raw':'mu_i=objective_divisor*nu_i/row_divisor_i; discovery support only',
            'native_target':str(F(model['target'],alg.OBJECTIVE_SCALE)),'columns':77,'rows':len(model['rows'])})
        limit(start);stage='one_scipy_highs_discovery';calls=1
        write(HERE/'primary-call-started.json',{'call_number':1,'pid':os.getpid(),'time_unix':time.time(),
            'model_sha256':pin(HERE/'model.json'),'scaling_sha256':pin(HERE/'scaling.json'),
            'method':METHOD,'options':OPTIONS,'all77_bounds_free':True,'auxiliary_optimization_calls':0})
        result=linprog(c,A_ub=A,b_ub=b,bounds=[(None,None)]*77,method=METHOD,options=OPTIONS)
        raw=safe_native(dict(result));write(HERE/'raw-result.json',raw)
        limit(start);stage='fixed_exact_reconstruction'
        exact=reconstruct(raw,model,alg);write(HERE/'exact-reconstruction.json',exact)
        dual=exact.get('exact_dual');primal=exact.get('exact_primal')
        gooddual=bool(dual and dual['checks']['valid']);goodprimal=bool(primal and primal['checks']['valid'])
        lower=gooddual and F(dual['checks']['raw_lower_bound'])>=model['target']
        below=goodprimal and F(primal['checks']['raw_objective'])<model['target']
        assert not (lower and below),'contradictory_exact_certificates'
        outcome='Lower' if lower else 'Below' if below else 'inconclusive_fixed_discovery_no_decisive_exact_certificate'
        if lower:write(HERE/'certificate.json',{'kind':'Lower','raw_row_weights':dual['raw_row_weights'],
            'target':str(model['target']),'checks':dual['checks'],'model_sha256':pin(HERE/'model.json'),
            'valid_dual_sufficient_even_if_native_primal_reconstruction_fails':True})
        if below:write(HERE/'certificate.json',{'kind':'Below','raw77':primal['raw77'],'checks':primal['checks'],
            'target':str(model['target']),'model_sha256':pin(HERE/'model.json'),'actual_F_counterexample':False})
        after={name:pin(ROOT/name) for name in refs};assert after==refs and runtime_hashes(runtime)==external
        summary={'schema':'M-one-original-component-envelope-result-v1','passed':lower or below,'outcome':outcome,
            'pid':os.getpid(),'seconds':time.monotonic()-start,'inputs_sha256_start':refs,'inputs_sha256_end':after,
            'external_runtime_sha256_start':external,'external_runtime_sha256_end':runtime_hashes(runtime),
            'linprog_calls':calls,'auxiliary_optimization_calls':0,'candidate_support_trials':1,'precision_retries':0,
            'native_status_not_mathematical_evidence':raw.get('status'),'exact_dual_valid':gooddual,'exact_primal_valid':goodprimal,
            'fixed_pair_only':True,'component_model_lower_proven_by_exact_certificate':lower,
            'below_refutes_only_fixed_component_polyhedral_lower_model':below,
            'model_sha256':pin(HERE/'model.json'),'certificate_sha256':pin(HERE/'certificate.json') if lower or below else None,
            'new_FS_or_anchors_or_kernel_queries_or_Lean_runs':0,'independent_review_pending':True,
            'new_global_floor_or_unconditional_kappa_proven':False,'website_source_and_total_runtime_budget':'unknown',
            'website_submission_ready':False,'automatic_retry_allowed':False}
        write(HERE/'result.json',summary)
        print(json.dumps({'outcome':outcome,'passed':lower or below,'seconds':summary['seconds'],'linprog_calls':calls}),flush=True)
    except BaseException as exc:
        write(HERE/'failure.json',{'passed':False,'stage':stage,'error':repr(exc),'traceback':traceback.format_exc(),
            'pid':os.getpid(),'seconds':time.monotonic()-start,'linprog_calls_started':calls,
            'inputs_sha256_start':refs,'inputs_sha256_end':{name:pin(ROOT/name) for name in refs},
            'external_runtime_sha256_start':external,
            'external_runtime_sha256_end':runtime_hashes(runtime,False) if runtime else {},'automatic_retry_allowed':False})
        raise

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--execute-authorized-fixed-M',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');a=ap.parse_args()
    if not a.execute_authorized_fixed_M:
        print(json.dumps({'prepared_only':True,'models_or_matrices_built':0,'linprog_calls':0}));return
    assert a.gate and a.gate_sha256;execute(checked(a.gate),a.gate_sha256)

if __name__=='__main__':main()
