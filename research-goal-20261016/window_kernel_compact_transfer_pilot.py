"""One fixed-r=.96 compact scalar-transfer LP with one shared pressure payment.

Discovery only: finite scalar samples are not uniform interval certificates.
One HiGHS-IPM call <=45 seconds; no scale sweep and no nine-dimensional solve.

Assume g>=SEP and F_new(g)<c_ref.  Nonnegative kernel terms imply P_new<c_ref.
For e=(i,j), rank=j-i, minb=min(b_new[i:j]), this implies
rank*SEP <= span_e <= rank*SEP+(c_ref-SEP*B_new)/minb.
For free-sign q_e and nonnegative lambda_d define
R=b_new-r*sum lambda_d*p_d-sum q_e*v_e.  Select a single rho>=0 satisfying
R+rho*b_new>=0 coordinatewise.  Then the residual pressure obeys
R.g >= SEP*sum(R+rho*b_new)-rho*c_ref.
The one rho pays the global pressure budget once, not once per edge.

Old-floor premise is only nonnegative gaps; r=.96 and r*SEP=369/400 are legal.
The final counting model and its window remain unchanged.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib, json, time, traceback
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from window_kernel_floor_transfer_design import parse_old
from window_kernel_scaled_transfer_pilot import square_kernel

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
PARAM=ROOT/'research-20261016-followup/window_reweight_rational.json'
OLD=ROOT/'GramDefect20261015/Core.lean'
OUT=HERE/'window-kernel-compact-transfer-pilot.json'
R=F(24,25);SEP=F(123,128);CREF=F(11,1250)
GOAL_FLOOR=F(5349002676301735733991141164305905087919557,
             608906172631303644195215758819391372800000000)
PAIRS=[(i,j) for i in range(10) for j in range(i+1,10)]
V=101  # lambda[10]>=0, q[45] free, d[45] free, shared rho>=0.


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    assert not OUT.exists(),'One-shot pilot: preserve the existing receipt.'
    started=time.monotonic()
    watched=[Path(__file__),PARAM,OLD,HERE/'window_kernel_floor_transfer_design.py',
             HERE/'window-kernel-floor-transfer-design.json',HERE/'window_kernel_floor_transfer_note.txt',
             HERE/'window_kernel_scaled_transfer_pilot.py',HERE/'window-kernel-scaled-transfer-pilot.json',
             ROOT/'research-20261016-followup/global_periodic_upper_bound.py',
             ROOT/'research-20261016-w10-cert/current-record-review.json']
    pins={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in watched}
    params=json.loads(PARAM.read_bytes());old=parse_old(OLD)
    new_b=[F(v,params['denominator']) for v in params['b_numerators']];B=sum(new_b)
    new_a={(i,j):F(v,params['denominator']) for i,j,v in params['a_upper']}
    h=F(params['window_H_lower'])
    site=F(json.loads((ROOT/'research-20261016-w10-cert/current-record-review.json').read_bytes())['current_record_exact'])
    match_floor=1-(h-B)/site
    exact_goal_floor=1-(h-B)/(site+F(1,100000))
    # The supplied threshold is 1.47e-22 stricter than exact inversion of the
    # archived rational record.  Preserve it, and record both exact values.
    assert 0<=GOAL_FLOOR-exact_goal_floor<F(1,10**20)
    assert match_floor<GOAL_FLOOR<CREF
    old_coeff=np.array([old['coeff'][j]/10**9 for j in range(13)])
    new_coeff=np.r_[1.,np.array(params['window_coefficient_numerators_1e9'])/10**9]
    incidence=np.array([[i<=k<j for k in range(9)] for i,j in PAIRS],dtype=float)
    a=np.zeros((45,10));p=[[F(0) for _ in range(9)] for _ in range(10)]
    for deleted in range(10):
        vertices=[i for i in range(10) if i!=deleted]
        for k in range(8):
            for l in range(vertices[k],vertices[k+1]):p[deleted][l]+=old['b'][k]
        for (i,j),weight in old['a'].items():
            a[PAIRS.index((vertices[i],vertices[j])),deleted]=float(weight)
    sums=[sum(row) for row in p]
    ranges=[]
    for i,j in PAIRS:
        lo=(j-i)*SEP;hi=lo+(CREF-SEP*B)/min(new_b[i:j])
        assert hi>lo
        ranges.append((lo,hi))
    out={'scope':__doc__,'phase':'initializing','fixed_scaling':str(R),'new_separation':str(SEP),
         'scaled_new_separation':str(R*SEP),'sublevel_energy_threshold':str(CREF),
         'old_floor_theorem':old['floor_theorem_statement'],
         'match_archived_site_floor':str(match_floor),'match_archived_site_floor_hint':float(match_floor),
         'goal_ratio':'archived site ratio + 1/100000 (kappa units); supplied floor is slightly conservative',
         'goal_floor':str(GOAL_FLOOR),'goal_floor_hint':float(GOAL_FLOOR),
         'direct_exact_goal_floor':str(exact_goal_floor),
         'supplied_goal_floor_conservatism':str(GOAL_FLOOR-exact_goal_floor),
         'goal_requires_strictly_exceeding_threshold':True,
         'pair_domains':[[i,j,str(lo),str(hi)] for (i,j),(lo,hi) in zip(PAIRS,ranges)],
         'source_sha256_start':pins,'LP_method':'highs-ipm','LP_time_limit_seconds':45,
         'maximum_LP_calls':1,'variables':V,'free_sign_q':True,'shared_pressure_multipliers':1,
         'sample_rule':'both exact domain endpoints plus 1/64 grid strictly between endpoints',
         'analytic_tail_rows':0,'uniform_majorization_proven':False,'Lean_checked':False,
         'new_zero_proportion_proven':False}
    def save():
        final={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in watched}
        assert final==pins
        out['source_sha256_end']=final;out['all_sources_unchanged']=True
        out['seconds_hint']=time.monotonic()-started
        OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    save()
    try:
        ri=[];ci=[];vv=[];bb=[];labels=[]
        def append(indices,values,bound,label):
            row=len(bb)
            for index,value in zip(indices,values):
                if value:ri.append(row);ci.append(index);vv.append(float(value))
            bb.append(float(bound));labels.append(label)
        # r*P*lambda + Inc*q - rho*b_new <= b_new, with one rho.
        for k in range(9):
            append(list(range(10))+[10+e for e in range(45)]+[100],
                   [R*p[d][k] for d in range(10)]+list(incidence[:,k])+[-new_b[k]],
                   new_b[k],['pressure_shared_rho',k])
        grid_counts=[]
        for e,((i,j),(lo,hi)) in enumerate(zip(PAIRS,ranges)):
            grid=sorted(set([lo,hi]+[F(k,64) for k in range((64*lo).__ceil__(),(64*hi).__floor__()+1)]))
            assert grid[0]==lo and grid[-1]==hi
            x=np.array(list(map(float,grid)))
            wn=square_kernel(x,new_coeff);wo=square_kernel(float(R)*x,old_coeff)
            active=np.flatnonzero(a[e]);grid_counts.append(len(grid))
            for k in range(len(x)):
                append(active.tolist()+[10+e,55+e],list(a[e,active]*wo[k])+[-x[k],1.],
                       float(new_a[i,j])*wn[k],['sample',e,k])
        matrix=coo_matrix((vv,(ri,ci)),shape=(len(bb),V)).tocsr();bound=np.array(bb)
        objective=np.r_[[float(old['c']-SEP*R*sums[d]) for d in range(10)],
                         [-float(SEP*(j-i)) for i,j in PAIRS],np.ones(45),float(SEP*B-CREF)]
        constant=float(SEP*B)
        out.update({'phase':'LP_running','total_rows':len(bb),'pressure_rows':9,
                    'sample_rows':sum(grid_counts),'sample_counts_by_pair':grid_counts,
                    'matrix_nonzero_count':int(matrix.nnz)})
        save();tick=time.monotonic()
        fit=linprog(-objective,A_ub=matrix,b_ub=bound,
                    bounds=[(0,None)]*10+[(None,None)]*90+[(0,None)],method='highs-ipm',
                    options={'time_limit':45.,'primal_feasibility_tolerance':1e-9,
                             'dual_feasibility_tolerance':1e-9,'ipm_optimality_tolerance':1e-9})
        out['LP']={'status':int(fit.status),'success':bool(fit.success),'message':str(fit.message),
                   'seconds_hint':time.monotonic()-tick,'iterations':int(fit.nit)}
        if fit.x is not None and np.all(np.isfinite(fit.x)):
            floor=constant+float(objective@fit.x)
            residue=np.array(list(map(float,new_b)))-float(R)*np.array(p,dtype=float).T@fit.x[:10]-incidence.T@fit.x[10:55]
            shifted=residue+fit.x[100]*np.array(list(map(float,new_b)))
            out['LP'].update({'derived_sublevel_floor_hint':floor,
                'global_floor_after_clamping_to_c_ref_hint':min(float(CREF),floor),
                'exceeds_match_archived_site_floor_hint':floor>float(match_floor),
                'exceeds_goal_floor_hint':floor>float(GOAL_FLOOR),
                'strict_goal_gap_hint':floor-float(GOAL_FLOOR),
                'lambda_sum_hint':float(sum(fit.x[:10])),
                'lambda_by_deleted_vertex_hint':fit.x[:10].tolist(),'shared_rho_hint':float(fit.x[100]),
                'q_by_pair_hint':[[i,j,float(fit.x[10+e])] for e,(i,j) in enumerate(PAIRS)],
                'd_by_pair_hint':[[i,j,float(fit.x[55+e])] for e,(i,j) in enumerate(PAIRS)],
                'pressure_residue_hint':residue.tolist(),'shifted_pressure_residue_hint':shifted.tolist(),
                'minimum_sampled_row_slack_hint':float(np.min(bound-matrix@fit.x)),
                'counting_ratio_percent_hint':100*float(h-B)/(1-min(float(CREF),floor)),
                'raw_primal_hint':fit.x.tolist()})
            if fit.success:
                nz=np.flatnonzero(abs(fit.ineqlin.marginals)>1e-13)
                out['LP']['nonzero_row_duals_hint']=[{'row':int(k),'label':labels[k],
                    'weight':float(-fit.ineqlin.marginals[k])} for k in nz]
        out['phase']='completed_one_fixed_r_compact_LP';save()
    except BaseException as exc:
        out['phase']='exception_stopped';out['exception']=repr(exc);out['traceback']=traceback.format_exc();save();raise
    print(json.dumps({'phase':out['phase'],'rows':out.get('total_rows'),
        'LP':{k:v for k,v in out.get('LP',{}).items() if k not in ['q_by_pair_hint','d_by_pair_hint','raw_primal_hint','nonzero_row_duals_hint']},
        'uniform_majorization_proven':False},indent=2),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
