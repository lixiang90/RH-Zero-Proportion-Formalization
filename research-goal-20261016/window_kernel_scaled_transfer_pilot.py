"""One fixed-r=24/25 sampled scalar transfer LP, not a uniform certificate.

The old floor is globally quantified over nonnegative gaps, so r*newSEP need
not exceed an internal old cover separation.  No scaled counting theorem is
assumed: the old floor is used as an inequality in the unchanged new model.
One HiGHS-IPM call, <=45 seconds; no r sweep or nine-dimensional optimizer.

For x>=T, y=r*x and old coefficient mass A=sum|c_j|, the finite sinc identity
gives |k_old(y)| <= [1/(1-1/(4*r*T))+A/(1-144/(r*T)^2)]/(pi*Z*r*x).
Use sqrt(2)/(2*pi)<1/4, pi>=3, Z>=11/12 to obtain rational D/x.
Consequently w_old(r*x)<=D^2/x^2.  Nonnegative q and old weights imply
q*x-A_e*D^2/x^2 is increasing: d_e<=T*q_e-A_e*D^2/T^2 certifies the tail.
All finite-domain constraints in this pilot are samples only.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib, json, time, traceback
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from window_kernel_floor_transfer_design import parse_old

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PARAM = ROOT/'research-20261016-followup/window_reweight_rational.json'
OLD = ROOT/'GramDefect20261015/Core.lean'
OUT = HERE/'window-kernel-scaled-transfer-pilot.json'
R, SEP, T = F(24, 25), F(123, 128), F(128)
PAIRS = [(i, j) for i in range(10) for j in range(i+1, 10)]
V = 100  # 10 nonnegative lambdas, 45 nonnegative q, 45 unrestricted d.


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def square_kernel(points, coeff):
    theta = np.sqrt(2)/2
    freq = np.r_[theta/np.pi, np.arange(1, len(coeff))]
    values = (np.sinc(points[:, None]+freq)+np.sinc(points[:, None]-freq))@coeff
    return (values/(2*np.sinc(theta/np.pi)))**2


def sample_grid(rank):
    low = rank*SEP
    # Dense through the first sixteen wells, then one-eighth spacing to T.
    dense = [F(k, 64) for k in range((low*64).__ceil__(), 16*64+1)]
    tail = [F(k, 8) for k in range(16*8+1, int(T)*8+1)]
    return sorted(set([low]+dense+tail))


def main():
    assert not OUT.exists(), 'One-shot pilot: preserve the existing receipt.'
    started = time.monotonic()
    watched = [Path(__file__), PARAM, OLD,
               HERE/'window_kernel_floor_transfer_design.py',
               HERE/'window-kernel-floor-transfer-design.json',
               HERE/'window_kernel_floor_transfer_note.txt',
               ROOT/'research-20261016-followup/global_periodic_upper_bound.py']
    pins = {str(p.relative_to(ROOT)).replace('\\', '/'): sha(p) for p in watched}
    params = json.loads(PARAM.read_bytes())
    old = parse_old(OLD)
    old_b = old['b']
    new_b = [F(b, params['denominator']) for b in params['b_numerators']]
    new_a = {(i, j): F(a, params['denominator']) for i, j, a in params['a_upper']}
    required = F(json.loads((HERE/'window-kernel-floor-transfer-design.json').read_bytes())['bounds'][0]['required_floor_to_match_archived_record'])
    old_coeff = np.array([old['coeff'][j]/10**9 for j in range(13)])
    new_coeff = np.r_[1., np.array(params['window_coefficient_numerators_1e9'])/10**9]
    incidence = np.array([[i<=k<j for k in range(9)] for i, j in PAIRS], dtype=float)
    a = np.zeros((45, 10)); p = [[F(0) for _ in range(9)] for _ in range(10)]
    for deleted in range(10):
        vertices = [i for i in range(10) if i != deleted]
        for k in range(8):
            for l in range(vertices[k], vertices[k+1]): p[deleted][l] += old_b[k]
        for (i, j), weight in old['a'].items():
            a[PAIRS.index((vertices[i], vertices[j])), deleted] = float(weight)
    sums = [sum(row) for row in p]
    mass = sum((F(abs(old['coeff'][j]), 10**9) for j in range(1, 13)), F(0))
    D = F(4, 11)/R*(1/(1-1/(4*R*T))+mass/(1-F(144)/(R*T)**2))
    tail_w = D**2/T**2
    out = {'scope': __doc__, 'phase': 'initializing', 'fixed_scaling': str(R),
           'new_separation': str(SEP), 'scaled_new_separation': str(R*SEP),
           'old_floor_domain': old['floor_theorem_statement'],
           'old_floor_domain_satisfied_for_all_nonnegative_new_gaps': True,
           'tail_start': str(T), 'old_coefficient_absolute_mass': str(mass),
           'tail_amplitude_D': str(D), 'tail_w_bound_at_T': str(tail_w),
           'source_sha256_start': pins, 'LP_method': 'highs-ipm',
           'LP_time_limit_seconds': 45, 'maximum_LP_calls': 1,
           'variables': V, 'required_floor': str(required),
           'sample_rule': 'rank*SEP plus 1/64 grid up to 16 then 1/8 grid through 128',
           'uniform_majorization_proven': False, 'Lean_checked': False,
           'new_zero_proportion_proven': False}
    def save():
        final = {str(p.relative_to(ROOT)).replace('\\', '/'): sha(p) for p in watched}
        assert final == pins
        out['source_sha256_end'] = final
        out['all_sources_unchanged'] = True
        out['seconds_hint'] = time.monotonic()-started
        OUT.write_text(json.dumps(out, indent=2, allow_nan=False)+'\n', encoding='utf8')
    save()
    try:
        rowind=[]; colind=[]; values=[]; bounds=[]; labels=[]
        def append(indices, vals, bound, label):
            row=len(bounds)
            for index, value in zip(indices, vals):
                if value:
                    rowind.append(row); colind.append(index); values.append(float(value))
            bounds.append(float(bound)); labels.append(label)
        # Exact-rational pressure vectors are converted to float only here.
        for k in range(9):
            append(list(range(10))+[10+e for e in range(45)],
                   [R*p[d][k] for d in range(10)]+list(incidence[:,k]), new_b[k], ['pressure',k])
        grids = {rank: sample_grid(rank) for rank in range(1, 10)}
        out['sample_counts_by_rank'] = {str(rank): len(grid) for rank,grid in grids.items()}
        samples = {}
        for rank, grid in grids.items():
            x = np.array(list(map(float, grid)))
            samples[rank] = (x, square_kernel(x, new_coeff), square_kernel(float(R)*x, old_coeff))
        for e,(i,j) in enumerate(PAIRS):
            rank=j-i; x,wn,wo=samples[rank]
            active=np.flatnonzero(a[e])
            for k in range(len(x)):
                append(active.tolist()+[10+e,55+e], list(a[e,active]*wo[k])+[-x[k],1.],
                       float(new_a[i,j])*wn[k], ['sample',e,k])
            append(active.tolist()+[10+e,55+e], list(a[e,active]*float(tail_w))+[-float(T),1.],
                   0., ['analytic_tail',e])
        matrix=coo_matrix((values,(rowind,colind)), shape=(len(bounds),V)).tocsr()
        bound=np.array(bounds)
        objective=np.r_[[float(old['c']-SEP*R*sums[d]) for d in range(10)],
                         [-float(SEP*(j-i)) for i,j in PAIRS],np.ones(45)]
        constant=float(SEP*sum(new_b))
        out.update({'phase':'LP_running', 'sample_rows':sum(v=='sample' for v, *_ in labels),
                    'analytic_tail_rows':45, 'pressure_rows':9, 'total_rows':len(bounds),
                    'matrix_nonzero_count':int(matrix.nnz)})
        save(); tick=time.monotonic()
        fit=linprog(-objective,A_ub=matrix,b_ub=bound,
                    bounds=[(0,None)]*55+[(None,None)]*45,method='highs-ipm',
                    options={'time_limit':45.,'primal_feasibility_tolerance':1e-9,
                             'dual_feasibility_tolerance':1e-9,'ipm_optimality_tolerance':1e-9})
        out['LP']={'status':int(fit.status),'success':bool(fit.success),'message':str(fit.message),
                   'seconds_hint':time.monotonic()-tick,'iterations':int(fit.nit)}
        if fit.x is not None and np.all(np.isfinite(fit.x)):
            floor=constant+float(objective@fit.x)
            residue=np.array(list(map(float,new_b)))-float(R)*np.array(p,dtype=float).T@fit.x[:10]-incidence.T@fit.x[10:55]
            out['LP'].update({'floor_hint':floor,'exceeds_required_hint':floor>float(required),
                'strict_floor_gap_hint':floor-float(required),'lambda_sum_hint':float(sum(fit.x[:10])),
                'lambda_by_deleted_vertex_hint':fit.x[:10].tolist(),
                'q_by_pair_hint':[[i,j,float(fit.x[10+e])] for e,(i,j) in enumerate(PAIRS)],
                'd_by_pair_hint':[[i,j,float(fit.x[55+e])] for e,(i,j) in enumerate(PAIRS)],
                'pressure_residue_hint':residue.tolist(),
                'minimum_sampled_row_slack_hint':float(np.min(bound-matrix@fit.x)),
                'counting_ratio_percent_hint':100*float((F(params['window_H_lower'])-sum(new_b)))/(1-floor),
                'raw_primal_hint':fit.x.tolist()})
            if fit.success:
                nz=np.flatnonzero(abs(fit.ineqlin.marginals)>1e-13)
                out['LP']['nonzero_row_duals_hint']=[{'row':int(k),'label':labels[k],
                    'weight':float(-fit.ineqlin.marginals[k])} for k in nz]
        out['phase']='completed_one_fixed_r_LP';save()
    except BaseException as exc:
        out['phase']='exception_stopped';out['exception']=repr(exc);out['traceback']=traceback.format_exc();save();raise
    print(json.dumps({'phase':out['phase'],'rows':out.get('total_rows'),
        'LP':{k:v for k,v in out.get('LP',{}).items() if k not in ['q_by_pair_hint','d_by_pair_hint','raw_primal_hint','nonzero_row_duals_hint']},
        'uniform_majorization_proven':False},indent=2),flush=True)


if __name__=='__main__':
    if not __debug__: raise RuntimeError('Assertions must remain enabled')
    main()
