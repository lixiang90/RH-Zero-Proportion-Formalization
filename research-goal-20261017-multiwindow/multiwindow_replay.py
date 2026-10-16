"""Read-only independent stdlib audit of the exact multiwindow ingredients.

Use different Taylor lengths and Fraction LDL (producer used Bareiss).
Verify one-frame 24-mode domination, actual fixed rational profile L1,
quadratic H intervals and the common short-pair payment arithmetic.
No producer/numerical import.  The finite LP stays floating discovery.
Default read-only; --write-receipt creates an absent receipt only.
"""
from pathlib import Path
from fractions import Fraction as F
from math import comb,factorial,lcm
import argparse,hashlib,json,sys,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OUT=HERE/'multiwindow-replay.json'
sys.set_int_max_str_digits(0)
PI_LO=F(314159265358979323846,10**20);PI_HI=F(314159265358979323847,10**20)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def interval_scale(pair,c):return (pair[0]*c,pair[1]*c) if c>=0 else (pair[1]*c,pair[0]*c)
def sinc_interval(x2,shift=False):
    def power(r):
        if not shift:return x2[0]**r,x2[1]**r
        return tuple(sum(F(comb(2*r,2*j),2**j)*x2[k]**(r-j) for j in range(r+1)) for k in range(2))
    lower=sum(interval_scale(power(r),F((-1)**r,factorial(2*r+1)))[0] for r in range(42))
    upper=sum(interval_scale(power(r),F((-1)**r,factorial(2*r+1)))[1] for r in range(43))
    return lower,upper
def H_interval(cs):
    clo=sum(F((-1)**r,2**r*factorial(2*r)) for r in range(42));chi=sum(F((-1)**r,2**r*factorial(2*r)) for r in range(43))
    zlo=sum(F((-1)**r,2**r*factorial(2*r+1)) for r in range(42));zhi=sum(F((-1)**r,2**r*factorial(2*r+1)) for r in range(43))
    plo=sum(c*c*(F(1,2)-1/(4*PI_LO**2*j*j)) for j,c in enumerate(cs,1));phi=sum(c*c*(F(1,2)-1/(4*PI_HI**2*j*j)) for j,c in enumerate(cs,1))
    return F(3,2)-chi/zlo-phi/zlo**2,F(3,2)-clo/zhi-plo/zhi**2


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write-receipt',action='store_true');args=parser.parse_args();began=time.monotonic()
    if args.write_receipt:assert not OUT.exists()
    paths=[Path(__file__),HERE/'multiwindow-same-ledger-obstruction.json',HERE/'multiwindow-fixed-pair-pilot.json',
        HERE/'multiwindow-diagnostic.json']
    proof,pilot,diagnostic=[json.loads(p.read_bytes()) for p in paths[1:]]
    for report in [proof,pilot,diagnostic]:
        assert report['source_sha256_start']==report['source_sha256_end']
        for relative,h in report['source_sha256_start'].items():
            p=ROOT/relative;assert sha(p)==h
            if p not in paths:paths.append(p)
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    archived=json.loads((ROOT/'research-20261016-followup/window_reweight_challenge.json').read_bytes())
    g=[F(str(v)) for v in archived['best_gaps']];assert list(map(str,g))==proof['frame_gaps']
    weights=[F(v,params['denominator']) for i,j,v in params['a_upper']];assert all(a>=0 for a in weights)
    assert weights==list(map(F,proof['pair_weights']))
    for rank in range(1,10):assert sum(a for a,(i,j,_) in zip(weights,params['a_upper']) if j-i==rank)<=2
    spans=[sum(g[i:j]) for i,j,_ in params['a_upper']];assert list(map(str,spans))==proof['pair_span_arguments']
    rows=[[F(v) for v in row] for row in proof['quantized_cosine_Fourier_basis']];assert len(rows)==45 and all(len(row)==24 for row in rows)
    error=F(proof['basis_error_upper']);maxentry=max(abs(v) for row in rows for v in row)
    # Cache by x: unlike the producer, compute the interval only once per span.
    for x,row in zip(spans,rows):
        integer=(x+F(1,2)).numerator//(x+F(1,2)).denominator;r=x-integer
        si=sinc_interval((PI_LO**2*r*r,PI_HI**2*r*r))
        for j,z in enumerate(row,1):
            if x==j:lo=hi=F(1,2)
            elif x==0:lo=hi=F(0)
            else:lo,hi=interval_scale(si,F((-1)**(j+integer))*x*r/(x*x-j*j))
            assert max(abs(z-lo),abs(z-hi))<error
    delta=F(proof['operator_Q_error_upper']);entryerror=sum(weights)*(2*maxentry*error+error**2)
    assert str(maxentry)==proof['max_quantized_basis_entry_abs'] and str(entryerror)==proof['entrywise_Q_error_upper'] and 24*entryerror<delta
    T=F(proof['comparison_constant']);assert T==F(11,10)
    elow=[F(1,2)-1/(4*PI_LO**2*j*j) for j in range(1,25)];assert list(map(str,elow))==proof['energy_penalty_diagonal_lower']
    Q=[[sum(a*row[i]*row[j] for a,row in zip(weights,rows)) for j in range(24)] for i in range(24)]
    P=[[(T*elow[i]-delta if i==j else F(0))-Q[i][j] for j in range(24)] for i in range(24)]
    denominator=1
    for row in P:
        for v in row:denominator=lcm(denominator,v.denominator)
    assert str(denominator)==proof['integer_matrix_denominator']
    integer=[[int(v*denominator) for v in row] for row in P]
    assert hashlib.sha256(json.dumps(integer,separators=(',',':')).encode()).hexdigest()==proof['integer_matrix_sha256']
    product=F(1);least=None
    for k in range(24):
        pivot=P[k][k];assert pivot>0;product*=pivot;least=pivot if least is None else min(least,pivot)
        assert product*denominator**(k+1)==F(proof['positive_leading_minors'][k])
        for i in range(k+1,24):
            for j in range(i,24):P[i][j]=P[j][i]=P[i][j]-P[i][k]*P[j][k]/pivot
    K=F(proof['target']);assert K==F(pilot['target']) and 1-K*T==F(proof['strict_variance_loss_coefficient'])>0
    mean=[F(v,10**9) for v in params['window_coefficient_numerators_1e9']];profiles=[list(map(F,row)) for row in pilot['profile_coefficients']]
    eps=F(pilot['epsilon']);q=list(map(F,pilot['perturbation_q']));assert eps==F(1,100) and q==[F(1),F(1)]+[F(0)]*22
    assert profiles==[[u+sign*eps*v for u,v in zip(mean,q)] for sign in [-1,1]]
    assert all(sum(map(abs,p))==sum(map(abs,mean))==F(78742791,10**9)<F(2,25) for p in profiles)
    assert all((profiles[0][j]**2+profiles[1][j]**2)/2==mean[j]**2+eps**2*q[j]**2 for j in range(24))
    for profile,stored in zip(profiles,pilot['each_profile_H_intervals']):
        lo,hi=H_interval(profile);assert F(stored[0])<=lo<=hi<=F(stored[1])
    cut=F(pilot['separation']);x2=PI_LO**2*cut**2,PI_HI**2*cut**2;B=sinc_interval(x2,True);si=sinc_interval(x2)
    zlo=sum(F((-1)**r,2**r*factorial(2*r+1)) for r in range(42));zhi=sum(F((-1)**r,2**r*factorial(2*r+1)) for r in range(43))
    pairfloors=[]
    for profile,record in zip(profiles,pilot['each_profile_short_pair_endpoint']):
        coefficient=sum(c*(-1)**j*cut**2/(cut**2-j*j) for j,c in enumerate(profile,1));perturb=interval_scale(si,coefficient)
        klo,khi=(B[0]+perturb[0])/zhi,(B[1]+perturb[1])/zlo;assert klo>0
        assert F(record['kernel_lower'])<=klo and F(record['w_lower'])<=klo**2<=khi**2<F(record['w_lower'])+F(1,10**12)
        pairfloors.append(F(record['w_lower']))
    assert F(pilot['joint_short_pair_floor_lower'])==sum(min(F(1),2*w) for w in pairfloors)/4
    assert F(pilot['average_H_lower'])==sum(F(row[0]) for row in pilot['each_profile_H_intervals'])/2
    assert pilot['solver_calls']==1 and pilot['LP_status']==0 and not pilot['candidate_strictly_exceeds_target_on_samples_hint']
    assert not pilot['actual_profile_derivative_PV_and_budget_checks_completed'] and not pilot['actual_AdmWindow_formalized']
    assert not any(n.split('.')[0] in ['numpy','scipy','scs'] for n in sys.modules)
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==initial
    out={'scope':__doc__,'status':'exact_same_ledger_24_mode_obstruction_and_fixed_profile_ingredients_verified',
        'source_sha256_start':initial,'source_sha256_end':final,'all_sources_unchanged':True,
        'basis_entries_interval_checked':45*24,'strict_positive_LDL_pivots':24,'minimum_positive_LDL_pivot':str(least),
        'comparison_constant':str(T),'strict_target_variance_loss_coefficient':str(1-K*T),
        'fixed_profiles_exact_L1':'78742791/1000000000','fixed_profile_short_pair_floors':list(map(str,pairfloors)),
        'fixed_profile_actual_AdmWindow_and_PV_obligations_pending':True,'finite_LP_is_float_only':True,
        'read_only_default':True,'pure_stdlib_replay':True,'solver_calls':0,'Lean_invocations':0,
        'different_ledger_route_excluded':False,'global_floor_proven':False,'new_zero_proportion_proven':False,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    if args.write_receipt:OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['status','basis_entries_interval_checked','strict_positive_LDL_pivots','fixed_profile_actual_AdmWindow_and_PV_obligations_pending','elapsed_milliseconds']}),flush=True)


if __name__=='__main__':main()
