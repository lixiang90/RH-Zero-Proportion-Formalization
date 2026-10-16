"""Exact one-frame obstruction to symmetric variance with the fixed ledger.

At one frozen coherent best point, Q=sum a B B^T <= (11/10) diag(e).
All 24 mode directions are covered by one rational positive-matrix proof.
This is not a global optimum or a no-go for different ledgers/windows.
"""
from pathlib import Path
from fractions import Fraction as F
from math import floor,lcm
import hashlib,importlib.util,json,sys,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
OUT=HERE/'multiwindow-same-ledger-obstruction.json';sys.set_int_max_str_digits(0)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    assert not OUT.exists();began=time.monotonic()
    paths=[Path(__file__),ROOT/'research-20261016-followup/window_reweight_rational.json',
        ROOT/'research-20261016-followup/window_reweight_challenge.json',ROOT/'research-20261016-followup/window_exact_parameters.py',
        HERE/'multiwindow-diagnostic.json',ROOT/'StructuralGoal20261016/WindowEnergy.lean',ROOT/'StructuralGoal20261016/WindowKernel.lean']
    pins={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    spec=importlib.util.spec_from_file_location('existing_exact_window_interval',paths[3]);ex=importlib.util.module_from_spec(spec);spec.loader.exec_module(ex)
    params=json.loads(paths[1].read_bytes());point=json.loads(paths[2].read_bytes());g=[F(str(v)) for v in point['best_gaps']]
    a=[F(v,params['denominator']) for i,j,v in params['a_upper']];xs=[sum(g[i:j]) for i,j,v in params['a_upper']]
    quantization=10**12;error=F(2,quantization);rows=[];maxentry=F(0)
    for x in xs:
        row=[]
        for j in range(1,25):
            if x==j:interval=(F(1,2),F(1,2))
            elif x==0:interval=(F(0),F(0))
            else:
                n=floor(x+F(1,2));r=x-n
                si=ex.sinc_bounds((ex.PI_LO**2*r*r,ex.PI_HI**2*r*r))
                interval=ex.scale(si,F((-1)**(j+n))*x*r/(x*x-j*j))
            z=F(floor((interval[0]+interval[1])*quantization/2),quantization)
            assert max(abs(z-interval[0]),abs(z-interval[1]))<error
            row.append(z);maxentry=max(maxentry,abs(z))
        rows.append(row)
    delta=F(1,10**8);entryerr=sum(a)*(2*maxentry*error+error**2)
    assert 24*entryerr<delta
    T=F(11,10);elow=[F(1,2)-1/(4*ex.PI_LO**2*j*j) for j in range(1,25)]
    Q=[[sum(weight*row[i]*row[j] for weight,row in zip(a,rows)) for j in range(24)] for i in range(24)]
    P=[[(T*elow[i]-delta if i==j else F(0))-Q[i][j] for j in range(24)] for i in range(24)]
    denominator=1
    for row in P:
        for v in row:denominator=lcm(denominator,v.denominator)
    integer=[[int(v*denominator) for v in row] for row in P]
    digest=hashlib.sha256(json.dumps(integer,separators=(',',':')).encode()).hexdigest();previous=1;minors=[]
    for k in range(24):
        pivot=integer[k][k];assert pivot>0;minors.append(str(pivot))
        for i in range(k+1,24):
            for j in range(i,24):
                numerator=integer[i][j]*pivot-integer[i][k]*integer[k][j];quotient,remainder=divmod(numerator,previous);assert not remainder
                integer[i][j]=integer[j][i]=quotient
        previous=pivot
    target=F(34191001116882886388531117129201664,50760020691785094633026544189453125)+F(1,100000)
    assert target*T<1
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==pins
    result={'scope':__doc__,'status':'exact_24_mode_one_frame_same_ledger_variance_obstruction',
        'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,
        'frame_gaps':list(map(str,g)),'pair_weights':list(map(str,a)),'pair_span_arguments':list(map(str,xs)),
        'basis_definition':'B_j(x)=(sinc_pi(x-j)+sinc_pi(x+j))/2, unnormalized cosine Fourier basis; Z cancels in reward/penalty comparison',
        'quantization_denominator':quantization,'basis_error_upper':str(error),'quantized_cosine_Fourier_basis':[[str(v) for v in row] for row in rows],
        'max_quantized_basis_entry_abs':str(maxentry),'entrywise_Q_error_upper':str(entryerr),'operator_Q_error_upper':str(delta),
        'comparison_constant':str(T),'energy_penalty_diagonal_lower':list(map(str,elow)),
        'integer_matrix_denominator':str(denominator),'integer_matrix_sha256':digest,'positive_leading_minors':minors,
        'target':str(target),'strict_variance_loss_coefficient':str(1-target*T),
        'consequence':'For every q in R^24, sum_e a_e*(sum_j q_j*B_j(x_e))^2 <= (11/10)*sum_j e_j*q_j^2. Hence symmetric same-ledger variance reduces Hbar+K*Fbar(g)-B by at least epsilon^2*(1-11*K/10)*C(q).',
        'pi_interval_input':[str(ex.PI_LO),str(ex.PI_HI)],'optimizer_calls':0,'Lean_invocations':0,
        'global_optimum_claim':False,'different_ledger_route_excluded':False,'new_zero_proportion_proven':False,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    OUT.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'status':result['status'],'matrix_size':24,'strict_positive_leading_minors':len(minors),
        'variance_ratio_upper':'11/10','strict_variance_loss_coefficient_hint':float(1-target*T),'milliseconds':result['elapsed_milliseconds']}),flush=True)


if __name__=='__main__':main()
