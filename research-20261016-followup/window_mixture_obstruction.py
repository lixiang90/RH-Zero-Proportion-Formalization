"""One exact 24-mode obstruction to adding symmetric window variance.

This does not rule out a joint-window improvement at other mean windows or
with different ledgers. It bounds variance reward at one explicit frame.
No floating eigenvalue is used in the exact PSD check.
"""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
from math import floor
import importlib.util,json
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('ex',HERE/'window_exact_parameters.py')
ex=importlib.util.module_from_spec(spec);spec.loader.exec_module(ex)
ROOT=HERE.parent
rec=json.loads((ROOT/'research-20261016/spectral-w10-refined-rational.json').read_text())
g=[F(v,10**6) for v in [1974780,1040178,1968258,1042558,1968678,1042587,1965446,1036437,1032176]]
weights=[F(v,rec['denominator']) for i,j,v in rec['a_upper']]
xs=[sum(g[i:j],F(0)) for i,j,v in rec['a_upper']]
M=24;D=10**12

def q_bounds(x,j):
    if x==j:return F(1,2),F(1,2)
    if x==0:return F(0),F(0)
    n=floor(x+F(1,2));r=x-n
    lo,hi=ex.sinc_bounds((ex.PI_LO**2*r*r,ex.PI_HI**2*r*r))
    fac=F((-1)**(j+n))*x*r/(x*x-j*j)
    return ex.scale((lo,hi),fac)

qs=[];err=F(0);maxq=F(0)
for x in xs:
    row=[]
    for j in range(1,M+1):
        lo,hi=q_bounds(x,j);z=F(floor((lo+hi)*D/2),D)
        row.append(z);err=max(err,abs(z-lo),abs(z-hi));maxq=max(maxq,abs(z))
    qs.append(row)
assert err<F(2,D)
# Entrywise error bound becomes an operator error via row sums.
delta=F(1,10**8)
assert M*sum(weights)*(2*maxq*F(2,D)+F(2,D)**2)<delta
Q=[[sum((a*q[i]*q[j] for a,q in zip(weights,qs)),F(0)) for j in range(M)] for i in range(M)]
T=F(7,5)
exactE=[F(1,2)-1/(4*ex.PI_LO**2*j*j) for j in range(1,M+1)]
E=[F(floor(e*D),D) for e in exactE]
assert all(e<=v for e,v in zip(E,exactE))
P=[[(T*E[i]-delta if i==j else F(0))-Q[i][j] for j in range(M)] for i in range(M)]
# Exact LDL/Schur elimination: positive pivots certify positive definiteness.
pivots=[]
for k in range(M):
    pivot=P[k][k];assert pivot>0;pivots.append(pivot)
    for i in range(k+1,M):
        for j in range(i,M):
            P[i][j]-=P[i][k]*P[j][k]/pivot;P[j][i]=P[i][j]
record={'status':'EXACT_24_MODE_FRAME_VARIANCE_OBSTRUCTION_NOT_A_GLOBAL_OPTIMUM',
    'frame_gaps_exact':[str(v) for v in g],'old_weight_source':'research-20261016/spectral-w10-refined-rational.json',
    'number_of_cosine_modes':M,'reward_energy_ratio_upper':str(T),
    'target_kappa_for_comparison':'67/100',
    'strict_bad_direction_margin':'31/500',
    'statement':'For q(t)=sum_{j=1}^24 d_j*cos(2*pi*j*t), this frame satisfies sum_pairs a_ij*qhat(x_j-x_i)^2 <= (7/5)*sum_j d_j^2*(1/2-1/(4*pi^2*j^2)). Thus at any target kappa>=67/100 but <5/7, the symmetric variance term in H+kappa*F is strictly negative. The displayed margin 31/500 is for kappa=67/100; for actual .6736 it is about .0569.',
    'qualifier':'This is one frame, one frozen ledger and 24-mode perturbations. It does not prove that all mixed windows fail globally, nor that a new mean window cannot improve.',
    'kernel_entry_quantization':D,'kernel_entry_abs_error_upper':str(F(2,D)),
    'matrix_perturbation_norm_upper_decimal':float(delta),
    'LDL_positive_pivots':len(pivots),'minimum_exact_pivot_decimal':float(min(pivots)),
    'all_fraction_checks_passed':True,'Lean_checked':False}
# At kappa=67/100: 1-kappa*(7/5)=31/500 exactly.
assert F(1)-F(67,100)*T==F(31,500)
(HERE/'window_mixture_obstruction.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf8')
print(json.dumps({k:record[k] for k in ['status','reward_energy_ratio_upper','LDL_positive_pivots','minimum_exact_pivot_decimal','matrix_perturbation_norm_upper_decimal']},indent=2))
