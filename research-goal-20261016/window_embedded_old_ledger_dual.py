"""Extract and exactly replay a dual upper bound for the fixed ledger LP.

The same ten-column instance is reconstructed from its saved rational
embedding data. A second numerical solve supplies only a dual hint. Its
nonnegative rational rounding is repaired and all ten column inequalities
are checked exactly. This proves no-go for this specified embedding class,
not for new ledgers with additional analytic information.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,math
import numpy as np
from scipy.optimize import linprog

HERE=Path(__file__).resolve().parent

def main():
    source=HERE/'window-embedded-old-ledger-pilot.json'
    output=HERE/'window-embedded-old-ledger-dual.json';assert not output.exists()
    d=json.loads(source.read_bytes());c=F(d['old_floor']);H=F(d['old_window_H']);K=F(d['target_kappa'])
    A=[[F(col['rank_masses'][s]) for col in d['embeddings']] for s in range(9)]
    objective=[K*c-sum(map(F,col['pressure'])) for col in d['embeddings']]
    fit=linprog(-np.array(list(map(float,objective))),A_ub=np.array([[float(x) for x in row] for row in A]),
        b_ub=np.full(9,2.),bounds=[(0,None)]*10,method='highs-ipm',options={'time_limit':45.})
    assert fit.success
    den=10**18;y=[F(max(0,math.ceil(-float(v)*den)),den) for v in fit.ineqlin.marginals]
    deficit=max([F(0)]+[(objective[j]-sum(A[s][j]*y[s] for s in range(9)))/sum(A[s][j] for s in range(9)) for j in range(10)])
    y=[v+deficit for v in y]
    column_slacks=[sum(A[s][j]*y[s] for s in range(9))-objective[j] for j in range(10)]
    assert all(v>=0 for v in y+column_slacks)
    upper=2*sum(y);gap=K-H-upper;assert gap>0
    out={'scope':__doc__,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'nonnegative_rational_dual':list(map(str,y)),'exact_ten_column_slacks':list(map(str,column_slacks)),
        'linear_objective_upper':str(upper),'needed_objective':str(K-H),
        'strict_shortfall':str(gap),'strict_shortfall_hint':float(gap),
        'proof':'sum_j lambda_j*(K*c-B_j) <= sum_s y_s*sum_j A_sj*lambda_j <= 2*sum_s y_s < K-H',
        'denominator_condition':'1-c*sum(lambda)>0',
        'all_admissible_nonnegative_ten_embedding_ratios_below_goal':True,
        'new_zero_proportion_proven':False}
    output.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'exact_dual_passed':True,'strict_shortfall_hint':float(gap)}))

if __name__=='__main__':main()
