"""Independent stdlib replay of the quartic relaxation obstruction.

No producer imports.  Recompute every rational inequality at both the
unadjusted lifted point and its factorized first moments.  For the lifted
point, an independent Fraction LDL algorithm checks strict positivity and
compares pivot products with all stored integer Bareiss leading minors.
The static Taylor-model replay is separately pinned.  This certifies an
outer relaxation obstruction only, never an actual kernel counterexample.
"""
from pathlib import Path
from fractions import Fraction as F
from math import lcm
import gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
OUT=HERE/'quartic-result-replay.json'
sys.set_int_max_str_digits(0)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def row_checks(rows,x):
    families={};violations=[]
    for index,row in enumerate(rows):
        slack=F(row['bound'])-sum(F(q)*x[k] for k,q in row['coefficients']);normalized=slack/F(row['scale']);family=row['meta'][0]
        entry={'row':index,'meta':row['meta'],'slack':str(slack),'normalized_slack':str(normalized)}
        if family not in families or normalized<F(families[family]['normalized_slack']):families[family]=entry
        if slack<0:violations.append(entry)
    return families,violations
def exact_matrix(block,x):
    n=block['size'];M=[[F(0) for _ in range(n)] for _ in range(n)]
    for i,j,form in block['entries']:
        M[i][j]=M[j][i]=F(form['constant'])+sum(F(q)*x[k] for k,q in form['coefficients'])
    return M
def verify_LDL(M,witness):
    n=len(M);assert n==witness['size'] and witness['strictly_positive_definite']
    denominator=1
    for row in M:
        for x in row:denominator=lcm(denominator,x.denominator)
    assert str(denominator)==witness['integer_matrix_denominator']
    integer=[[int(x*denominator) for x in row] for row in M]
    assert hashlib.sha256(json.dumps(integer,separators=(',',':')).encode()).hexdigest()==witness['integer_matrix_sha256']
    # Fraction Schur-complement elimination, distinct from producer Bareiss.
    schur=[row.copy() for row in M];product=F(1);pivots=[]
    for k in range(n):
        pivot=schur[k][k];assert pivot>0,(witness['name'],k,pivot)
        pivots.append(pivot);product*=pivot
        assert product*denominator**(k+1)==F(witness['positive_leading_minors'][k])
        for i in range(k+1,n):
            for j in range(i,n):
                new=schur[i][j]-schur[i][k]*schur[j][k]/pivot
                schur[i][j]=schur[j][i]=new
    return min(pivots)


def main():
    assert not OUT.exists();began=time.monotonic()
    names=['quartic-model.json.gz','quartic-build.json','quartic-replay.json','quartic-cone.json',
        'quartic-rankone.json','quartic-exact-primal.json']
    paths=[Path(__file__)]+[HERE/n for n in names]
    modelraw=gzip.decompress((HERE/names[0]).read_bytes());model=json.loads(modelraw)
    build,static,cone,rankone,proof=[json.loads((HERE/n).read_bytes()) for n in names[1:]]
    for report in [build,static,cone,rankone,proof]:
        start=report.get('source_sha256_start',report.get('input_sha256_start'))
        end=report.get('source_sha256_end',report.get('input_sha256_end'));assert start==end
        for relative,digest in start.items():
            p=ROOT/relative;assert sha(p)==digest,(relative,digest)
            if p not in paths:paths.append(p)
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    assert sha(HERE/names[0])==build['model_compressed_sha256'] and hashlib.sha256(modelraw).hexdigest()==build['model_uncompressed_sha256']
    assert static['status']=='shared_quartic_coefficients_rows_and_localizers_independently_verified'
    assert proof['status']=='strict_exact_shared_quartic_outer_relaxation_feasible'
    assert not cone['any_positive_hint'] and cone['phase']=='completed_single_shared_quartic_SCS'
    assert model['path']==proof['path']==rankone['path']==cone['path']
    x=[F(str(v)) for v in cone['raw_primal_hint'][:714]]+[F(0)]
    assert x[:714]==list(map(F,proof['rational_714_moments'])) and proof['energy_slack']=='0'
    families,violations=row_checks(model['linear_rows'],x)
    assert families==proof['minimum_by_row_family'] and violations==proof['violations']==[]
    assert proof['linear_rows_checked']==len(model['linear_rows'])==5795
    assert len(proof['strict_PD_blocks'])==len(model['PSD_blocks'])==47
    least_pivots=[]
    for block,witness in zip(model['PSD_blocks'],proof['strict_PD_blocks']):
        assert block['name']==witness['name']
        least_pivots.append(str(verify_LDL(exact_matrix(block,x),witness)))
    # Factorized mean point is a separate one-shot diagnosis, not a point search.
    y=x[:9];assert list(map(F,rankone['normalized_gap_point']))==y
    values=[]
    for monomial in model['monomials']:
        value=F(1)
        for r in monomial:value*=y[r]
        values.append(value)
    rankx=values[1:]+[F(0)];rf,rv=row_checks(model['linear_rows'],rankx)
    assert rf==rankone['minimum_by_row_family'] and rv==rankone['violations'] and len(rv)==6
    assert not rankone['rank_one_fixed_Taylor_model_pass']
    for block,record in zip(model['PSD_blocks'],rankone['rank_one_PSD_blocks']):
        multiplier=sum(F(q)*values[k] for k,q in block['multiplier_polynomial'])
        assert str(multiplier)==record['multiplier'] and multiplier>=0 and record['PSD_at_rank_one']
        M=exact_matrix(block,rankx);basis=values[:block['size']]
        assert all(M[i][j]==multiplier*basis[i]*basis[j] for i in range(block['size']) for j in range(block['size']))
    index={tuple(m):k-1 for k,m in enumerate(model['monomials']) if m}
    variances=[x[index[r,r]]-x[r]**2 for r in range(9)];assert all(v>0 for v in variances)
    assert not any(n.split('.')[0] in ['numpy','scipy','scs'] for n in sys.modules)
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==initial
    out={'scope':__doc__,'status':'strict_exact_shared_quartic_outer_relaxation_independently_verified',
        'path':model['path'],'source_sha256_start':initial,'source_sha256_end':final,'all_sources_unchanged':True,
        'unadjusted_rational_moments':714,'energy_slack':'0','rational_linear_rows_checked':5795,
        'strict_positive_PSD_blocks_checked':47,'PSD_sizes':model['PSD_sizes'],'PSD_entries_checked':4070,
        'independent_algorithm':'Fraction Schur/LDL; exact comparison to integer Bareiss leading minors',
        'minimum_LDL_pivot_by_block':least_pivots,'nonzero_position_variances':list(map(str,variances)),
        'rank_one_diagnostic_negative_rows':len(rv),'rank_one_localizer_factorizations_checked':47,
        'pure_stdlib_replay':True,'solver_calls':0,'Lean_invocations':0,
        'actual_analytic_inputs_Lean_proved_here':False,'actual_F_or_KKT_counterexample':False,
        'cell_exclusion_proven':False,'new_zero_proportion_proven':False,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['status','rational_linear_rows_checked','strict_positive_PSD_blocks_checked',
        'rank_one_diagnostic_negative_rows','elapsed_milliseconds']}),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
