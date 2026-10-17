"""Independent stdlib check of the fixed eight-swap relaxation witness.

No producer imports or optimizer. Recompute all 5803 rational rows at
the unadjusted 714 coordinates, energy slack zero, and all 47 PSD blocks
by Fraction LDL. Compare pivot products with producer Bareiss minors.
Default read-only; --write-receipt creates only a previously absent file.
"""
from pathlib import Path
from fractions import Fraction as F
from math import lcm
import argparse,gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
PARENT=ROOT/'research-goal-20261017-quartic'
OUT=HERE/'swap-family-result-replay.json'
sys.set_int_max_str_digits(0)

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def row_checks(rows,x):
    families={};violations=[]
    for index,row in enumerate(rows):
        slack=F(row['bound'])-sum(F(q)*x[k] for k,q in row['coefficients']);normalized=slack/F(row['scale']);family=row['meta'][0]
        item={'row':index,'meta':row['meta'],'slack':str(slack),'normalized_slack':str(normalized)}
        if family not in families or normalized<F(families[family]['normalized_slack']):families[family]=item
        if slack<0:violations.append(item)
    return families,violations
def matrix(block,x):
    n=block['size'];a=[[F(0) for _ in range(n)] for _ in range(n)]
    for i,j,form in block['entries']:a[i][j]=a[j][i]=F(form['constant'])+sum(F(q)*x[k] for k,q in form['coefficients'])
    return a
def verify_ldl(a,w):
    n=len(a);assert n==w['size'] and w['strictly_positive_definite']
    denominator=1
    for row in a:
        for v in row:denominator=lcm(denominator,v.denominator)
    assert str(denominator)==w['integer_matrix_denominator']
    integer=[[int(v*denominator) for v in row] for row in a]
    assert sha_bytes(json.dumps(integer,separators=(',',':')).encode())==w['integer_matrix_sha256']
    schur=[r.copy() for r in a];product=F(1);pivots=[]
    for k in range(n):
        pivot=schur[k][k];assert pivot>0,(w['name'],k,pivot)
        pivots.append(pivot);product*=pivot
        assert product*denominator**(k+1)==F(w['positive_leading_minors'][k])
        for i in range(k+1,n):
            for j in range(i,n):
                v=schur[i][j]-schur[i][k]*schur[j][k]/pivot
                schur[i][j]=schur[j][i]=v
    return min(pivots)
def sha_bytes(raw):return hashlib.sha256(raw).hexdigest()

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--write-receipt',action='store_true');args=parser.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic()
    paths=[Path(__file__),PARENT/'quartic-model.json.gz',PARENT/'quartic-build.json',PARENT/'quartic-replay.json',
        HERE/'swap-family-normalized.json.gz',HERE/'swap-family-normalized-build.json',HERE/'swap-family-cone.json',
        HERE/'swap-family-exact-primal.json',ROOT/'research-goal-20261017-swap-family-audit/independent-replay.json']
    modelraw=gzip.decompress(paths[1].read_bytes());parent=json.loads(modelraw)
    build=json.loads(paths[2].read_bytes());oldstatic=json.loads(paths[3].read_bytes());familyraw=gzip.decompress(paths[4].read_bytes());family=json.loads(familyraw)
    fb=json.loads(paths[5].read_bytes());cone=json.loads(paths[6].read_bytes());proof=json.loads(paths[7].read_bytes());gate=json.loads(paths[8].read_bytes())
    for report in [build,oldstatic,fb,cone,proof,gate]:
        start=report.get('source_sha256_start',report.get('input_sha256_start'));end=report.get('source_sha256_end',report.get('input_sha256_end'))
        assert start==end
        for name,h in start.items():
            p=ROOT/name;assert sha(p)==h,(name,h)
            if p not in paths:paths.append(p)
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    assert sha(paths[1])==build['model_compressed_sha256'] and sha_bytes(modelraw)==build['model_uncompressed_sha256']
    assert sha(paths[4])==fb['packet_compressed_sha256']==gate['packet_sha256'] and sha_bytes(familyraw)==fb['packet_uncompressed_sha256']
    assert oldstatic['status']=='shared_quartic_coefficients_rows_and_localizers_independently_verified' and gate['passed']
    assert family['parent_model_sha256']==sha(paths[1]) and family['monomials']==parent['monomials'] and family['all_eight_conditions_simultaneous']
    assert proof['status']=='strict_exact_shared_quartic_eight_swap_outer_relaxation_feasible'
    assert not cone['any_positive_hint'] and cone['phase']=='completed_single_shared_quartic_eight_swap_SCS'
    assert parent['path']==family['path']==cone['path']==proof['path']=='r001000001000100110011001'
    x=[F(str(float(v))) for v in cone['raw_primal_hint'][:714]]+[F(0)]
    assert x[:714]==list(map(F,proof['rational_714_moments'])) and proof['energy_slack']=='0'
    extra=family['additional_linear_rows'];assert len(extra)==8
    for r,row in enumerate(extra):
        assert row['meta']==['unsoftened_global_adjacent_swap_necessary',r,r+1] and all(k<714 for k,_ in row['coefficients'])
    rows=parent['linear_rows']+extra;assert len(parent['linear_rows'])==5795 and len(rows)==5803
    families,violations=row_checks(rows,x)
    assert families==proof['minimum_by_row_family'] and violations==proof['violations']==[] and proof['linear_rows_checked']==5803
    assert len(proof['strict_PD_blocks'])==len(parent['PSD_blocks'])==47 and parent['PSD_sizes']==[55]+[10]*46
    least=[]
    for block,witness in zip(parent['PSD_blocks'],proof['strict_PD_blocks']):
        assert block['name']==witness['name'];least.append(str(verify_ldl(matrix(block,x),witness)))
    # Also read the new row directly as the moment expectation of Dplus.
    moments=[F(1)]+x[:714];expectations=[]
    for row,item in zip(extra,family['maps']):
        value=sum(F(v)*moments[k] for k,v in item['difference_upper_quartic'])
        slack=F(row['bound'])-sum(F(v)*x[k] for k,v in row['coefficients'])
        assert value==slack>0;expectations.append(str(value))
    assert not any(n.split('.')[0] in ['numpy','scipy','scs'] for n in sys.modules)
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==initial
    out={'scope':__doc__,'status':'strict_exact_eight_swap_quartic_outer_relaxation_independently_verified',
        'passed':True,'path':parent['path'],'source_sha256_start':initial,'source_sha256_end':final,'all_sources_unchanged':True,
        'unadjusted_rational_moments':714,'energy_slack':'0','rational_linear_rows_checked':5803,
        'old_rows_referenced_unchanged':5795,'new_unsoftened_rows':8,'new_swap_upper_difference_expectations':expectations,
        'strict_positive_PSD_blocks_checked':47,'PSD_sizes':parent['PSD_sizes'],'PSD_entries_checked':4070,
        'independent_algorithm':'Fraction Schur/LDL; exact pivot products equal integer Bareiss leading minors',
        'minimum_LDL_pivot_by_block':least,'pure_stdlib_replay':True,'solver_calls':0,'Lean_invocations':0,
        'actual_analytic_inputs_Lean_proved_here':False,'actual_F_or_KKT_counterexample':False,
        'cell_exclusion_proven':False,'new_zero_proportion_proven':False,'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    if args.write_receipt:OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['status','rational_linear_rows_checked','strict_positive_PSD_blocks_checked','elapsed_milliseconds']}),flush=True)
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
