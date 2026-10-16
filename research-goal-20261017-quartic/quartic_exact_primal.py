"""One unadjusted rational check of the saved quartic lifted primal.

Fraction(str(saved_float)) for all 714 moments, and t=0.  No projection,
precision loop, optimizer, or new sampling.  Check every linear inequality
and, if those pass, every PSD block by exact fraction-free Sylvester/Bareiss.
A pass certifies only this fixed degree-four outer relaxation, not actual F.
"""
from pathlib import Path
from fractions import Fraction as F
from math import lcm
import gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
OUT=HERE/'quartic-exact-primal.json'
sys.set_int_max_str_digits(0)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check_pd(matrix):
    n=len(matrix);den=1
    for row in matrix:
        for z in row:den=lcm(den,z.denominator)
    integer=[[int(z*den) for z in row] for row in matrix]
    digest=hashlib.sha256(json.dumps(integer,separators=(',',':')).encode()).hexdigest()
    minors=[];previous=1
    for k in range(n):
        pivot=integer[k][k];minors.append(pivot)
        if pivot<=0:return {'strictly_positive_definite':False,'failed_leading_minor_index':k+1,
            'integer_matrix_denominator':str(den),'integer_matrix_sha256':digest,'positive_leading_minors':[str(v) for v in minors[:-1]],'failed_leading_minor':str(pivot)}
        for i in range(k+1,n):
            for j in range(i,n):
                z=integer[i][j]*pivot-integer[i][k]*integer[k][j]
                q,r=divmod(z,previous);assert not r
                integer[i][j]=integer[j][i]=q
        previous=pivot
    return {'strictly_positive_definite':True,'integer_matrix_denominator':str(den),'integer_matrix_sha256':digest,
        'positive_leading_minors':[str(v) for v in minors]}


def main():
    assert not OUT.exists();began=time.monotonic()
    paths=[Path(__file__),HERE/'quartic-model.json.gz',HERE/'quartic-build.json',HERE/'quartic-cone.json',HERE/'quartic-rankone.json']
    pins={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths}
    raw=gzip.decompress(paths[1].read_bytes());model=json.loads(raw);build=json.loads(paths[2].read_bytes());cone=json.loads(paths[3].read_bytes())
    assert sha(paths[1])==build['model_compressed_sha256'] and hashlib.sha256(raw).hexdigest()==build['model_uncompressed_sha256']
    assert not cone['any_positive_hint'] and len(cone['raw_primal_hint'])==715
    point=[F(str(v)) for v in cone['raw_primal_hint'][:714]]+[F(0)]
    out={'scope':__doc__,'phase':'checking_unadjusted_rational_primal','path':model['path'],'source_sha256_start':pins,
        'conversion':'Fraction(str(saved_float)) exactly once for all moments; t=0; no projection',
        'rational_714_moments':list(map(str,point[:714])),'energy_slack':'0','linear_rows_checked':0,'strict_PD_blocks_checked':0,
        'actual_F_evaluated':False,'actual_KKT_verified':False,'actual_sublevel_verified':False,
        'solver_calls':0,'Lean_invocations':0,'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
    def save():
        final={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths};assert final==pins
        out.update({'source_sha256_end':final,'all_sources_unchanged':True,'elapsed_milliseconds':int((time.monotonic()-began)*1000)})
        OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    save();families={};violations=[]
    for index,row in enumerate(model['linear_rows']):
        slack=F(row['bound'])-sum(F(q)*point[k] for k,q in row['coefficients']);normalized=slack/F(row['scale']);family=row['meta'][0]
        entry={'row':index,'meta':row['meta'],'slack':str(slack),'normalized_slack':str(normalized)}
        if family not in families or normalized<F(families[family]['normalized_slack']):families[family]=entry
        if slack<0:violations.append(entry)
    out.update({'linear_rows_checked':len(model['linear_rows']),'minimum_by_row_family':families,'negative_linear_rows':len(violations),'violations':violations})
    out['strict_PD_blocks']=[]
    if not violations:
        for block in model['PSD_blocks']:
            n=block['size'];matrix=[[F(0) for _ in range(n)] for _ in range(n)]
            for i,j,form in block['entries']:
                matrix[i][j]=matrix[j][i]=F(form['constant'])+sum(F(q)*point[k] for k,q in form['coefficients'])
            witness=check_pd(matrix);witness.update({'name':block['name'],'size':n});out['strict_PD_blocks'].append(witness)
            out['strict_PD_blocks_checked']+=1;save()
            if not witness['strictly_positive_definite']:break
    passed=not violations and len(out['strict_PD_blocks'])==47 and all(b['strictly_positive_definite'] for b in out['strict_PD_blocks'])
    out['exact_quartic_outer_relaxation_feasible']=passed
    out['status']='strict_exact_shared_quartic_outer_relaxation_feasible' if passed else 'unadjusted_rational_primal_check_failed_stopped'
    out['phase']='completed_once_no_adjustment';save()
    print(json.dumps({k:out[k] for k in ['status','linear_rows_checked','negative_linear_rows','strict_PD_blocks_checked','exact_quartic_outer_relaxation_feasible','elapsed_milliseconds']}),flush=True)
    print(json.dumps({'row_family_minimum_hint':{k:float(F(v['normalized_slack'])) for k,v in families.items()}}),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
