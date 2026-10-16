"""One zero-solver rank-one diagnostic at the saved first-moment hint.

Convert the nine saved decimal floats exactly once using Fraction(str(x)).
Set all shared moments to their actual monomials, slack=0, and check every
row and rank-one localizer exactly.  No search, Taylor sampling, or solver.
Even a pass concerns only this fixed Taylor outer relaxation, not actual
F or the actual stationary equations, nor any global lower bound.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip,hashlib,json,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
OUT=HERE/'quartic-rankone.json'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    assert not OUT.exists();began=time.monotonic()
    paths=[Path(__file__),HERE/'quartic-model.json.gz',HERE/'quartic-build.json',HERE/'quartic-cone.json']
    pins={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths}
    raw=gzip.decompress(paths[1].read_bytes());model=json.loads(raw);build=json.loads(paths[2].read_bytes());cone=json.loads(paths[3].read_bytes())
    assert sha(paths[1])==build['model_compressed_sha256'] and hashlib.sha256(raw).hexdigest()==build['model_uncompressed_sha256']
    assert cone['phase']=='completed_single_shared_quartic_SCS' and not cone['any_positive_hint']
    y=[F(str(v)) for v in cone['raw_primal_hint'][:9]];values=[]
    for monomial in model['monomials']:
        z=F(1)
        for r in monomial:z*=y[r]
        values.append(z)
    point=values[1:]+[F(0)];assert len(point)==715
    families={};violations=[];worst=None
    for index,row in enumerate(model['linear_rows']):
        slack=F(row['bound'])-sum(F(q)*point[k] for k,q in row['coefficients']);normalized=slack/F(row['scale'])
        family=row['meta'][0]
        entry={'row':index,'meta':row['meta'],'slack':str(slack),'normalized_slack':str(normalized)}
        if family not in families or normalized<F(families[family]['normalized_slack']):families[family]=entry
        if worst is None or normalized<F(worst['normalized_slack']):worst=entry
        if slack<0:violations.append(entry)
    blocks=[]
    for block in model['PSD_blocks']:
        multiplier=sum(F(q)*values[k] for k,q in block['multiplier_polynomial'])
        # The basis contains 1, so g(y)*v(y)v(y)^T PSD iff g(y)>=0.
        # Check all coefficient entries against this factorization as well.
        basis=values[:block['size']]
        for i,j,form in block['entries']:
            value=F(form['constant'])+sum(F(q)*point[k] for k,q in form['coefficients'])
            assert value==multiplier*basis[i]*basis[j]
        blocks.append({'name':block['name'],'size':block['size'],'multiplier':str(multiplier),'PSD_at_rank_one':multiplier>=0})
    passed=not violations and all(b['PSD_at_rank_one'] for b in blocks)
    final={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths};assert final==pins
    out={'scope':__doc__,'status':'rank_one_fixed_Taylor_outer_relaxation_verified' if passed else 'saved_means_rank_one_diagnostic_failed_no_search',
        'path':model['path'],'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,
        'conversion':'Fraction(str(saved_float)) exactly once; no precision adjustment',
        'normalized_gap_point':list(map(str,y)),'energy_slack':'0','shared_monomials_evaluated':len(values),
        'linear_rows_checked':len(model['linear_rows']),'negative_linear_rows':len(violations),
        'violations':violations,'worst_normalized_linear_slack':worst,'minimum_by_row_family':families,
        'rank_one_PSD_blocks':blocks,'rank_one_PSD_entries_checked':sum(len(b['entries']) for b in model['PSD_blocks']),
        'rank_one_fixed_Taylor_model_pass':passed,'actual_F_evaluated':False,'actual_KKT_verified':False,
        'actual_sublevel_verified':False,'new_actual_scalar_positions':0,'solver_calls':0,'Lean_invocations':0,
        'cell_exclusion_proven':False,'new_zero_proportion_proven':False,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['status','linear_rows_checked','negative_linear_rows','rank_one_PSD_entries_checked','rank_one_fixed_Taylor_model_pass','elapsed_milliseconds']}),flush=True)
    print(json.dumps({'worst_normalized_linear_slack_hint':float(F(worst['normalized_slack'])),
        'negative_PSD_multipliers':[b['name'] for b in blocks if not b['PSD_at_rank_one']]}),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
