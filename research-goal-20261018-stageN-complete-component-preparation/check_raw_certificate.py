"""Independent of native discovery/RREF: full raw sparse certificate arithmetic."""
from fractions import Fraction as F

def verify(model,exact):
    rows=model['rows'];target=F(model['target']);out={'Lower':False,'Below':False}
    dual=exact.get('exact_dual');primal=exact.get('exact_primal')
    if dual:
        mu=list(map(F,dual['raw_row_weights']));assert len(mu)==len(rows)
        balance=list(map(F,model['objective_position10']+model['objective_epigraph']))
        bound=F(0)
        for w,row in zip(mu,rows):
            if not w:continue
            for j,a in enumerate(row['position10']):
                if a:balance[j]+=w*a
            t=row['epigraph_index']
            if t is not None:balance[10+t]+=w*row['epigraph_coefficient']
            bound-=w*row['bound']
        valid=all(w>=0 for w in mu) and all(v==0 for v in balance)
        check=dual['checks'];assert valid==check['valid']
        assert list(map(str,balance))==check['full_balance'] and str(bound)==check['raw_lower_bound']
        out.update({'dual_valid':valid,'raw_lower_bound':str(bound),'Lower':valid and bound>=target})
    if primal:
        x=list(map(F,primal['raw_primal']));assert len(x)==model['columns_count'];X=[F(0)]+x[:9];bad=[]
        for row in rows:
            lhs=sum(a*X[j] for j,a in enumerate(row['position10']) if a)
            if row['epigraph_index'] is not None:lhs+=row['epigraph_coefficient']*x[9+row['epigraph_index']]
            if lhs>row['bound']:bad.append(row['row_id'])
        value=sum(a*X[j] for j,a in enumerate(model['objective_position10']) if a)
        value+=sum(a*x[9+j] for j,a in enumerate(model['objective_epigraph']) if a)
        check=primal['checks'];assert check['valid']==(not bad) and check['violated_row_ids']==bad
        assert str(value)==check['raw_objective']
        out.update({'primal_valid':not bad,'raw_objective':str(value),'Below':not bad and value<target})
    assert not(out['Lower'] and out['Below']),'contradictory_raw_certificates'
    return out
