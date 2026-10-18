"""N fixed native support, one normalized rational RREF; definitions only."""
from fractions import Fraction as F
import math

def finite_list(x,n):
    return isinstance(x,list) and len(x)==n and all(type(v) in (int,float) and math.isfinite(v) for v in x)

def reconstruct(raw,model,alg,cells):
    x=raw.get('x');marg=raw.get('ineqlin',{}).get('marginals')
    if not finite_list(x,model['columns_count']) or not finite_list(marg,len(model['rows'])):
        return {'dual_eligible':False,'dual_reason':'no_finite_native_primal_and_dual',
            'exact_dual':None,'exact_primal':None,'support_or_precision_retries':0}
    nu=[-float(v) for v in marg];positive=[r for r,v in enumerate(nu) if v>0]
    X=[F(0)]+[F.from_float(float(v))*20*alg.Q for v in x[:9]]
    rows=model['rows'];bases=[];have_mass=True
    for term in model['terms']:
        candidates=[r for r in term['component_rows'] if nu[r]>0]
        if candidates:base=max(candidates,key=lambda r:(nu[r],-r))
        else:
            have_mass=False
            base=max(term['component_rows'],key=lambda r:(sum(a*X[j] for j,a in alg.sparse_position(rows[r]))-rows[r]['bound'],-r))
        bases.append(base)
    extras=[r for r in positive if r>=155 and r not in bases]
    geo=[r for r in positive if r<155]
    comps={c['row_id']:c for t in model['terms'] for c in t['components']}
    nonzero=[];redundant=[];unsupported=[]
    columns=[rows[r]['position10'] for r in geo];descriptors=[{'row_id':r,'kind':'geometry','raw_divisor':1} for r in geo]
    for rid in extras:
        termid=rows[rid]['epigraph_index'];base=bases[termid]
        ds=comps[rid]['S']-comps[base]['S'];de=comps[rid]['E']-comps[base]['E']
        if not ds:
            (redundant if not de else unsupported).append(rid)
            continue
        divisor=abs(ds)
        rawcol=[a-b for a,b in zip(rows[rid]['position10'],rows[base]['position10'])]
        assert all(a%divisor==0 for a in rawcol)
        col=[a//divisor for a in rawcol]
        assert sorted(v for v in col if v)==[-1,1] and sum(col)==0
        columns.append(col);nonzero.append(rid)
        descriptors.append({'row_id':rid,'kind':'extra','base_row':base,'delta_S':ds,'raw_divisor':divisor})
    reason=None;dual=None;rank=None
    if any(v<0 for v in nu):reason='negative_native_dual_hint'
    elif not have_mass:reason='missing_term_positive_dual_hint'
    elif unsupported:reason='zero_delta_S_different_E_fixed_support_not_changed'
    elif len(columns)>9:reason='more_than9_normalized_unknowns_no_alternate_support'
    else:
        constant=list(map(F,model['objective_position10']))
        for term,base in zip(model['terms'],bases):
            for j,a in alg.sparse_position(rows[base]):constant[j]+=2*term['weight_numerator']*a
        mat=[[col[j] for col in columns] for j in range(1,10)]
        gamma,rank=alg.exact_rref(mat,[-v for v in constant[1:]],len(columns),[F(0)]*len(columns))
        if gamma is None:reason='fixed_normalized_support_exact_balance_inconsistent'
        else:
            mu=[F(0)]*len(rows)
            for info,value in zip(descriptors,gamma):mu[info['row_id']]=value/info['raw_divisor']
            for term,base in zip(model['terms'],bases):
                mu[base]=2*term['weight_numerator']-sum(mu[r] for r in term['component_rows'] if r!=base)
            checks=alg.sparse_dual_check(model,mu)
            dual={'raw_row_weights':list(map(str,mu)),'checks':checks,'normalized_rank':rank,
                'normalized_weights':list(map(str,gamma)),'normalized_columns':descriptors,
                'base_mass_nonnegative_checked':all(mu[r]>=0 for r in bases),
                'all_group_T_equations_and_full10_position_balance_checked':True,
                'free_normalized_unknowns_predeclared_zero':True}
            if not checks['valid']:reason='raw_nonnegative_base_mass_or_full_raw_balance_failed'
    # These equalities generate one candidate only. A zero base multiplier does
    # NOT imply a tie. Every original inequality is subsequently checked.
    pm=[];pr=[]
    for rid in geo:pm.append(rows[rid]['position10'][1:]);pr.append(rows[rid]['bound'])
    for rid in extras:
        row=rows[rid];base=rows[bases[row['epigraph_index']]]
        pm.append([a-b for a,b in zip(row['position10'][1:],base['position10'][1:])])
        pr.append(row['bound']-base['bound'])
    physical,prank=alg.exact_rref(pm,pr,9,X[1:]);primal=None
    if physical is not None:
        point=alg.epigraph_point(model,[F(0)]+physical)
        checks=alg.sparse_primal_check(model,point,cells)
        primal={'raw_primal':list(map(str,point)),'checks':checks,'candidate_face_rank':prank,
            'tie_equations_are_candidate_generation_only':True,
            'free_coordinates':'original native dyadics scaled by20Q; no repair/search',
            'T_coordinates':'exact max of all original positive-mass components and constant'}
    return {'dual_eligible':reason is None,'dual_reason':reason,'exact_dual':dual,'exact_primal':primal,
        'primal_reason':None if physical is not None else 'fixed_candidate_face_inconsistent',
        'support_plan':{'positive_rows':positive,'base_rows':bases,'positive_geometry_rows':geo,
            'positive_extra_rows':extras,'nonzero_delta_S_extra_rows':nonzero,
            'zero_delta_S_identical_E_merged_rows':redundant,'zero_delta_S_different_E_rows':unsupported,
            'negative_native_dual_rows':[r for r,v in enumerate(nu) if v<0]},
        'normalized_unknown_count':len(columns),'native_optimal_status':raw.get('status'),
        'native_status_is_not_a_certificate':True,'support_or_precision_retries':0}
