"""Optional future exact transfer API, definitions only, not called by P.

No claim that data loaders, Lean consumers or source-size acceptance exist.
These formulas preserve the given certificate; they do not search for a dual.
"""
from fractions import Fraction as F

def M_unpooled_to_pooled(original_model, pooled_model, original_mu, alg):
    """Same row order; only T coordinates are identified, never weights changed."""
    assert original_model['fixed_cells'] == pooled_model['fixed_cells'] == [0, 604]
    assert original_model['chart'] == pooled_model['chart'] == 'id/rev'
    assert original_model['target'] == pooled_model['target']
    assert len(original_model['rows']) == len(pooled_model['rows']) == len(original_mu)
    mapping = pooled_model['original_term_to_shared_group']
    for old, new in zip(original_model['rows'], pooled_model['rows']):
        assert old['row_id'] == new['row_id'] and old['position10'] == new['position10']
        assert old['bound'] == new['bound'] and old['epigraph_coefficient'] == new['epigraph_coefficient']
        assert new['epigraph_index'] == (None if old['epigraph_index'] is None else mapping[old['epigraph_index']])
    mu = list(map(F, original_mu)); checked = alg.sparse_dual_check(pooled_model, mu)
    assert checked['valid'] and F(checked['raw_minus_target']) >= 0
    return {'raw_row_weights': list(map(str, mu)), 'checks': checked,
            'given_M_weights_unchanged_only_epigraph_coordinates_identified': True}

def J_affine_to_components(pooled_model, original_geo_mu_by_id, alg):
    """Given J geometry dual plus original FS convex masses, no LP or new FS.

Caller must supply the ORIGINAL J raw geometry weights in this model's raw
objective scale, and independently establish its original Cstar/J identity.
Loading those exact weights from the compact J certificate remains pending.
"""
    mu = [F(0)] * len(pooled_model['rows'])
    for rid, weight in original_geo_mu_by_id.items():
        assert type(rid) is int and 0 <= rid < 155
        mu[rid] = F(weight)
    for term in pooled_model['original_terms68']:
        masses = term['original_masses']; assert len(masses) == 3 and sum(masses) == 1024 and min(masses) >= 0
        for component in term['components']:
            mass = masses[0] if component['kind'] == 'constant' else masses[1 + component['original_slot']]
            mu[component['row_id']] = F(2 * term['weight_numerator'] * mass, 1024)
    checked = alg.sparse_dual_check(pooled_model, mu)
    assert checked['valid'] and F(checked['raw_minus_target']) >= 0
    return {'raw_row_weights': list(map(str, mu)), 'checks': checked,
            'given_J_geometry_and_original_FS_masses_no_new_anchor_or_optimization': True}
