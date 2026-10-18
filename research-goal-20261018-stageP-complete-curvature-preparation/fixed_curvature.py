"""P thin generalization of frozen O's row selection; no work at import.

CellA arithmetic and the two payment algorithms are imported, unchanged, from
O only by the future gated driver. No new anchor, interval or dual is chosen.
"""
from fractions import Fraction as F

Q = 32768
KAPPA = Q * 1024 * 10**10

def original_rows(model, windows, source):
    """Variable raw-row count, same original 68 FS components and guards."""
    assert len(windows) == 2 and len(model['original_terms68']) == 68
    assert model['group_count'] == 42 and model['full_balance_coordinates'] == 52
    intervals = {}
    rows = []
    for term in model['original_terms68']:
        wi = term['window']; ti = term['original_term']; window = windows[wi]
        original = window['terms'][ti]
        assert original['term_id'] == ti and window['cell_id'] == model['fixed_cells'][wi]
        assert original['FS'] == term['original_FS']
        i, j = term['original_span']; a = term['weight_numerator']
        assert list(source['TS'][ti][:3]) == [i, j, a] and a > 0
        edge = tuple(term['physical_span']); L, U = term['original_bounds']; L0 = term['original_L0']
        reverse = model['chart'].split('/')[wi] == 'rev'; offset = wi
        expected_edge = (offset + 8 - j, offset + 8 - i) if reverse else (offset + i, offset + j)
        assert edge == expected_edge
        assert original['original_term_bounds'] == [L, U] and original['original_L0'] == L0
        lo, hi = max(F(L, Q), F(17 * (edge[1] - edge[0]), 20)), F(U, Q)
        if edge in intervals:
            lo = max(lo, intervals[edge][0]); hi = min(hi, intervals[edge][1])
        assert lo <= hi
        intervals[edge] = (lo, hi)
        for component in term['components']:
            rid = component['row_id']; raw = model['rows'][rid]
            assert raw['row_id'] == rid and raw['epigraph_index'] == term['shared_group']
            row = {'row_id': rid, 'kind': 'constant' if component['kind'] == 'constant' else 'anchor',
                   'physical_span': list(edge), 'source_window': wi, 'source_term': ti}
            if row['kind'] == 'anchor':
                slot = component['original_slot']; p = component['anchor']
                mass = [original['mass_first'], original['mass_second']][slot]
                assert mass > 0 and original['FS'][2 + slot] == p
                rawpt = source['PTraw'][p]
                vl = max(0, p - ((rawpt >> 96) & ((1 << 20) - 1))); vu = p + (rawpt >> 116)
                assert vu > 0 and vl <= L <= p <= U <= vu and L0 <= L
                assert component['original_mass'] == mass and component['original_valid_interval'] == [vl, vu]
                row.update({'cell_id': window['cell_id'], 'source_slot': slot,
                    'source_original_positive_mass': mass, 'q_integer': p, 'q_physical': str(F(p, Q)),
                    'original_L0': L0, 'original_guard': [vl, L, p, U, vu],
                    'original_state_sha256': window['state_sha256'], 'original_witness': window['witness']})
            rows.append(row)
    assert len(intervals) == 42 and [r['row_id'] for r in rows] == list(range(155, len(model['rows'])))
    return rows, intervals

def attempt(record, model, windows, source, params, frozen_O, provider, network,
            cache, cache_refs, before_cell, append_cell, check_limit):
    """At most one O payment attempt, only for the original exact Below/dual."""
    exact = record['normalized_exact_reconstruction']; dual = exact.get('exact_dual')
    if not dual or not dual['checks']['valid']:
        return None, 'exact_Below_has_no_valid_fixed_raw_dual'
    assert record['separate_raw_verification']['Below'] and record['separate_raw_verification']['dual_valid']
    mu = list(map(F, dual['raw_row_weights']))
    assert len(mu) == len(model['rows']) and all(v >= 0 for v in mu)
    cost = F(dual['checks']['raw_lower_bound']); target = F(model['target'])
    assert cost < target
    components, intervals = original_rows(model, windows, source)
    selected = []
    for row in components:
        row['raw_dual_weight'] = str(mu[row['row_id']])
        if row['kind'] != 'anchor' or not mu[row['row_id']]:
            continue
        check_limit()
        edge = tuple(row['physical_span']); lo, hi = intervals[edge]; p = row['q_integer']
        hlo, hhi = min(F(p), Q * lo), max(F(p), Q * hi)
        cover = frozen_O.cover_original_chain(params, hlo, hhi)
        item = {**row, 'joint_direct_span_interval': list(map(str, [lo, hi])),
                'required_hull_in_Q_units': list(map(str, [hlo, hhi]))}
        if cover is None:
            item.update({'coverage': 'outside_existing_REG_chain', 'm': '0', 'c_raw': '0', 'original_cells': []})
        else:
            entries = []
            for cell in cover:
                key = (cell['L'], cell['U'])
                if key not in cache:
                    check_limit()
                    before_cell(cell)
                    value = provider.evaluate_original_cell(params, *key)
                    cache_refs[key] = append_cell(value)
                    cache[key] = value
                entries.append(cache[key])
            m = min(F(c['m_quantitative']) for c in entries)
            assert m >= 0
            c = mu[row['row_id']] * KAPPA * m / 2
            item.update({'coverage': 'complete_original_REG_chain', 'original_cells': cover,
                         'm': str(m), 'c_raw': str(c),
                         'cell_proof_refs': [cache_refs[(c['L'], c['U'])] for c in cover]})
        selected.append(item)
    check_limit()
    variance, variance_proof = network.variance_clamp(selected, intervals)
    laplace, laplace_proof = network.laplace_payment(selected)
    payment = max(variance, laplace)
    packet = {'schema': 'P-one-fixed-rawdual-original-REG-curvature-v1',
        'G_index': record['G_index'], 'pair': model['fixed_cells'], 'chart': model['chart'],
        'raw_target': str(target), 'frozen_raw_dual_cost': str(cost), 'raw_dual_deficit': str(target - cost),
        'all_original_component_rows': components, 'weighted_anchor_rows': selected,
        'physical_span_intervals': [{'edge': list(e), 'interval': list(map(str, v))} for e, v in sorted(intervals.items())],
        'variance_clamp_payment': str(variance), 'variance_proof': variance_proof,
        'laplace_payment': str(laplace), 'laplace_proof': laplace_proof,
        'chosen_uniform_payment': str(payment), 'uniform_raw_lower_bound': str(cost + payment),
        'minus_target': str(cost + payment - target), 'conditional_pair_floor_closes': cost + payment >= target,
        'exact_Laplace_calls_this_case': 1, 'source_REG_cells_only': True,
        'same_original_rawdual_without_reweighting': True,
        'new_anchors_subdivision_precision_support_solver_or_Lean_runs': 0}
    return packet, None if packet['conditional_pair_floor_closes'] else 'fixed_curvature_payment_insufficient'

def selector(record, closure, curvature=None):
    """Data contract only; no claim that a Lean reconstructor exists."""
    exact = record.get('normalized_exact_reconstruction', {})
    dual = exact.get('exact_dual') or {}
    cells = sorted({(c['chain'], c['ordinal'])
                    for row in (curvature or {}).get('weighted_anchor_rows', [])
                    for c in row['original_cells']})
    return {'G_index': record['G_index'], 'closure': closure,
            'group_base_row_IDs': exact.get('support_plan', {}).get('base_rows', []),
            'normalized_unknown_row_IDs': [d['row_id'] for d in dual.get('normalized_columns', [])],
            'positive_anchor_row_IDs': [r['row_id'] for r in (curvature or {}).get('weighted_anchor_rows', [])],
            'original_REG_selectors': [list(c) for c in cells],
            'raw_mu_m_and_pstar_values_not_in_selector': True,
            'deterministic_reconstructor_and_generic_Lean_consumer_not_implemented': True}
