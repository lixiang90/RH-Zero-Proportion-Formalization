"""Standalone stdlib replay of two strict quadratic-energy moment systems.

Rebuild old DBM/slab/facet/KKT integer rows, tight scalar boxes, all moment
RLT/McCormick rows, energy packets, selected outward integer rows, positive
weights and strict residual-box contradictions. Replay complete ancestors
from the frozen pressure root. Point energy/gradient intervals are rerun
using the SAME exact interval kernel helper as the provider; this part is
not an implementation-independent transcendental audit. No optimizer,
NumPy, SciPy, networkx, Lean proof or global-cover claim is involved.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip
import hashlib
import json
import sys
import time

import cover_exact_scalar_replay as adapter
adapter.install()
import cover_lifted_graph_verify as graph
import cover_correlated_curvature_verify as curvature
import cover_cross_moment_exact_rows as exact
import cover_cross_moment_energy_replay as energy_audit
import window_interval_kernel as ik

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SC, DS, D, Q = exact.SC, exact.DS, exact.D, exact.Q
sha = lambda raw: hashlib.sha256(raw).hexdigest()


def rebuild_old_rows(state, old_meta, scalar_affine_data, params, checker):
    """Independent old row/box soundness using GraphReplay's rational bounds."""
    graph.a.closure_valid(state)
    terms = [tuple(map(int, r)) for r in params['a_upper'] if r[2]]
    bs = list(map(int, params['b_numerators']))
    assert params['denominator'] == D and len(terms) == len(scalar_affine_data) == 41
    slabs = []
    rectangles = {}
    for (i, j, aw), raw in zip(terms, scalar_affine_data):
        axis = graph.a.INDEX[i, j]
        l, u = state[0][axis], state[1][axis]
        slabs.append(checker.slab(l, u, raw))
        rectangles[axis] = checker.rectangles(l, u)
    rows = []
    counts = {}
    for meta in old_meta:
        ag, au = [0]*9, [0]*41
        kind = meta[0]
        counts[kind] = counts.get(kind, 0)+1
        if kind == 'DBM':
            _, axis, sign = meta
            assert isinstance(axis, int) and 0 <= axis < 45 and sign in [-1, 1]
            i, j = graph.a.PAIRS[axis]
            ag = [sign*Q if i <= r < j else 0 for r in range(9)]
            B = sign*2*DS*D*state[1 if sign == 1 else 0][axis]
        elif kind == 'KKT':
            _, r, sign = meta
            assert isinstance(r, int) and 0 <= r < 9 and sign in [-1, 1]
            assert sign == -1 or state[0][r] > 123*SC//128
            au = [sign*2*SC*DS*aw if i <= r < j else 0 for i, j, aw in terms]
            B = -sign*2*SC*DS*bs[r]
        else:
            assert kind in ['slab', 'facet']
            t, sign = meta[1:3]
            assert isinstance(t, int) and 0 <= t < 41 and sign in [-1, 1]
            i, j, aw = terms[t]
            axis = graph.a.INDEX[i, j]
            au[t] = sign*Q
            if kind == 'slab':
                assert len(meta) == 3
                P, m0, m1, err, _ = slabs[t]
                ag = [-sign*2*SC*m1*D if i <= r < j else 0 for r in range(9)]
                B = D*(sign*(2*SC*m0-m1*P)+2*SC*err)
            else:
                assert len(meta) == 5
                S, C = map(exact.integer, meta[3:])
                rect = rectangles[axis]
                if sign == 1:
                    bound = max(SC*U-S*(a if S >= 0 else b) for a, b, L, U in rect)
                else:
                    bound = min(SC*L-S*(b if S >= 0 else a) for a, b, L, U in rect)
                assert C == bound
                ag = [-sign*2*SC*S*D if i <= r < j else 0 for r in range(9)]
                B = sign*2*D*C
        rows.append((ag, au, B))
    ubounds = []
    for i, j, aw in terms:
        rect = rectangles[graph.a.INDEX[i, j]]
        L = F(min(r[2] for r in rect), DS)
        U = F(max(r[3] for r in rect), DS)
        assert -7 <= L <= U <= 7
        ubounds.append((L, U))
    return rows, ubounds, {'old_rows': len(rows), 'row_kinds': counts,
                            'scalar_slabs_checked': len(slabs), 'tight_scalar_boxes_checked': len(ubounds)}


def point_intervals(packet, params):
    """Rerun the shared rational kernel helper, not a second implementation."""
    point = list(map(F, packet['centre']))
    f0 = ik.I(sum(F(b, D)*x for b, x in zip(params['b_numerators'], point)))
    grad = [ik.I(F(b, D)) for b in params['b_numerators']]
    terms = [tuple(t) for t in params['a_upper'] if t[2]]
    for i, j, aw in terms:
        w0, w1 = ik.w_jet(sum(point[i:j]), 1)
        f0 += F(aw, D)*w0
        for r in range(i, j):
            grad[r] += F(aw, D)*w1
    assert [f0.l, f0.u] == list(map(F, packet['F_interval']))
    assert [[v.l, v.u] for v in grad] == [list(map(F, row)) for row in packet['gradient_interval']]
    return {'point_energy_and_nine_gradient_intervals_match': True,
            'scalar_point_calls': len(terms), 'shared_provider_kernel_implementation': True}


def independent_integer_row(row, bounds, N):
    coeff = {i: round(F(a)*N) for i, a in row['coeff'].items()}
    error = sum(abs(F(a)-F(coeff[i], N))*max(abs(F(bounds[i][0])), abs(F(bounds[i][1])))
                for i, a in row['coeff'].items())
    rhs = N*(F(row['bound'])+error)
    rhs = -((-rhs.numerator)//rhs.denominator)
    return {i: a for i, a in coeff.items() if a}, rhs, error


def dependency_hashes():
    result = {}
    for module in list(sys.modules.values()):
        path = getattr(module, '__file__', None)
        if not path:
            continue
        path = Path(path).resolve()
        try:
            relative = path.relative_to(ROOT).as_posix()
        except ValueError:
            continue
        if path.is_file():
            result[relative] = sha(path.read_bytes())
    result[Path(__file__).resolve().relative_to(ROOT).as_posix()] = sha(Path(__file__).read_bytes())
    return result


def main():
    started = time.monotonic()
    input_path = HERE/'cover-cross-moment-integer-two.json'
    raw = input_path.read_bytes()
    document = json.loads(raw)
    for name, digest in document['receipt']['inputs'].items():
        assert sha((HERE/name).read_bytes()) == digest, name
    assert sha(Path(exact.__file__).read_bytes()) == document['receipt']['exact_rows_sha256']
    assert sha((HERE/'cover_cross_moment_integer_extract.py').read_bytes()) == document['receipt']['script_sha256']
    frozen_raw = (HERE/'cover-curvature-parent64.input.json.gz').read_bytes()
    frozen = json.loads(gzip.decompress(frozen_raw))
    for name, digest in frozen['input_sha256'].items():
        assert sha((ROOT/name).read_bytes()) == digest, name
    params_raw = (ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes()
    params = json.loads(params_raw)
    table_raw = (HERE/'cover_newjet.json').read_bytes()
    checker = graph.GraphReplay(json.loads(table_raw))
    second_checker = curvature.CurvatureReplay(checker.scalar)
    selected = {row['path'] for row in document['rows']}
    assert selected == {'r001000001000001101011101', 'r001000001000001110011100'}
    target = F(frozen['target'])*graph.energy.g.DEN
    assert target.denominator == 1
    before, ancestor_counts = graph.reconstruct(frozen, selected, params, checker, target.numerator)
    print(json.dumps({'stage': 'complete_two_path_ancestor_replay', 'counts': ancestor_counts,
                      'seconds': time.monotonic()-started}), flush=True)
    results = []
    for case in document['rows']:
        state = case['cell']
        assert state == before[case['path']]
        old_rows, ubounds, old_counts = rebuild_old_rows(state, case['old_meta'], case['scalar_affine_data'], params, checker)
        assert old_rows == [(list(map(int, ag)), list(map(int, au)), int(B)) for ag, au, B in case['old_integer_rows']]
        assert ubounds == [tuple(map(F, pair)) for pair in case['u_bounds']]
        energy_checks = []
        for k, packet in enumerate(case['energy_packets']):
            point_check = point_intervals(packet, params)
            algebra_check = energy_audit.verify_packet(state, packet, params, second_checker)
            energy_checks.append({**point_check, **algebra_check})
            # The smaller audit only skipped point evaluation; this replay
            # has now rerun it, explicitly using the common helper.
            energy_checks[-1]['point_kernel_intervals_recomputed'] = True
            print(json.dumps({'stage': 'point_and_energy_packet_replay', 'path': case['path'], 'packet': k,
                              'seconds': time.monotonic()-started}), flush=True)
        model = exact.inputs(state, old_rows, case['old_meta'], ubounds, case['energy_packets'])
        assert model['bounds'] == [tuple(map(F, b)) for b in case['box_bounds']]
        assert model['integer_bounds'] is not None and model['box_denominator'] == SC*DS
        N = exact.integer(case['integerization_denominator'])
        assert N == 10**30
        coeff, Btotal, weight_sum = {}, 0, 0
        indices, rebuilt_ints, weights = set(), [], []
        for saved in case['selected_integer_rows']:
            index = saved['row_index']
            assert isinstance(index, int) and 0 <= index < len(model['rows']) and index not in indices
            indices.add(index)
            row = model['rows'][index]
            assert row['meta'] == saved['meta']
            a, B, payment = independent_integer_row(row, model['bounds'], N)
            assert sorted(a.items()) == [(i, exact.integer(v)) for i, v in saved['integer_coefficients']]
            assert B == exact.integer(saved['integer_bound']) and payment == F(saved['rounding_payment'])
            mu = exact.integer(saved['weight'])
            assert 0 < mu <= 2**case['dual_weight_power']
            weight_sum += mu
            Btotal += mu*B
            for i, value in a.items():
                coeff[i] = coeff.get(i, 0)+mu*value
            rebuilt_ints.append({'coeff': a, 'bound': B, 'denominator': N})
            weights.append((len(rebuilt_ints)-1, str(mu)))
        coeff = {i: a for i, a in coeff.items() if a}
        minimum = sum(a*model['bounds'][i][0 if a >= 0 else 1] for i, a in coeff.items())
        margin = minimum-Btotal
        aggregate = case['aggregate']
        assert margin > 0 and aggregate['strict_exclusion'] and case['strict_integer_system_contradiction']
        assert sorted(coeff.items()) == [(i, exact.integer(a)) for i, a in aggregate['coefficient']]
        assert Btotal == exact.integer(aggregate['bound']) and minimum == F(aggregate['box_minimum'])
        assert margin == F(aggregate['strict_margin']) and N == exact.integer(aggregate['denominator'])
        crosscheck = exact.verify_aggregate(rebuilt_ints, weights, model['bounds'])
        assert crosscheck['coefficient'] == coeff and crosscheck['strict_margin'] == margin
        results.append({'path': case['path'], 'all_checks_passed': True, **old_counts,
                        'energy_packets': energy_checks, 'exact_moment_rows': len(model['rows']),
                        'selected_outward_integer_rows': len(indices), 'positive_integer_weight_sum': str(weight_sum),
                        'box_denominator': str(model['box_denominator']), 'integerization_denominator': str(N),
                        'strict_margin': str(margin), 'normalized_margin': str(margin/(N*weight_sum)),
                        'actual_Lean_exclusion_proven': False})
        print(json.dumps({'stage': 'strict_integer_system_replayed', 'path': case['path'],
                          'selected_rows': len(indices), 'normalized_margin': float(margin/(N*weight_sum)),
                          'seconds': time.monotonic()-started}), flush=True)
    assert not any(name in sys.modules for name in ['numpy', 'scipy', 'networkx'])
    output = HERE/'cover-cross-moment-independent-replay.json'
    receipt = {'scope': __doc__, 'script_sha256': sha(Path(__file__).read_bytes()),
               'input_sha256': sha(raw), 'parent64_input_sha256': sha(frozen_raw),
               'parameters_sha256': sha(params_raw), 'table_sha256': sha(table_raw),
               'dependency_sources_sha256': dependency_hashes(), 'no_site_packages': sys.flags.no_site,
               'no_numerical_optimization_packages_imported': True, 'all_checks_passed': True,
               'ancestor_counts': ancestor_counts, 'independent_derivative_grid_cells': len(checker.checked_grid),
               'local_strict_integer_contradictions': len(results), 'cases': results,
               'point_intervals_use_shared_provider_kernel_helper': True,
               'implementation_independent_point_transcendental_audit': False,
               'actual_Lean_exclusions': 0, 'complete_global_cover': False,
               'new_zero_proportion_proven': False, 'seconds': time.monotonic()-started}
    output.write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'all_checks_passed': True, 'strict_local_integer_systems': len(results),
                      'seconds': receipt['seconds'], 'receipt_sha256': sha(output.read_bytes())}), flush=True)


if __name__ == '__main__':
    main()
