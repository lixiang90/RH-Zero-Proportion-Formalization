"""One frozen residual: at most two64-cut DBM/pressure-slack RLT rounds.

Uses the same original moment model, same feasible-midpoint energy0 and
saved primal from the frozen six-case negative experiment. No PSD cuts,
new samples, threshold changes, or main-search mutations are performed.
Each HiGHS call has a45-second limit. A timeout is inconclusive. Floating
slack is not a proof; positive slack is followed by outward integerization.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, hashlib, json, time
import numpy as np
from scipy.sparse import csr_matrix, vstack, hstack
import cover_cross_moment_probe as base
import cover_cross_moment_exact_rows as exact
import cover_span_slack_separator as separator

HERE = Path(__file__).parent
PATH = 'r001000001000100110011001'
sha = lambda b: hashlib.sha256(b).hexdigest()


def integer_certificate(state, integer, meta, scalar_data, graph, packet,
                        cuts, dual):
    ubounds = []
    for i, j, aw in base.g.TERMS:
        z = base.g.LOOK[i, j]
        facets, n = graph.facets(state[0][z], state[1][z])
        U = min(F(C, base.SC*base.old.DS) for sign, S, C in facets if sign == 1 and S == 0)
        L = max(F(C, base.SC*base.old.DS) for sign, S, C in facets if sign == -1 and S == 0)
        ubounds.append((L, U))
    model = exact.inputs(state, integer, meta, ubounds, [packet])
    assert len(model['rows']) == dual['base_rows']+1
    model['rows'][-1:-1] = cuts
    selected = dual['nonzero_row_dual_weights']
    indices = [i for i, w in selected]
    coefficients = [w/float(model['rows'][i]['scale']) for i, w in selected]
    mx = max(coefficients)
    integers = [exact.integerize(model['rows'][i], model['bounds'], 10**30) for i in indices]
    attempts = [];chosen = None
    for power in [32, 48, 64]:
        weights = [round(w/mx*2**power) for w in coefficients]
        weighted = [(i, mu) for i, mu in enumerate(weights) if mu]
        checked = exact.verify_aggregate(integers, weighted, model['bounds'])
        attempts.append({'power': power, 'strict': checked['strict_exclusion'],
                         'margin': str(checked['strict_margin'])})
        if checked['strict_exclusion']:
            chosen = (power, weights, checked);break
    if chosen is None:
        return None, attempts
    power, weights, checked = chosen;saved = [];kinds = {}
    for index, mu, row in zip(indices, weights, integers):
        if not mu:
            continue
        kind = row['meta'][0];kinds[kind] = kinds.get(kind, 0)+1
        saved.append({'row_index': index, 'meta': row['meta'], 'weight': str(mu),
          'integer_coefficients': [[k, str(a)] for k, a in sorted(row['coeff'].items())],
          'integer_bound': str(row['bound']), 'rounding_payment': str(row['rounding_payment'])})
    aggregate = {k: ([[i, str(v)] for i, v in sorted(value.items())] if k == 'coefficient'
      else str(value) if isinstance(value, (F, int)) and not isinstance(value, bool)
      else value) for k, value in checked.items()}
    return {'scalar_affine_data': [[P, str(m0), str(m1), str(err), kind] for P, m0, m1, err, kind in scalar_data],
      'u_bounds': [[str(l), str(u)] for l, u in ubounds],
      'integerization_denominator': str(10**30), 'dual_weight_power': power,
      'selected_integer_rows': saved, 'selected_row_kind_counts': kinds,
      'box_bounds': [[str(l), str(u)] for l, u in model['bounds']], 'aggregate': aggregate,
      'attempts': attempts, 'strict_integer_system_contradiction': True,
      'independent_analytic_input_replay_passed': False,
      'actual_Lean_exclusion_proven': False}, attempts


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args();assert not args.output.exists(), 'Use a new output.'
    start = time.monotonic()
    seed_path = HERE/'cover-cross-moment-remaining-six.json';seed_raw = seed_path.read_bytes()
    seed_doc = json.loads(seed_raw);seed = seed_doc['rows'][0]
    assert seed['path'] == PATH and seed['dual_hint']['minimum_energy_slack_hint'] == 0
    state = seed['cell'];packet, = seed['energy_packets']
    sources = [Path(base.__file__), Path(base.old.__file__), Path(exact.__file__),
               Path(separator.__file__), HERE/'cover_newjet.json']
    guards = {p.name: sha(p.read_bytes()) for p in sources}
    for name, digest in seed_doc['receipt']['source_guards'].items():
        assert sha((HERE/name).read_bytes()) == digest
    table = HERE/'cover_newjet.json'
    taylor = base.old.context.curvature.first.TaylorOracle(table)
    graph = base.old.GraphOracle(table)
    rr, bb, integer, meta, data, obj, stats = base.old.build(state, taylor, graph, True)
    candidates = separator.factors(state, base.g.BS, base.g.D)
    identity_checks = []
    # A fixed rational rank-one algebra check, not an actual-kernel sample.
    gap_test = [F(l+u, 2*base.SC)+F((k%3)-1, 7)*F(u-l, 2*base.SC)
                for k, (l, u) in enumerate(zip(state[0][:9], state[1][:9]))]
    scalar_test = [F((k%7)-3, 11) for k in range(41)]
    for factor in candidates:
        identity_checks.append(separator.exact_identity_check(state, integer[-1], factor, gap_test, scalar_test))
    current = seed['base_result']['final_primal']
    selected_pairs = [];cuts = [];cut_records = [];history = [];dual = {}
    certificate = None;attempts = []
    output = {'receipt': {'scope': __doc__, 'script_sha256': sha(Path(__file__).read_bytes()),
      'source_guards': guards, 'seed_input_sha256': sha(seed_raw), 'seed_path': PATH,
      'target': '11/1250', 'maximum_cut_rounds': 2, 'maximum_cuts_per_round': 64,
      'HiGHS_time_limit_seconds': 45, 'old_atom_count': len(integer),
      'candidate_factors': candidates, 'exact_product_factorization_checks': len(identity_checks),
      'no_new_kernel_samples': True, 'position_PSD_cut_rounds': 0,
      'strict_certificates': 0, 'independent_input_replay_passed': False,
      'actual_Lean_exclusions': 0, 'complete_global_cover': False,
      'new_zero_proportion_proven': False}, 'path': PATH, 'cell': state,
      'energy_packet': packet, 'history': history, 'cuts': cut_records}
    def save(stage):
        output['stage'] = stage;output['receipt']['seconds'] = time.monotonic()-start
        assert all(sha(p.read_bytes()) == guards[p.name] for p in sources)
        args.output.write_text(json.dumps(output, separators=(',', ':'))+'\n', encoding='utf8')
    save('initialized')
    energy_row = np.zeros(base.V)
    for k, v in packet['row']:
        energy_row[k] = float(F(v))
    energy_bound = float(F(packet['bound']))
    energy_scale = max(1., max(abs(energy_row)), abs(energy_bound))
    original = base.linprog
    def augmented(c, **kw):
        nonlocal current
        A0 = kw['A_ub'];B0 = kw['b_ub'];base_rows = A0.shape[0]
        assert base_rows == seed['dual_hint']['base_rows']
        seed_error = float(np.max(A0@np.array(current)-B0))
        assert seed_error < 1e-7, seed_error
        assert energy_row@np.array(current)-energy_bound < 1e-7
        output['seed_rebuilt_base_max_violation_hint'] = seed_error
        last = None
        for iteration in range(1, 3):
            selection_start = time.monotonic()
            chosen, selection = separator.select(state, integer, meta, current, candidates,
                                                 excluded=selected_pairs, limit=64)
            if not chosen:
                output['termination'] = 'No violated candidate selected.'
                save('no_new_violation');break
            for item in chosen:
                selected_pairs.append((item['old_atom_index'], item['factor_index']))
                cuts.append(item['exact_row'])
                cut_records.append({'round': iteration, 'old_atom_index': item['old_atom_index'],
                  'factor_index': item['factor_index'], 'score_hint': item['score_hint'],
                  'residual_hint': item['residual_hint'],
                  'exact_row': separator.serialize_row(item['exact_row'])})
            h = {'iteration': iteration, 'selection': selection,
              'selection_seconds': time.monotonic()-selection_start,
              'total_new_cuts': len(cuts)}
            history.append(h);save('selected_before_LP')
            dense = np.zeros((len(cuts), base.V));rhs = []
            for n, row in enumerate(cuts):
                scale = float(row['scale'])
                for i, value in row['coeff'].items():
                    dense[n, i] = float(value)/scale
                rhs.append(float(row['bound'])/scale)
            A = vstack([A0, csr_matrix(dense), csr_matrix(energy_row[None, :]/energy_scale)], format='csr')
            B = np.r_[B0, rhs, energy_bound/energy_scale]
            column = np.r_[np.zeros(base_rows+len(cuts)), -1/energy_scale][:, None]
            lpstart = time.monotonic()
            last = original(np.r_[np.zeros(base.V), 1.],
              A_ub=hstack([A, csr_matrix(column)], format='csr'), b_ub=B,
              bounds=kw['bounds']+[(0, None)], method=kw['method'],
              options={'time_limit': 45.0})
            h.update({'LP_status': int(last.status), 'LP_success': bool(last.success),
              'LP_message': str(last.message), 'LP_seconds': time.monotonic()-lpstart})
            if not last.success:
                h['outcome'] = 'inconclusive-timeout-or-other-failure' if last.status != 2 else 'floating-infeasibility-hint-only'
                save('LP_not_successful');break
            h['minimum_energy_slack_hint'] = float(last.fun)
            h['minimum_softened_row_slack_hint'] = float(min(B-A@last.x[:-1]-column[:, 0]*last.x[-1]))
            current = last.x[:-1].tolist()
            h['primal'] = current;last.x = last.x[:-1]
            if last.fun > 1e-9:
                dual.update({'base_rows': base_rows, 'new_cuts': len(cuts),
                  'minimum_energy_slack_hint': float(last.fun),
                  'nonzero_row_dual_weights': [[k, float(-v)] for k, v in enumerate(last.ineqlin.marginals) if -v > 1e-14]})
                h['outcome'] = 'positive-slack-hint-awaiting-exact-check'
                save('positive_hint');break
            h['outcome'] = 'zero-slack-feasible-floating-primal'
            save('completed_round')
            print(json.dumps({'path': PATH, 'round': iteration, 'selected': len(chosen),
              'slack_hint': float(last.fun), 'LP_seconds': h['LP_seconds'],
              'seconds': time.monotonic()-start}), flush=True)
        if last is None:
            from types import SimpleNamespace
            last = SimpleNamespace(status=0, success=True, x=np.asarray(current))
        return last
    base.linprog = augmented
    try:
        result = base.solve(state, taylor, graph, 0)
    finally:
        base.linprog = original
    assert not result['integer_PSD_cut_vectors']
    if dual:
        certificate, attempts = integer_certificate(state, integer, meta, data, graph, packet, cuts, dual)
    output['integer_certificate'] = certificate;output['integer_attempts'] = attempts
    output['dual_hint'] = dual;output['base_result'] = result
    output['receipt']['strict_certificates'] = int(certificate is not None)
    save('finished')
    print(json.dumps({'path': PATH, 'rounds': len(history), 'strict_integer': certificate is not None,
      'last_status': history[-1].get('LP_status'), 'last_slack_hint': history[-1].get('minimum_energy_slack_hint'),
      'seconds': time.monotonic()-start, 'output_sha256': sha(args.output.read_bytes())}), flush=True)


if __name__ == '__main__':
    main()
