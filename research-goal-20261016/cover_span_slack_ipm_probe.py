"""One45-second highs-ipm replay of exactly the frozen128-cut system.

No separation, new cuts, new cases, new samples or new energy anchors.
The original default-HiGHS second call timed out. This separate diagnostic
changes only the LP algorithm and never treats timeout as a certificate.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, hashlib, json, time
import numpy as np
from scipy.sparse import csr_matrix, vstack, hstack
import cover_cross_moment_probe as base
import cover_span_slack_probe as discovery

HERE = Path(__file__).parent
sha = lambda b: hashlib.sha256(b).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args();assert not args.output.exists(), 'Use a new output.'
    start = time.monotonic()
    input_path = HERE/'cover-span-slack-first-case.json';raw = input_path.read_bytes();doc = json.loads(raw)
    assert doc['path'] == discovery.PATH and len(doc['cuts']) == 128
    assert doc['history'][1]['LP_status'] == 1 and doc['history'][1]['total_new_cuts'] == 128
    assert doc['receipt']['strict_certificates'] == 0
    state = doc['cell'];packet = doc['energy_packet'];cuts = []
    for saved in doc['cuts']:
        r = saved['exact_row']
        row = {'coeff': {i: F(v) for i, v in r['coeff']}, 'bound': F(r['bound']),
               'scale': F(r['scale']), 'meta': r['meta']}
        assert row['scale'] == max([F(1), abs(row['bound'])]+list(map(abs, row['coeff'].values())))
        cuts.append(row)
    guards = doc['receipt']['source_guards']
    assert all(sha((HERE/name).read_bytes()) == digest for name, digest in guards.items())
    table = HERE/'cover_newjet.json'
    taylor = base.old.context.curvature.first.TaylorOracle(table);graph = base.old.GraphOracle(table)
    result = {'scope': __doc__, 'script_sha256': sha(Path(__file__).read_bytes()),
      'frozen_default_run_sha256': sha(raw), 'source_guards': guards,
      'path': doc['path'], 'target': '11/1250', 'new_cuts_added': 0,
      'fixed_cuts': 128, 'energy_anchors': 1, 'HiGHS_time_limit_seconds': 45,
      'strict_integer_certificate': None, 'independent_input_replay_passed': False,
      'actual_Lean_exclusions': 0, 'complete_global_cover': False, 'new_zero_proportion_proven': False}
    def save(stage):
        result['stage'] = stage;result['seconds'] = time.monotonic()-start
        args.output.write_text(json.dumps(result, separators=(',', ':'))+'\n', encoding='utf8')
    save('before_build')
    original = base.linprog;dual = {}
    def fixed(c, **kw):
        nr = kw['A_ub'].shape[0];assert nr == 43304
        dense = np.zeros((129, base.V));rhs = [];scales = []
        for n, row in enumerate(cuts):
            scale = float(row['scale']);scales.append(scale)
            for i, v in row['coeff'].items():
                dense[n, i] = float(v)/scale
            rhs.append(float(row['bound'])/scale)
        erow = np.zeros(base.V)
        for i, v in packet['row']:
            erow[i] = float(F(v))
        B = float(F(packet['bound']));scale = max(1., max(abs(erow)), abs(B))
        dense[-1] = erow/scale;rhs.append(B/scale)
        A = vstack([kw['A_ub'], csr_matrix(dense)], format='csr');b = np.r_[kw['b_ub'], rhs]
        column = np.r_[np.zeros(nr+128), -1/scale][:, None]
        bounds = kw['bounds']+[(0, None)]
        save('before_LP');lpstart = time.monotonic()
        lp = original(np.r_[np.zeros(base.V), 1.],
          A_ub=hstack([A, csr_matrix(column)], format='csr'), b_ub=b,
          bounds=bounds, method='highs-ipm', options={'time_limit': 45.0})
        result['LP'] = {'status': int(lp.status), 'success': bool(lp.success), 'message': str(lp.message),
          'seconds': time.monotonic()-lpstart, 'iterations': getattr(lp, 'nit', None),
          'crossover_iterations': getattr(lp, 'crossover_nit', None),
          'has_returned_primal': lp.x is not None}
        if lp.x is not None:
            X = lp.x[:-1];slack = float(lp.x[-1])
            row_error = float(np.max(A@X+column[:, 0]*slack-b))
            box_error = max([0.]+[float(l-x) for x, (l, u) in zip(lp.x, bounds) if l is not None]
                            +[float(x-u) for x, (l, u) in zip(lp.x, bounds) if u is not None])
            result['LP'].update({'energy_slack_hint': slack, 'maximum_row_violation_hint': row_error,
              'maximum_box_violation_hint': box_error, 'primal_with_slack': lp.x.tolist()})
            if lp.success and lp.fun > 1e-9:
                dual.update({'base_rows': nr, 'new_cuts': 128, 'minimum_energy_slack_hint': float(lp.fun),
                  'nonzero_row_dual_weights': [[i, float(-v)] for i, v in enumerate(lp.ineqlin.marginals) if -v > 1e-14]})
            lp.x = X
        result['LP']['timeout_is_inconclusive'] = lp.status == 1
        save('after_LP');return lp
    base.linprog = fixed
    try:
        base_result = base.solve(state, taylor, graph, 0)
    finally:
        base.linprog = original
    result['base_result'] = base_result
    if dual:
        rr, bb, integer, meta, data, obj, stats = base.old.build(state, taylor, graph, True)
        cert, attempts = discovery.integer_certificate(state, integer, meta, data, graph, packet, cuts, dual)
        result['strict_integer_certificate'] = cert;result['integer_attempts'] = attempts;result['dual_hint'] = dual
    assert all(sha((HERE/name).read_bytes()) == digest for name, digest in guards.items())
    save('finished')
    print(json.dumps({'path': result['path'], 'LP': {k: v for k, v in result['LP'].items() if k != 'primal_with_slack'},
      'strict_integer': result['strict_integer_certificate'] is not None,
      'seconds': result['seconds'], 'output_sha256': sha(args.output.read_bytes())}), flush=True)


if __name__ == '__main__':
    main()
