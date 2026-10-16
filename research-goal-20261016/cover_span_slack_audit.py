"""Package then independently audit only the128 frozen affine-slack rows.

Export uses the unchanged old discovery builder, with no LP. Replay runs
under Python-S, reconstructs every active old atom with GraphReplay and
checks each exact product by a separate signed coordinate-RLT expansion.
Factor positivity comes from its actual DBM bound or energy sublevel,
never from the independent gap box. No strict exclusion is claimed.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, hashlib, json, sys, time

HERE = Path(__file__).parent
ROOT = HERE.parent
sha = lambda b: hashlib.sha256(b).hexdigest()
PARAMS = ROOT/'research-20261016-followup/window_reweight_rational.json'


def export(output):
    import cover_cross_moment_probe as base
    source = HERE/'cover-span-slack-first-case.json';raw = source.read_bytes();doc = json.loads(raw)
    assert len(doc['cuts']) == 128 and doc['receipt']['strict_certificates'] == 0
    state = doc['cell'];table = HERE/'cover_newjet.json'
    taylor = base.old.context.curvature.first.TaylorOracle(table);graph = base.old.GraphOracle(table)
    rr, bb, integer, meta, data, obj, stats = base.old.build(state, taylor, graph, True)
    selected = sorted({r['old_atom_index'] for r in doc['cuts']})
    used_slabs = sorted({meta[k][1] for k in selected if meta[k][0] == 'slab'})
    stored = {'scope': 'Finite old-atom supplies for independently auditing128 new product rows; no LP.',
      'source_sha256': sha(Path(__file__).read_bytes()), 'discovery_sha256': sha(raw),
      'parameters_sha256': sha(PARAMS.read_bytes()), 'derivative_table_sha256': sha(table.read_bytes()),
      'path': doc['path'], 'cell': state,
      'old_atoms': [{'index': k, 'meta': meta[k],
        'integer_row': [list(map(str, integer[k][0])), list(map(str, integer[k][1])), str(integer[k][2])]}
        for k in selected],
      'slabs': [[t, [data[t][0], str(data[t][1]), str(data[t][2]), str(data[t][3]), data[t][4]]]
                for t in used_slabs],
      'actual_Lean_new_factor_consumer_proven': False, 'strict_certificates': 0,
      'complete_global_cover': False, 'new_zero_proportion_proven': False}
    output.write_text(json.dumps(stored, separators=(',', ':'))+'\n', encoding='utf8')
    return {'packet_sha256': sha(output.read_bytes()), 'old_atoms': len(selected), 'slabs': len(used_slabs)}


def check_factor(factor, state, params):
    SC = 32768
    spans = [(i, i+1) for i in range(9)]+[(i, j) for i in range(9) for j in range(i+2, 10)]
    lo, hi = state;mid = [F(l+u, 2*SC) for l, u in zip(lo[:9], hi[:9])]
    rad = [F(u-l, 2*SC) for l, u in zip(lo[:9], hi[:9])]
    d = int(factor['denominator']);assert d > 0
    A = F(factor['A_numerator'])/d;b = [F(0)]*9
    for s, n in factor['b_numerators']:
        assert isinstance(s, int) and 0 <= s < 9 and b[s] == 0
        b[s] = F(n)/d
    physical = [v/r for v, r in zip(b, rad)]
    constant = A-sum(v*m for v, m in zip(physical, mid))
    kind = factor['kind']
    if kind == 'DBM-span-slack':
        axis = factor['span_axis'];assert 9 <= axis < 45
        i, j = spans[axis];assert factor['pair'] == [i, j]
        sign = factor['side'];assert sign in [-1, 1]
        assert hi[axis]-lo[axis] == d
        assert physical == [F(2*SC*sign, d) if i <= s < j else F(0) for s in range(9)]
        assert constant == -F(2*sign*(lo[axis] if sign == 1 else hi[axis]), d)
        deficit = lo[axis]-sum(lo[i:j]) if sign == 1 else sum(hi[i:j])-hi[axis]
        assert deficit == factor['correlation_deficit_units'] > 0
        return A, b, mid, rad, 'nonnegative-by-DBM-span-bound'
    assert kind == 'pressure-sublevel-slack'
    c = F(factor['target']);assert c == F(11, 1250)
    D = int(factor['ledger_denominator']);assert D == 10**10
    bs = params['b_numerators'];assert factor['pressure_numerators'] == bs and min(bs) > 0
    sep = factor['sep_units'];assert sep == 31488 and min(lo[:9]) >= sep
    payment_denominator = c-sum(F(v*sep, D*SC) for v in bs)
    assert payment_denominator > 0 and d == payment_denominator*SC*D
    assert physical == [-2*F(v, D)/payment_denominator for v in bs]
    assert constant == 2*c/payment_denominator
    return A, b, mid, rad, 'nonnegative-on-energy-sublevel-by-positive-kernel-squares'


def replay(packet_path, output):
    import cover_cross_moment_factor_replay as independent
    started = time.monotonic();packet_raw = packet_path.read_bytes();packet = json.loads(packet_raw)
    source = HERE/'cover-span-slack-first-case.json';source_raw = source.read_bytes();doc = json.loads(source_raw)
    ipm_path = HERE/'cover-span-slack-first-case-ipm.json';ipm_raw = ipm_path.read_bytes();ipm = json.loads(ipm_raw)
    assert sha(source_raw) == packet['discovery_sha256'] == ipm['frozen_default_run_sha256']
    assert packet['cell'] == doc['cell'] and packet['path'] == doc['path'] == ipm['path']
    params_raw = PARAMS.read_bytes();table_raw = (HERE/'cover_newjet.json').read_bytes()
    assert sha(params_raw) == packet['parameters_sha256']
    assert sha(table_raw) == packet['derivative_table_sha256']
    params = json.loads(params_raw);checker = independent.support.graph.GraphReplay(json.loads(table_raw))
    slabs = {t: r for t, r in packet['slabs']};atoms = {}
    for saved in packet['old_atoms']:
        row = independent.old_row(saved['meta'], doc['cell'], slabs, params, checker)
        ag, au, B = saved['integer_row'];integer = list(map(int, ag+au));D = 2*32768*10**15*10**10
        assert row['coeff'] == {k: F(a, D) for k, a in enumerate(integer) if a}
        assert row['bound'] == F(int(B), D)
        assert saved['index'] not in atoms;atoms[saved['index']] = (saved['meta'], row)
    factors = []
    for f in doc['receipt']['candidate_factors']:
        factors.append(check_factor(f, doc['cell'], params))
    counts = {};cut_ids = set()
    for saved in doc['cuts']:
        n = saved['old_atom_index'];fi = saved['factor_index'];assert (n, fi) not in cut_ids
        cut_ids.add((n, fi));meta, old = atoms[n];A, b, mid, rad, proof = factors[fi]
        # (A+b.y)*old = (A-sum b)*old + sum b_s*(1+y_s)*old.
        # This is only an algebra identity; signed weights are not used as
        # a positivity proof. check_factor proved the actual factor>=0.
        expanded = {'coeff': {}, 'bound': F(0)}
        independent.add(expanded, old, A-sum(b))
        for s, weight in enumerate(b):
            if weight:
                independent.add(expanded, independent.rlt(old, mid, rad, s, 1), weight)
        stored = saved['exact_row'];got = {i: F(v) for i, v in stored['coeff']}
        assert got == expanded['coeff'] and F(stored['bound']) == expanded['bound']
        assert F(stored['scale']) == max([F(1), abs(expanded['bound'])]+list(map(abs, got.values())))
        assert stored['meta'] == ['affine-slack-RLT', n, meta, doc['receipt']['candidate_factors'][fi]]
        counts[proof] = counts.get(proof, 0)+1
    assert len(cut_ids) == 128
    assert doc['history'][0]['LP_status'] == 0 and doc['history'][0]['minimum_energy_slack_hint'] == 0
    assert doc['history'][1]['LP_status'] == 1 and doc['integer_certificate'] is None
    assert ipm['LP']['status'] == 0 and ipm['LP']['energy_slack_hint'] == 0
    assert ipm['strict_integer_certificate'] is None
    assert 'scipy' not in sys.modules and 'numpy' not in sys.modules
    result = {'scope': __doc__, 'source_sha256': sha(Path(__file__).read_bytes()),
      'packet_sha256': sha(packet_raw), 'default_run_sha256': sha(source_raw),
      'IPM_run_sha256': sha(ipm_raw), 'passed_exact_new_factor_and_old_atom_algebra': True,
      'old_atoms_reconstructed_from_canonical_metadata': len(atoms), 'active_scalar_slabs': len(slabs),
      'new_factors_checked': len(factors), 'products_checked': len(cut_ids), 'product_factor_kinds': counts,
      'optimizer_imported': False, 'numpy_imported': False,
      'actual_derivative_graph_finite_inputs_checked_by_GraphReplay': True,
      'ancestry_replay_reused_from_frozen_remaining_manifest': 'research-goal-20261016/cover-cross-moment-remaining-files.json',
      'LP_claim': 'Default second call timed out; same128-cut IPM has only an approximate zero-slack primal, max row error7.14e-8. No exact feasible primal or exclusion.',
      'strict_certificates': 0, 'complete_global_cover': False, 'new_zero_proportion_proven': False,
      'seconds': time.monotonic()-started}
    output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf8')
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--export', action='store_true')
    ap.add_argument('--packet', type=Path, default=HERE/'cover-span-slack-old-atoms.json')
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args();assert not args.output.exists(), 'Use a new output.'
    result = export(args.output) if args.export else replay(args.packet, args.output)
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
