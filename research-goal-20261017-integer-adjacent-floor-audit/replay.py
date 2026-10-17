"""Independent exact read-only audit of a fixed integer-gap lower bound.

No kernel value, solver, Lean process, lattice enumeration or new point is
computed.  Default is read-only; --write-receipt creates an absent receipt.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, hashlib, json, re, time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def pin(p):
    return {'path': p.relative_to(ROOT).as_posix(), 'bytes': p.stat().st_size,
            'sha256': sha(p)}

def table_from_lean(text):
    assert 'def qi30 (l u : ℤ) : QI := ((l:ℚ)/10^30,(u:ℚ)/10^30)' in text
    start = text.index('def wValues : List (List QI) :=')
    start = text.index('[', start)
    depth = 0
    for end in range(start, len(text)):
        if text[end] == '[':
            depth += 1
        elif text[end] == ']':
            depth -= 1
            if depth == 0:
                break
    assert depth == 0
    body = text[start:end+1]
    rows = re.findall(r'\[([^\[\]]*)\]', body)
    out = []
    pattern = r'qi30\s+\((-?\d+)\)\s+\((-?\d+)\)'
    for row in rows:
        pairs = re.findall(pattern, row)
        assert len(pairs) == 24
        assert not re.sub(pattern, '', row).replace(',', '').strip()
        out.append([(F(int(l), 10**30), F(int(u), 10**30)) for l, u in pairs])
    assert len(out) == 33
    return out

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write-receipt', action='store_true')
    args = ap.parse_args()
    started = time.monotonic()
    names = [
        'research-goal-20261016/window_normalized_interval.json',
        'research-20261016-followup/window_reweight_rational.json',
        'StructuralGoal20261016/WindowJetTableData.lean',
        'StructuralW10Followup20261016/NewLedger.lean',
        'StructuralGoal20261016/WindowNormalizedJets.lean',
        'StructuralGoal20261016/WindowRationalInterval.lean',
        'StructuralGoal20261016/WindowFixedTablesAll.lean',
        'StructuralGoal20261016/WindowKernel.lean',
        'StructuralGoal20261016/WindowGramExpansion.lean',
        'StructuralGoal20261016/WindowGapEnergy.lean',
    ]
    paths = [ROOT / n for n in names]
    initial = {n: sha(ROOT / n) for n in names}
    doc = json.loads(paths[0].read_text(encoding='utf-8'))
    params = json.loads(paths[1].read_text(encoding='utf-8'))
    assert doc['parameter_sha256'] == initial[names[1]]
    assert int(doc['scale']) == 10**30
    expected = doc['integer_w_Taylor_coefficients']
    table = table_from_lean(paths[2].read_text(encoding='utf-8'))
    for n in range(33):
        assert len(expected[str(n)]) == 24
        for r in range(24):
            assert table[n][r] == tuple(F(x) for x in expected[str(n)][r]), (n, r)

    assert int(params['denominator']) == 10**10
    ledger = paths[3].read_text(encoding='utf-8')
    atext = ledger[ledger.index('def aN'):ledger.index('def bN')]
    btext = ledger[ledger.index('def bN'):ledger.index('def a (')]
    a = {(int(i), int(j)): int(v) for i, j, v in
         re.findall(r'\| (\d+), (\d+) => (\d+)', atext)}
    b = {int(i): int(v) for i, v in re.findall(r'\| (\d+) => (\d+)', btext)}
    assert len(a) == 45 and len(b) == 9
    assert a == {(int(i), int(j)): int(v) for i, j, v in params['a_upper']}
    assert [b[i] for i in range(9)] == params['b_numerators']
    assert all(v >= 0 for v in a.values()) and all(v > 0 for v in b.values())
    assert sum(b.values()) == 44222684

    rows = []
    total = F(0)
    for r in range(9):
        br, ar = F(b[r], 10**10), F(a[r, r+1], 10**10)
        candidates = [(n, br*n + ar*table[n][0][0]) for n in range(1, 33)]
        tail = 33*br
        minimum = min([v for _, v in candidates] + [tail])
        minimizers = [n for n, v in candidates if v == minimum]
        assert minimizers == [2] and minimum < tail
        assert all(minimum <= v for _, v in candidates) and minimum <= tail
        rows.append({'gap': r, 'b': str(br), 'a_adjacent': str(ar),
                     'minimizing_integer_among_1_to_32': minimizers,
                     'minimum': str(minimum), 'tail_from_33': str(tail),
                     'candidates': [{'n': n, 'lower': str(v)} for n, v in candidates]})
        total += minimum
    claimed = F(49010784449364406850369272140464640617,
                5000000000000000000000000000000000000000)
    assert total == claimed
    thresholds = [F(11, 1250), F(221, 25000)]
    assert all(total > c for c in thresholds)

    # Read existing authoritative module receipts; do not run/rebuild anything.
    verification = json.loads((ROOT/'research-goal-20261016/lean_verification.json').read_text())
    proof_bindings = []
    modules = [f'StructuralGoal20261016.WindowFixedKernelCenter{n:02}' for n in range(1, 33)]
    modules += ['StructuralGoal20261016.WindowFixedTablesAll']
    for module in modules:
        source = ROOT/(module.replace('.', '/')+'.lean')
        current = sha(source)
        matching = [r for r in verification['modules'] if r.get('module') == module and
                    r.get('source_sha256') == current and r.get('passed') and
                    r.get('exit_code') == 0 and r.get('source_unchanged')]
        assert matching, module
        rec = matching[-1]
        log = ROOT/'research-goal-20261016'/rec['log']
        assert sha(log) == rec['log_sha256']
        proof_bindings.append({'module': module, 'source': pin(source),
                               'log': pin(log), 'existing_ordinary_passed': True,
                               'olean_sha256_from_existing_receipt': rec['olean_sha256']})

    assert all(sha(ROOT/n) == h for n, h in initial.items())
    result = {
        'scope': __doc__, 'status': 'PASS_fixed_integer_adjacent_arithmetic_and_table_identity',
        'auditor': pin(Path(__file__)), 'inputs': [pin(p) for p in paths],
        'exact_table_identity': {'centres': 33, 'orders_per_centre': 24,
                                 'pairs': 792, 'endpoints': 1584,
                                 'relation': 'exactly_equal_not_merely_outward'},
        'existing_proof_bindings': proof_bindings, 'rows': rows,
        'L': str(total), 'L_decimal_diagnostic_only': float(total),
        'strict_thresholds': [{'c': str(c), 'margin': str(total-c)} for c in thresholds],
        'mathematical_scope': [
            'For any positive integer 9-gap vector, drop all nonadjacent nonnegative weighted squares.',
            'For n=1..32 use actual w(n)>=W(n,0).lower; wc at order0 is definitionally w.',
            'For n>=33 use b*n+a*w(n)>=33*b, since b,a,w are nonnegative.',
            'Sum the 9 independent lower bounds; no upper gap bound or lattice search is needed.',
            'This is an exact arithmetic implication from already proved tables, not a new Lean theorem.',
            'Consequently common-shift averaged integer energy >=L>c; the minimizer upper comparison alone supplies no new floor.',
            'A useful rounding route must instead bound the pointwise transfer loss from below.'
        ],
        'new_kernel_values': 0, 'solver_calls': 0, 'Lean_invocations': 0,
        'audit_history': 'First invocation passed the arithmetic assertions but failed while unnecessarily decoding an existing binary/non-UTF8 log. No receipt was written. Only that unused decoding step was removed; fixed inputs and arithmetic were unchanged. This is the second audit invocation, not a new candidate.',
        'new_Lean_theorem_proven': False, 'rounding_transfer_lower_bound_proven': False,
        'complete_global_floor_proven': False, 'new_zero_proportion_proven': False,
        'seconds': time.monotonic()-started,
    }
    if args.write_receipt:
        with (HERE/'independent-replay.json').open('x', encoding='utf-8', newline='\n') as out:
            json.dump(result, out, ensure_ascii=False, indent=2)
            out.write('\n')
    print(json.dumps({k: result[k] for k in ['status', 'L', 'L_decimal_diagnostic_only',
                      'exact_table_identity', 'seconds']}))

if __name__ == '__main__':
    main()
