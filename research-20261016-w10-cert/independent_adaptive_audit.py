"""Compare adaptive and original ordered cells on a fixed exported tree.

Only the independent Nat-cuB implementation is reused; no search generator,
optimizer or codec is imported. This checks compatibility of finite data,
not the analytic floor or any new proportion theorem.
"""
from pathlib import Path
import argparse, hashlib, json, time
import independent_integer_audit as arithmetic


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    if not __debug__:
        raise RuntimeError('Adaptive audit assertions must remain enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('inputs', type=Path, nargs='+')
    parser.add_argument('--require-complete', action='store_true')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()
    parameter = json.loads(arithmetic.PARAMETER.read_bytes())
    root = arithmetic.initial_root(parameter['b_numerators'])
    branches = {}
    leaves = {}
    inputs = []
    for path in args.inputs:
        raw = path.read_bytes()
        data = json.loads(raw)
        assert data['format'] == 'ordered-mcheckGX-1024' and data['normalize_rounds'] == 2
        assert data['root'] == root
        inputs.append({'path': str(path), 'sha256': sha(raw)})
        for table, rows in [(branches, data['branches']), (leaves, data['accepted'])]:
            for row in rows:
                assert row['path'] not in table or table[row['path']] == row
                table[row['path']] = row
    assert not set(branches)&set(leaves)
    counts = {'visited_nodes': 0, 'skipped_normalizations': 0, 'performed_normalizations': 0,
              'numeric_leaves': 0, 'empty_leaves': 0, 'unresolved_subtree_roots': 0}
    first_difference = first_leaf_difference = None
    seen = set()
    pending = [('r', root, root)]
    while pending:
        path, old_raw, adaptive_raw = pending.pop()
        if path not in branches and path not in leaves:
            counts['unresolved_subtree_roots'] += 1
            continue
        counts['visited_nodes'] += 1
        seen.add(path)
        old, _ = arithmetic.normalize_ordered(old_raw)
        skip = adaptive_raw[1][0] <= adaptive_raw[1][8] and adaptive_raw[0][0] <= adaptive_raw[0][8]
        if skip:
            adaptive = adaptive_raw
            counts['skipped_normalizations'] += 1
        else:
            adaptive, _ = arithmetic.normalize_ordered(adaptive_raw)
            counts['performed_normalizations'] += 1
        if old != adaptive and first_difference is None:
            first_difference = {'path': path, 'skip': skip, 'old': old, 'adaptive': adaptive}
        if path in branches:
            row = branches[path]
            for upper, bit in [(False, '1'), (True, '0')]:
                pending.append((path+bit,
                                arithmetic.raw_child(old, row['axis'], row['cut'], upper),
                                arithmetic.raw_child(adaptive, row['axis'], row['cut'], upper)))
        else:
            result = leaves[path]['result']
            counts['empty_leaves' if result.get('empty') else 'numeric_leaves'] += 1
            if 'certificate' in result:
                certificate = result['certificate']
                expected = [certificate['lower_bounds'], certificate['upper_bounds']]
                assert expected == old, ('Raw data differs from original independent replay', path)
                if adaptive != expected and first_leaf_difference is None:
                    first_leaf_difference = {'path': path, 'expected': expected, 'adaptive': adaptive}
            elif result.get('reflection'):
                if not adaptive[1][8] < adaptive[0][0] and first_leaf_difference is None:
                    first_leaf_difference = {'path': path, 'reflection_not_empty': True}
    assert seen == set(branches)|set(leaves), 'Unreachable data in supplied subtrees'
    for row in inputs:
        row['unchanged_after_audit'] = sha(Path(row['path']).read_bytes()) == row['sha256']
    if args.require_complete:
        assert counts['unresolved_subtree_roots'] == 0, 'Incomplete adaptive compatibility audit'
        assert all(row['unchanged_after_audit'] for row in inputs), 'An input changed during final adaptive audit'
    receipt = {'scope': __doc__, 'passed': first_difference is None and first_leaf_difference is None,
               'inputs': inputs, **counts,
               'skip_proportion': counts['skipped_normalizations']/max(counts['visited_nodes'], 1),
               'all_visited_cells_equal': first_difference is None,
               'all_leaf_certificate_bounds_equal': first_leaf_difference is None,
               'complete_finite_partition': counts['unresolved_subtree_roots'] == 0,
               'required_complete': args.require_complete,
               'first_cell_difference': first_difference, 'first_leaf_difference': first_leaf_difference,
               'script_sha256': sha(Path(__file__).read_bytes()),
               'independent_arithmetic_script_sha256': sha(Path(arithmetic.__file__).read_bytes()),
               'seconds': time.monotonic()-started, 'higher_kappa_proven': False}
    args.output.write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf8')
    print(json.dumps({k: receipt[k] for k in ['passed', 'visited_nodes', 'skipped_normalizations',
                     'skip_proportion', 'numeric_leaves', 'empty_leaves', 'unresolved_subtree_roots',
                     'all_visited_cells_equal', 'all_leaf_certificate_bounds_equal', 'seconds']}))
    assert receipt['passed'], 'Adaptive normalization changes recorded cell data; inspect receipt'


if __name__ == '__main__':
    main()
