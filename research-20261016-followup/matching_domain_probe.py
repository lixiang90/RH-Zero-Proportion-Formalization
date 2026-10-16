"""Measure the effect of a larger maximal-matching threshold on the old tree.

Exact integer geometry and frozen LB queries only. The experiment does not
establish a Lean cover or an unconditional zeta bound. Old files are read-only.
"""
from pathlib import Path
import argparse, hashlib, json, sys, time

ROOT = Path(__file__).resolve().parents[1]
OLD = ROOT / 'research-20261016-w10-cert'
sys.path.insert(0, str(ROOT / 'research-20261016-w10-unconditional'))
from prune_floor_probe import branches_only
import ordered_generate as ordered
import independent_integer_audit as audit

g = ordered.g
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--sep-grid', type=int, default=31488)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    assert 27852 <= args.sep_grid <= 31488
    start = time.monotonic()
    source = OLD / 'ordered-proof-input.json'
    source_hash = sha(source)
    parameter_hash = sha(g.PAR)
    _, lower = audit.load_analytic_library()
    close_pair_lb = lower(27852, args.sep_grid)
    assert close_pair_lb >= 86600000
    oldsep = g.SEP
    g.SEP = args.sep_grid
    stronger_root = g.root()
    g.SEP = oldsep
    oldroot = g.root()
    assert all(a <= b <= c <= d for a, b, c, d in
               zip(oldroot[0], stronger_root[0], stronger_root[1], oldroot[1]))
    nodes = branches_only(source)
    todo = [('r', stronger_root)]
    counts = {'visited': 0, 'retained_branches': 0, 'skipped_branches': 0,
              'nonempty_old_leaves': 0, 'empty_cells': 0}
    while todo:
        path, state = todo.pop()
        state, _ = ordered.normalize(state)
        counts['visited'] += 1
        lo, hi = state
        if any(l > u for l, u in zip(lo, hi)) or hi[8] < lo[0]:
            counts['empty_cells'] += 1
        elif path in nodes:
            node = nodes[path]
            axis, cut = node['axis'], node['cut']
            if cut <= lo[axis]:
                counts['skipped_branches'] += 1
                todo.append((path+'1', state))
            elif hi[axis] <= cut:
                counts['skipped_branches'] += 1
                todo.append((path+'0', state))
            else:
                counts['retained_branches'] += 1
                todo.extend((path+digit, ordered.rawsplit(state, axis, cut, upper))
                            for digit, upper in [('1', False), ('0', True)])
        else:
            counts['nonempty_old_leaves'] += 1
    result = {'scope': __doc__, 'script_sha256': sha(Path(__file__)),
              'source_sha256': source_hash, 'parameter_sha256': parameter_hash,
              'old_separation': '17/20', 'new_separation_grid': args.sep_grid,
              'new_separation_denominator': g.SC,
              'close_pair_extension_lower_bound': [close_pair_lb, 10**10],
              'old_close_pair_lower_bound': [1, 64],
              'required_pair_payment': [433, 50000],
              'old_branches': len(nodes), 'old_total_leaves': len(nodes)+1,
              'counts': counts,
              'retained_partition_leaves': counts['retained_branches']+1,
              'stronger_root': stronger_root,
              'elapsed_seconds': time.monotonic()-start,
              'global_floor_lean_proven': False, 'higher_kappa_proven': False}
    assert source_hash == sha(source) and parameter_hash == sha(g.PAR)
    args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf8')
    print(json.dumps({k: v for k, v in result.items() if k != 'stronger_root'}), flush=True)


if __name__ == '__main__':
    main()
