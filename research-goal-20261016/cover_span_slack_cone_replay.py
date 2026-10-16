"""Independent pure-Fraction cone counterexample; no checkpoint dependency.

The abstract counterexample separates nonadjacent span-slack RLT products
from the coordinate-box RLT, McCormick, KKT and position-PSD model. It is
not a window-kernel exclusion and does not establish numerical speed gains.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse, hashlib, json


def cone_counterexample():
    names = ['x', 'y', 'z', 't']
    means = dict(zip(names, [F(1, 2), F(1, 2), F(-1, 2), F(-1, 2)]))
    box = {'x': (F(0), F(1)), 'y': (F(0), F(1)),
           'z': (F(-1), F(0)), 't': (F(-1), F(0))}
    second = {('x', 'x'): F(1, 4), ('x', 'y'): F(1, 4), ('y', 'y'): F(1, 4),
      ('x', 'z'): F(0), ('y', 'z'): F(0), ('x', 't'): F(-1, 2), ('y', 't'): F(-1, 2)}
    def product(a, b):
        return second[(a, b) if (a, b) in second else (b, a)]
    rows = []
    for name in names:
        lower, upper = box[name]
        rows += [({name: F(-1)}, lower), ({name: F(1)}, -upper)]
    rows += [({'x': F(-1), 'y': F(-1)}, F(1)),
             ({'z': F(1), 't': F(1)}, F(1)),
             ({'z': F(-1), 't': F(-1)}, F(-1))]
    old = [];rlt = [];mc = []
    for coeff, constant in rows:
        residual = constant+sum(a*means[name] for name, a in coeff.items())
        assert residual <= 0;old.append(residual)
        for name in ['x', 'y']:
            lifted = constant*means[name]+sum(a*product(name, other) for other, a in coeff.items())
            assert lifted <= 0 and residual-lifted <= 0
            rlt.extend([lifted, residual-lifted])
    for (a, b), h in second.items():
        l, u = box[a];L, U = box[b];x, y = means[a], means[b]
        residuals = [l*y+L*x-l*L-h, u*y+U*x-u*U-h,
                     h-u*y-L*x+u*L, h-l*y-U*x+l*U]
        assert max(residuals) <= 0;mc.extend(residuals)
    # [[1,x,y],[x,Hxx,Hxy],[y,Hxy,Hyy]] = v v^T, v=(1,1/2,1/2).
    v = [F(1), means['x'], means['y']]
    M = [[F(1), means['x'], means['y']],
         [means['x'], product('x', 'x'), product('x', 'y')],
         [means['y'], product('x', 'y'), product('y', 'y')]]
    assert all(M[i][j] == v[i]*v[j] for i in range(3) for j in range(3))
    assert means['z']+means['t']+1 == 0
    assert all(product(name, 'z')+product(name, 't')+means[name] == 0 for name in ['x', 'y'])
    new = product('x', 'z')+product('y', 'z')-means['z']
    assert new == F(1, 2) > 0
    return {'base_rows': len(old), 'coordinate_RLT_rows': len(rlt), 'McCormick_rows': len(mc),
      'position_matrix_exact_rank_one_PSD': True, 'KKT_and_both_products_exact': True,
      'violated_new_row': 'z*(x+y-1)<=0', 'new_residual': str(new),
      'checkpoint_required': False, 'actual_window_exclusion': False}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args();assert not args.output.exists(), 'Use a new receipt.'
    result = {'scope': __doc__, 'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'passed': True, 'exact_counterexample': cone_counterexample(),
      'optimizer_imported': False, 'new_zero_proportion_proven': False}
    review = Path(__file__).with_name('cover-main117500-structure-review.json')
    if review.exists():
        doc = json.loads(review.read_bytes());old = doc['cone_counterexample']
        assert old['new_lifted_residual'] == result['exact_counterexample']['new_residual']
        assert old['old_base_rows_checked'] == result['exact_counterexample']['base_rows']
        assert old['old_coordinate_RLT_rows_checked'] == result['exact_counterexample']['coordinate_RLT_rows']
        assert old['McCormick_rows_checked'] == result['exact_counterexample']['McCormick_rows']
        result['matches_frozen_structure_review'] = True
        result['review_sha256'] = hashlib.sha256(review.read_bytes()).hexdigest()
    args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf8')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
