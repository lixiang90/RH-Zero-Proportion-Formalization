"""Pure-stdlib exact algebra audit of the two-cell moment probe.

Execute only its row-construction AST using rational vector operations and
synthetic dense old rows. No producer module, NumPy, optimizer, or Lean is
imported. Factorized substitutions check the full RLT/McCormick index
patterns and all recorded integer PSD-cut vectors. This audits algebra,
not floating LP feasibility or any new exclusion.
"""
from pathlib import Path
from fractions import Fraction as F
from types import SimpleNamespace
import ast
import gzip
import hashlib
import json
import time

HERE = Path(__file__).resolve().parent
SC = 32768
DS = 10**15
V = 464
PAIRS = [(s, r) for s in range(9) for r in range(s, 9)]
HI = {p: 50+k for k, p in enumerate(PAIRS)}
ALL = [(i, i+1) for i in range(9)]+[(i, j) for i in range(9) for j in range(i+2, 10)]
LOOK = {p: k for k, p in enumerate(ALL)}
hindex = lambda s, r: HI[min(s, r), max(s, r)]
qindex = lambda s, t: 95+41*s+t
sha = lambda raw: hashlib.sha256(raw).hexdigest()


class Vec(list):
    def __getitem__(self, i):
        result = super().__getitem__(i)
        return Vec(result) if isinstance(i, slice) else result
    def __setitem__(self, i, value):
        return super().__setitem__(i, map(F, value) if isinstance(i, slice) else F(value))
    def copy(self): return Vec(self)
    def __add__(self, other): return Vec(a+b for a, b in zip(self, other))
    def __sub__(self, other): return Vec(a-b for a, b in zip(self, other))
    def __mul__(self, scalar):
        return Vec(a*b for a, b in zip(self, scalar)) if isinstance(scalar, Vec) else Vec(a*F(scalar) for a in self)
    __rmul__ = __mul__
    def __truediv__(self, scalar):
        return Vec(a/b for a, b in zip(self, scalar)) if isinstance(scalar, Vec) else Vec(a/F(scalar) for a in self)
    def __matmul__(self, other): return sum((a*b for a, b in zip(self, other) if a and b), F(0))


def row_constructor(source, terms, table, state):
    tree = ast.parse(source)
    fn = next(node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == 'solve')
    end = next(k for k, node in enumerate(fn.body) if isinstance(node, ast.Assign)
               and any(isinstance(t, ast.Name) and t.id == 'history' for t in node.targets))
    fn.body = fn.body[:end]
    fn.body.insert(0, ast.parse('audit_raw=[]').body[0])
    add = next(node for node in fn.body if isinstance(node, ast.FunctionDef) and node.name == 'add')
    add.body.insert(0, ast.parse('audit_raw.append((row.copy(),B,kind))').body[0])
    fn.body.append(ast.parse('return audit_raw,center,radius,bounds,algebra_error').body[0])
    tree = ast.fix_missing_locations(ast.Module(body=[fn], type_ignores=[]))
    dense = []
    for k in range(3):
        row = Vec(F(((j+2)*(k+1)) % 13-6, 7) for j in range(59))
        dense.append(row)
    old = SimpleNamespace(DS=DS, build=lambda *args: (dense, [F(-2, 3), F(5, 7), F(-1, 11)],
                          None, [['audit']]*3, None, None, None))
    np = SimpleNamespace(zeros=lambda n: Vec(F(0) for _ in range(n)),
                         array=lambda xs, **kw: Vec(map(F, xs)), max=max,
                         abs=lambda xs: Vec(map(abs, xs)),
                         linspace=lambda a, b, n: Vec(F(str(a))+(F(str(b))-F(str(a)))*k/(n-1) for k in range(n)))
    def facets(l, u):
        width = SC//64
        first = l//width
        last = (max(l+1, u)+width-1)//width
        L = min(table['ranges'][k][0] for k in range(first, last))
        U = max(table['ranges'][k][1] for k in range(first, last))
        return [(1, 0, F(SC*U)), (-1, 0, F(SC*L))], last-first
    scope = {'old': old, 'np': np, 'g': SimpleNamespace(TERMS=terms, LOOK=LOOK, SEP=123*SC//128),
             'SC': SC, 'V': V, 'PAIRS': PAIRS, 'hindex': hindex, 'qindex': qindex, 'float': F}
    exec(compile(tree, '<audited-row-construction-only>', 'exec'), scope)
    return scope['solve'](state, None, SimpleNamespace(facets=facets), 0)


def main():
    started = time.monotonic()
    source_path = HERE/'cover_cross_moment_probe.py'
    raw = source_path.read_bytes()
    source = raw.decode('utf8')
    assert 'bound=-sign*a*b' in source and 'bound+=yadd(row,s,-2*int(v[0])*int(v[s+1]))' in source
    diagnostic_raw = (HERE/'cover-cross-moment-two.json').read_bytes()
    diagnostic = json.loads(diagnostic_raw)
    assert diagnostic['receipt']['script_sha256'] == sha(raw)
    frozen_raw = (HERE/'cover-curvature-parent64.input.json.gz').read_bytes()
    cases = {c['path']: c for c in json.loads(gzip.decompress(frozen_raw))['cases']}
    params_raw = (HERE.parent/'research-20261016-followup/window_reweight_rational.json').read_bytes()
    params = json.loads(params_raw)
    terms = [tuple(row) for row in params['a_upper'] if row[2]]
    table_raw = (HERE/'cover_newjet.json').read_bytes()
    table = json.loads(table_raw)
    details = []
    for recorded in diagnostic['rows']:
        state = cases[recorded['path']]['before']
        rows, center, radius, bounds, err = row_constructor(source, terms, table, state)
        assert err == 0
        rlt_checks = mc_checks = psd_checks = 0
        for sample in range(5):
            ys = [F(-1) if sample == 0 else F(1) if sample == 1 else F((r*(sample+1)) % 11-5, 5) for r in range(9)]
            point = Vec(F(0) for _ in range(V))
            point[:9] = [center[r]+radius[r]*ys[r] for r in range(9)]
            for t in range(41):
                L, U = bounds[9+t]
                point[9+t] = L+(U-L)*F((t+sample) % 5, 4)
            for s, r in PAIRS: point[hindex(s, r)] = ys[s]*ys[r]
            for s in range(9):
                for t in range(41): point[qindex(s, t)] = ys[s]*point[9+t]
            base_value = None
            rlt_index = 0
            for row, B, kind in rows:
                residual = row@point-B
                if kind == 'base_audit':
                    base_value = residual
                    rlt_index = 0
                elif kind == 'RLT_audit':
                    s, parity = divmod(rlt_index, 2)
                    sign = -1 if parity == 0 else 1
                    assert residual == base_value*(1+sign*ys[s])
                    rlt_index += 1
                    rlt_checks += 1
                else:
                    assert kind in ['moment_McCormick', 'cross_McCormick'] and residual <= 0
                    mc_checks += 1
            for vector in recorded['integer_PSD_cut_vectors']:
                row = Vec(F(0) for _ in range(V))
                B = vector[0]**2
                for s in range(9):
                    coefficient = -2*vector[0]*vector[s+1]
                    row[s] += F(coefficient, radius[s])
                    B += coefficient*center[s]/radius[s]
                    for r in range(s, 9):
                        row[hindex(s, r)] = -(1 if s == r else 2)*vector[s+1]*vector[r+1]
                square = (vector[0]+sum(vector[r+1]*ys[r] for r in range(9)))**2
                assert row@point-B == -square <= 0
                psd_checks += 1
        details.append({'path': recorded['path'], 'rational_factorized_samples': 5,
                        'RLT_exact_identities': rlt_checks, 'McCormick_valid_rows': mc_checks,
                        'recorded_PSD_cut_vectors': len(recorded['integer_PSD_cut_vectors']),
                        'PSD_exact_negative_square_identities': psd_checks})
    receipt = {'scope': __doc__, 'script_sha256': sha(Path(__file__).read_bytes()),
               'producer_sha256': sha(raw), 'diagnostic_sha256': sha(diagnostic_raw),
               'cell_input_sha256': sha(frozen_raw), 'parameters_sha256': sha(params_raw),
               'table_sha256': sha(table_raw), 'all_algebra_checks_passed': True,
               'cases': details, 'generic_dense_old_rows_per_case': 3,
               'old_row_soundness_reproved': False, 'floating_LP_primal_verified': False,
               'PSD_feasibility_proven': False, 'strict_certificates': 0,
               'complete_global_cover': False, 'new_zero_proportion_proven': False,
               'seconds': time.monotonic()-started}
    output = HERE/'cover-cross-moment-algebra-replay.json'
    output.write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'all_algebra_checks_passed': True, 'cases': details,
                      'seconds': receipt['seconds'], 'receipt_sha256': sha(output.read_bytes())}), flush=True)


if __name__ == '__main__':
    main()
