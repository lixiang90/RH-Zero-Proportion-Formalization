"""Standalone exact replay of signed 32-star-cycle interval evidence.

Do not import the producer or numerical libraries. Rebuild fixed-dual
uniform interval bounds and rational-star relaxed witnesses using our own
Q30 interval arithmetic. The exact kernel/trigonometric helper and the
phase coefficient Taylor Provider are shared, with source/data hashes.
No matrix solve, eigenvalue, SVD, optimizer, Lean, or cover search is run.
The five strict witnesses concern only the specified 32-star relaxation.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
import gzip
import hashlib
import json
import sys
import time

import window_interval_kernel as ik
import window_phase_coefficients as phase

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SC, Q = 32768, 10**30
sha = lambda raw: hashlib.sha256(raw).hexdigest()
floor = lambda x: F(x).numerator//F(x).denominator
ceil = lambda x: -floor(-F(x))


class J:
    """Independent fixed-grid implementation; no phase.RI arithmetic used."""
    def __init__(self, l, u=None):
        self.l, self.u = floor(F(l)*Q), ceil(F(l if u is None else u)*Q)
        assert self.l <= self.u
    @classmethod
    def raw(cls, l, u):
        obj = object.__new__(cls)
        obj.l, obj.u = int(l), int(u)
        assert obj.l <= obj.u
        return obj
    @staticmethod
    def lift(x): return x if isinstance(x, J) else J(x)
    def __add__(self, x):
        x = J.lift(x)
        return J.raw(self.l+x.l, self.u+x.u)
    __radd__ = __add__
    def __neg__(self): return J.raw(-self.u, -self.l)
    def __sub__(self, x): return self+-J.lift(x)
    def __rsub__(self, x): return J.lift(x)+-self
    def __mul__(self, x):
        x = J.lift(x)
        p = [a*b for a in [self.l, self.u] for b in [x.l, x.u]]
        return J.raw(min(p)//Q, -((-max(p))//Q))
    __rmul__ = __mul__
    def __truediv__(self, x):
        x = J.lift(x)
        assert x.l*x.u > 0
        p = [F(a*Q, b) for a in [self.l, self.u] for b in [x.l, x.u]]
        return J.raw(floor(min(p)), ceil(max(p)))
    def square(self):
        lower = 0 if self.l <= 0 <= self.u else min(self.l**2, self.u**2)
        return J.raw(lower//Q, -((-max(self.l**2, self.u**2))//Q))
    def bounds(self): return [str(F(self.l, Q)), str(F(self.u, Q))]


@lru_cache(None)
def sine_point(x):
    x = F(x)
    x -= 2*((x+1)//2)
    if x in [F(-1), F(0), F(1)]: return F(0), F(0)
    if x == F(1, 2): return F(1), F(1)
    if x == F(-1, 2): return F(-1), F(-1)
    v = ik.interval.sin_interval(ik.PI*x)
    return max(F(-1), v.l), min(F(1), v.u)


def sine_interval(l, u):
    l, u = F(l), F(u)
    assert l <= u
    if u-l >= 2: return J(-1, 1)
    a, b = sine_point(l), sine_point(u)
    low, high = min(a[0], b[0]), max(a[1], b[1])
    for k in range(ceil(l-F(1, 2)), floor(u-F(1, 2))+1):
        if k % 2: low = F(-1)
        else: high = F(1)
    return J(low, high)


class Replay:
    def __init__(self, params):
        self.edges = [(i, j, F(a, 10**10)) for i, j, a in params['a_upper'] if a]
        self.lookup = {(i, j): e for e, (i, j, a) in enumerate(self.edges)}
        self.all = [(i, i+1) for i in range(9)]+[(i, j) for i in range(10) for j in range(i+2, 10)]
        self.alookup = {p: k for k, p in enumerate(self.all)}
        self.pressure = [F(b, 10**10) for b in params['b_numerators']]
        self.star = {i: self.lookup[tuple(sorted((i, 1)))] for i in range(10) if i != 1}
        self.chords = [e for e, (i, j, _) in enumerate(self.edges) if i != 1 and j != 1]
        assert len(self.edges) == 41 and len(self.star) == 9 and len(self.chords) == 32
        assert all(a > 0 for i, j, a in self.edges)
        self.provider = phase.Provider()
        h = ik.Z/(2*ik.PI*ik.COSTH)
        assert h.l > 0 and ik.COSTH.l > 0 and ik.Z.l > 0
        self.h = J(h.l, h.u)
        self.piece_calls = 0
    @staticmethod
    def sign(i):
        assert i != 1
        return -1 if i < 1 else 1
    def edge_packets(self, state):
        rows = []
        for i, j, _ in self.edges:
            axis = self.alookup[i, j]
            l, u = state[0][axis], state[1][axis]
            lo, hi = F(l, SC), F(u, SC)
            assert F(123, 128) <= lo <= hi <= 32
            cuts = [l]+list(range((l//1024+1)*1024, u, 1024))+[u]
            pieces, digest = [], hashlib.sha256()
            for left, right in zip(cuts, cuts[1:]):
                _, _, amp = self.provider.amplitudes(F(left, SC), F(right, SC))
                A, C = J.raw(amp[0].l, amp[0].u), J.raw(amp[2].l, amp[2].u)
                assert A.l > 0
                ratio = C/A
                pieces.append(ratio)
                digest.update(json.dumps([left, right, [ratio.l, ratio.u]], separators=(',', ':')).encode())
                self.piece_calls += 1
            correction = J.raw(min(v.l for v in pieces), max(v.u for v in pieces))
            cosine = sine_interval(lo+F(1, 2), hi+F(1, 2))
            def amplitude_at(x):
                px = ik.PI*x
                return ik.COSTH*px/(ik.Z*(px.square()-F(1, 2)))
            atlo, athi = amplitude_at(lo), amplitude_at(hi)
            assert atlo.l > 0 and athi.l > 0
            inverse = J(1/atlo.u, 1/athi.l)
            beta = -self.h*cosine/J(lo, hi)+correction
            rows.append({'inverse': inverse, 'cosine': cosine, 'beta': beta,
                         'record': {'pair': [i, j], 'span_units': [l, u],
                                    'C_over_A': correction.bounds(), 'inverse_A': inverse.bounds(),
                                    'cosine': cosine.bounds(), 'beta': beta.bounds(),
                                    'Taylor_piece_count': len(pieces),
                                    'Taylor_piece_endpoint_sha256': digest.hexdigest()}})
        return rows
    def cycle_rhs(self, rows, edge):
        i, j, _ = self.edges[edge]
        ei, ej = self.star[i], self.star[j]
        ri, rj, re = rows[ei], rows[ej], rows[edge]
        return re['beta']-self.sign(j)*ri['cosine']*rj['beta']+self.sign(i)*rj['cosine']*ri['beta']
    def dual(self, state, strings, expected):
        assert len(strings) == 32
        y = list(map(F, strings))
        assert all((2**30) % v.denominator == 0 for v in y)
        rows = self.edge_packets(state)
        q, linear = [J(0) for _ in self.edges], J(0)
        for value, e in zip(y, self.chords):
            i, j, _ = self.edges[e]
            ei, ej = self.star[i], self.star[j]
            linear += 2*value*self.cycle_rhs(rows, e)
            q[e] += value*rows[e]['inverse']
            q[ej] -= value*self.sign(j)*rows[ei]['cosine']*rows[ej]['inverse']
            q[ei] += value*self.sign(i)*rows[ej]['cosine']*rows[ei]['inverse']
        cost = sum((v.square()/a for v, (_, _, a) in zip(q, self.edges)), J(0))
        bound = linear-cost
        energy = F(bound.l, Q)
        pressure = sum(b*F(state[0][self.alookup[r, r+1]], SC) for r, b in enumerate(self.pressure))
        assert expected['fixed_rational_dual'] == strings
        assert expected['edge_packets'] == [row['record'] for row in rows]
        for key, interval in [('twice_yD_interval', linear), ('dual_quadratic_cost_interval', cost), ('uniform_E_dual_interval', bound)]:
            assert list(map(F, expected[key])) == list(map(F, interval.bounds()))
        assert energy == F(expected['uniform_E_lower']) and pressure == F(expected['pressure_lower'])
        assert pressure+max(F(0), energy) == F(expected['uniform_F_lower'])
        return {'all_exact_packets_matched': True, 'edges': 41,
                'uniform_E_lower': str(energy), 'uniform_F_lower': str(pressure+max(F(0), energy)),
                'pressure_lower': str(pressure)}
    def point_witness(self, gaps, strings, expected):
        prefix = [F(0)]
        for g in gaps: prefix.append(prefix[-1]+F(g))
        spans = [SC*(prefix[j]-prefix[i]) for i, j in self.all]
        state = [[floor(x) for x in spans], [ceil(x) for x in spans]]
        assert all(F(l, SC) <= prefix[j]-prefix[i] <= F(u, SC)
                   for (i, j), l, u in zip(self.all, *state))
        rows = self.edge_packets(state)
        k = [None]*41
        for vertex, e in self.star.items():
            value = F(strings[str(vertex)])
            assert (2**30) % value.denominator == 0
            k[e] = J(value)
        for e in self.chords:
            i, j, _ = self.edges[e]
            ei, ej = self.star[i], self.star[j]
            k[e] = (self.cycle_rhs(rows, e)+self.sign(j)*rows[ei]['cosine']*rows[ej]['inverse']*k[ej]
                    -self.sign(i)*rows[ej]['cosine']*rows[ei]['inverse']*k[ei])/rows[e]['inverse']
        assert all(v is not None for v in k)
        energy = sum((a*v.square() for v, (_, _, a) in zip(k, self.edges)), J(0))
        upper = F(energy.u, Q)
        pressure = sum(b*F(g) for b, g in zip(self.pressure, gaps))
        assert list(map(F, expected['exact_point_positions'])) == prefix
        assert expected['rational_star_coordinates'] == strings
        assert expected['selected_32_cycle_constraints_exactly_satisfied_by_construction']
        assert pressure == F(expected['point_pressure_exact'])
        assert upper == F(expected['projected_feasible_energy_upper'])
        assert pressure+upper == F(expected['pressure_plus_projection_upper'])
        strict = pressure+upper < F(11, 1250)
        assert strict == expected['strictly_below_0088']
        assert F(11, 1250)-pressure-upper == F(expected['margin_to_0088'])
        return {'all_exact_point_bounds_matched': True, 'pressure_plus_projection_upper': str(pressure+upper),
                'strictly_below_0088': strict, 'scope': 'Only selected 32-star-cycle system; not actual kernel or KKT.'}


def main():
    started = time.monotonic()
    producer_paths = [HERE/'window_joint_cycle_projection_note.txt', HERE/'window_joint_cycle_projection_probe.py',
                      HERE/'window_joint_cycle_projection_probe.json']
    frozen_hashes = {p.name: sha(p.read_bytes()) for p in producer_paths}
    doc = json.loads(producer_paths[2].read_bytes())
    assert doc['script_sha256'] == frozen_hashes[producer_paths[1].name]
    source_paths = [ROOT/'research-20261016-followup/window_reweight_rational.json', HERE/'cover-lifted-graph-energy8.json',
                    HERE/'cover-curvature-parent64.input.json.gz', HERE/'window_phase_coefficients.py',
                    HERE/'window_interval_kernel.py', ROOT/'StructuralGoal20261016/WindowJetTableData.lean']
    for p in source_paths: assert doc['source_sha256'][p.name] == sha(p.read_bytes())
    params = json.loads(source_paths[0].read_bytes())
    replay = Replay(params)
    assert doc['star_root'] == 1 and doc['cycles'] == 32
    assert {int(i): e for i, e in doc['star_edge_indices'].items()} == replay.star
    assert doc['independent_chord_edge_indices'] == replay.chords
    triangles = [(i, j, l) for i in range(10) for j in range(i+1, 10) for l in range(j+1, 10)
                 if all(p in replay.lookup for p in [(i, j), (j, l), (i, l)])]
    assert len(triangles) == 90
    selected = json.loads(source_paths[1].read_bytes())['rows']
    inputs = json.loads(gzip.decompress(source_paths[2].read_bytes()))
    lookup = {row['path']: row for row in inputs['cases']}
    assert [row['path'] for row in doc['residual8_point_diagnostics']] == [row['path'] for row in selected]
    results = []
    for index, row in enumerate(doc['residual8_point_diagnostics']):
        state = lookup[row['path']]['before']
        prefix = [F(0)]+[F(state[0][replay.alookup[0, j]]+state[1][replay.alookup[0, j]], 2*SC) for j in range(1, 10)]
        gaps = [prefix[j+1]-prefix[j] for j in range(9)]
        assert list(map(F, row['gaps'])) == gaps
        assert all(F(l, SC) <= prefix[j]-prefix[i] <= F(u, SC) for (i, j), l, u in zip(replay.all, *state))
        dual = replay.dual(state, row['rational_dual_weights'], row['uniform_cell_fixed_dual'])
        witness = replay.point_witness(gaps, row['rational_star_feasible_witness'], row['strict_point_projection_witness'])
        assert F(dual['uniform_E_lower']) < 0
        results.append({'selection_index': index, 'path': row['path'], 'uniform_dual': dual, 'relaxed_point_witness': witness})
    assert [r['selection_index'] for r in results if r['relaxed_point_witness']['strictly_below_0088']] == [0, 1, 4, 6, 7]
    low = doc['low_pressure_point_diagnostics']
    assert list(map(F, low[0]['gaps'])) == [F(1)]*9 and list(map(F, low[1]['gaps'])) == [F(9, 4)]+[F(1)]*8
    bands = []
    for ru, row in zip([256, 512, 1024], doc['low_pressure_integer_bands']):
        assert F(row['radius']) == F(ru, SC)
        state = [[(j-i)*SC-ru for i, j in replay.all], [(j-i)*SC+ru for i, j in replay.all]]
        result = replay.dual(state, low[0]['rational_dual_weights'], row)
        assert F(result['pressure_lower']) == (1-F(ru, SC))*sum(replay.pressure)
        bands.append({'radius': str(F(ru, SC)), **result})
    assert F(bands[-1]['uniform_E_lower']) > F(4683, 10**6)
    assert F(bands[-1]['uniform_F_lower']) > F(8967, 10**6) > F(221, 25000)
    assert F(bands[-1]['pressure_lower']) == F(42840725125, 10**13)
    assert F(31, 32) > F(123, 128)
    assert all(sha(p.read_bytes()) == frozen_hashes[p.name] for p in producer_paths)
    assert not any(name in sys.modules for name in ['numpy', 'scipy', 'networkx'])
    dependencies = source_paths+[Path(ik.interval.__file__), Path(__file__)]
    receipt = {'scope': __doc__, 'frozen_producer_sha256': frozen_hashes,
               'dependency_sha256': {p.resolve().relative_to(ROOT).as_posix(): sha(p.read_bytes()) for p in dependencies},
               'all_exact_checks_passed': True, 'no_site_packages': sys.flags.no_site,
               'no_numerical_libraries_or_producer_imported': True,
               'shared_kernel_and_phase_Taylor_provider': True,
               'independent_fixed_grid_interval_arithmetic': True,
               'replayed_uniform_duals': 11, 'uniform_edge_packets': 11*41,
               'replayed_relaxed_point_witnesses': 8, 'strict_32_star_subsystem_witnesses': 5,
               'amplitude_Taylor_piece_calls': replay.piece_calls, 'residual8': results, 'integer_bands': bands,
               'all_one_radius_1_over_32_uniform_F_above_8967_over_1e6': True,
               'ninety_triangle_combinatorial_count_checked': True,
               'ninety_triangle_rank_40_or_SVD_replayed': False,
               'floating_matrix_solves_or_eigen_computations_replayed': False,
               'point_witnesses_are_actual_kernel_vectors': False,
               'complete_cycle_route_refuted': False, 'ordinary_Lean_proven': False,
               'complete_global_cover': False, 'new_zero_proportion_proven': False,
               'seconds': time.monotonic()-started}
    output = HERE/'window-joint-cycle-projection-independent-replay.json'
    output.write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'all_exact_checks_passed': True, 'uniform_duals': 11,
                      'strict_relaxed_32_star_witnesses': 5,
                      'r1_32_uniform_F_lower': float(F(bands[-1]['uniform_F_lower'])),
                      'seconds': receipt['seconds'], 'receipt_sha256': sha(output.read_bytes())}), flush=True)


if __name__ == '__main__':
    main()
