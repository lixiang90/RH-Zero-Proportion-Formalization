"""One authorized static comparison of 391 fifth-derivative grid bounds.

Use frozen normalized W coefficients already linked to actual derivatives by
Lean. Compare exact interval Horner and the existing FI-1e30 implementation
with the old provider's M5 values. No Lean, optimizer, new sample or producer
execution; all inputs must retain their initial hashes.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
from collections import Counter
import hashlib
import json
import re
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
S = 10**30
DS = 10**15


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def add(a, b):
    return (a[0]+b[0], a[1]+b[1])


def mul(a, b):
    corners = [a[i]*b[j] for i in range(2) for j in range(2)]
    return (min(corners), max(corners))


def ceil(q):
    return -((-q.numerator)//q.denominator)


def mul_fi(a, b):
    lo, hi = mul(a, b)
    return (lo//S, -((-hi)//S))


def horner(coefficients, x, product=mul):
    value = coefficients[-1]
    for c in reversed(coefficients[:-1]):
        value = add(c, product(value, x))
    return value


def m5(interval, remainder):
    return ceil(max(abs(interval[0]-remainder), abs(interval[1]+remainder))*DS)


def main():
    began = time.monotonic()
    paths = [Path(__file__),
             ROOT/'research-goal-20261017-swap67-quartic/swap67-quartic-static.json',
             ROOT/'research-goal-20261016/window_normalized_interval.json',
             ROOT/'research-goal-20261016/cover_newjet.json',
             ROOT/'StructuralGoal20261016/WindowRawCoefficientData.lean',
             ROOT/'StructuralGoal20261016/WindowRawCoefficients.lean',
             ROOT/'StructuralGoal20261016/WindowFixedDerivative.lean',
             ROOT/'StructuralGoal20261016/WindowCellDerivative.lean',
             ROOT/'StructuralGoal20261016/WindowFixedHornerChoice.lean',
             ROOT/'StructuralGoal20261016/WindowFixedInterval.lean']
    start = {p.relative_to(ROOT).as_posix(): sha(p) for p in paths}
    packet, wd, ud = [json.loads(p.read_bytes()) for p in paths[1:4]]
    w = {int(n): [tuple(map(F, x)) for x in row]
         for n, row in wd['integer_w_Taylor_coefficients'].items()}
    u = {int(n): [tuple(map(F, x)) for x in row]
         for n, row in ud['integer_taylor_coefficients'].items()}
    rawtext = paths[4].read_text(encoding='utf8').split('def values : List (List FI) := [',1)[1].split('\n\ndef W',1)[0]
    rawrows = re.findall(r'\[(iw.*?)\]', rawtext, re.S)
    raw = [[(int(a), int(a)+int(width)) for a,width in re.findall(r'iw \((-?\d+)\) \((\d+)\)', row)]
           for row in rawrows]
    assert len(raw)==32 and all(len(row)==24 for row in raw)
    assert all(tuple(F(v,S) for v in raw[n-1][j])==w[n][j]
               for n in range(1,33) for j in range(24))
    scalar_packets = [(str(edge['edge'])+':'+side, edge[side])
                      for edge in packet['changed_edge_packets'] for side in ('old','new')]
    cells = sorted({k for _,p in scalar_packets for k in p['whole_span_w5_grid_cells']})
    assert len(scalar_packets)==16 and len(cells)==391
    table_stats = Counter()
    used_stats = Counter()
    for n in range(1,33):
        for j in range(23):
            a,b = (x*(j+1) for x in w[n][j+1])
            c,d = u[n][j]
            for stats in [table_stats]+([used_stats] if 2<=n<=9 and 4<=j<=22 else []):
                stats['coefficients']+=1
                stats['identical']+=int(a==c and b==d)
                stats['normalized_contains_old']+=int(a<=c and d<=b)
                stats['old_contains_normalized']+=int(c<=a and b<=d)
    remainder = F(44,7)**24*F(1,2)**19/factorial(19)
    checks = []
    by_cell = {}
    for k in cells:
        n = round(F(2*k+1,128))
        x = (F(k,64)-n, F(k+1,64)-n)
        assert 1<=n<=32 and -F(1,2)<=x[0]<=x[1]<=F(1,2)
        old_coeff = [tuple(v*F(factorial(j+4),factorial(j)) for v in u[n][j+4])
                     for j in range(19)]
        new_coeff = [tuple(v*F(factorial(j+5),factorial(j)) for v in w[n][j+5])
                     for j in range(19)]
        old_interval = horner(old_coeff, x)
        exact_interval = horner(new_coeff, x)
        fi_coeff = [tuple(v*S for v in row) for row in new_coeff]
        assert all(v.denominator==1 for row in fi_coeff for v in row)
        fi_coeff = [tuple(int(v) for v in row) for row in fi_coeff]
        fi_x = tuple(v*S for v in x)
        assert all(v.denominator==1 for v in fi_x)
        fi_interval = tuple(F(v,S) for v in horner(fi_coeff, tuple(map(int,fi_x)), mul_fi))
        assert fi_interval[0]<=exact_interval[0]<=exact_interval[1]<=fi_interval[1]
        oldM, exactM, fiM = [m5(i,remainder) for i in (old_interval,exact_interval,fi_interval)]
        row = {'k': k, 'integer_center': n, 'old_M5_ticks': str(oldM),
               'normalized_exact_M5_ticks': str(exactM), 'normalized_FI_M5_ticks': str(fiM),
               'exact_minus_old_ticks': exactM-oldM, 'FI_minus_old_ticks': fiM-oldM}
        checks.append(row)
        by_cell[k] = row
    spans = []
    for name,p in scalar_packets:
        ks = p['whole_span_w5_grid_cells']
        oldM = max(int(by_cell[k]['old_M5_ticks']) for k in ks)
        exactM = max(int(by_cell[k]['normalized_exact_M5_ticks']) for k in ks)
        fiM = max(int(by_cell[k]['normalized_FI_M5_ticks']) for k in ks)
        assert F(oldM,DS)==F(p['whole_span_absolute_w5_bound'])
        spans.append({'packet':name,'cells':len(ks),'old_M5_ticks':str(oldM),
                      'normalized_exact_M5_ticks':str(exactM),'normalized_FI_M5_ticks':str(fiM),
                      'exact_minus_old_ticks':exactM-oldM,'FI_minus_old_ticks':fiM-oldM})
    end = {p.relative_to(ROOT).as_posix(): sha(p) for p in paths}
    assert start==end
    out = {'scope': __doc__, 'source_sha256_start': start, 'source_sha256_end': end,
           'all_sources_unchanged': True, 'normalized_W_matches_proved_raw_literals': 32*24,
           'whole_old_table_comparison': dict(table_stats),
           'used_centers_2_to_9_old_orders_4_to_22_comparison':dict(used_stats),
           'table_containment_does_not_assert_old_table_invalid':True,
           'static_cell_checks':len(checks), 'scalar_packets':16,
           'unique_anchor_points':len({p['anchor'] for _,p in scalar_packets}),
           'grid_cell_rows':checks,'packet_M5_comparison':spans,
           'max_extra_FI_ticks_per_cell':max(0,max(r['FI_minus_old_ticks'] for r in checks)),
           'max_extra_FI_ticks_per_packet':max(0,max(r['FI_minus_old_ticks'] for r in spans)),
           'all_packet_M5_preserved_by_normalized_FI':all(r['FI_minus_old_ticks']<=0 for r in spans),
           'Horner_FI_scale':str(S),'M5_tick_scale':str(DS),
           'required_new_Lean_cell_checks':391,'Lean_invocations':0,'solver_calls':0,
           'old_producer_executed':False,'actual_numeric_M5_Lean_proven_here':False,
           'new_actual_cell_exclusion':False,'new_zero_proportion_proven':False,
           'elapsed_seconds':time.monotonic()-began}
    target = HERE/'m5-compatibility-audit.json'
    assert not target.exists()
    target.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['static_cell_checks','unique_anchor_points',
        'max_extra_FI_ticks_per_cell','max_extra_FI_ticks_per_packet',
        'all_packet_M5_preserved_by_normalized_FI','elapsed_seconds']}))


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled')
    main()
