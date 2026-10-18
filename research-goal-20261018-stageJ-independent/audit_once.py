"""Independent full JLB2 certificate audit, prepared without mathematics runs.

Only our frozen independent A source parser is imported after a future gate.
No J producer/I producer/shared core import, optimizer, geometry search, points,
kernel queries or Lean. Singular-only input needs no FS/affine energy replay.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
import gzip
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import time
import traceback

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PROD = ROOT / 'research-goal-20261018-stageJ-fixed-basis-preparation'
OWN_A = ROOT / 'research-goal-20261018-record-baseline-independent/replay_independent.py'
B = ROOT / 'research-goal-20261018-stageB-classification'
H = ROOT / 'research-goal-20261018-stageH-ordered-transport'
N, COUNT, Q, R, D, V, SA = 1187, 15378, 32768, 1024, 10**9, 10**10, 10**20
KAPPA = Q * V * R
CN, TAU, CANDIDATE = 893616123055294719, 893916123055294719, 893766123055294719
TARGET = 4 * KAPPA * CANDIDATE
SEED = [9, 29, 36, 74, 84, 110, 130, 153, 154]
CHARTS = ['id/id', 'id/rev', 'rev/id', 'rev/rev']
NAMES = ['negative_multiplier', 'Lower', 'valid_but_below_target', 'singular_chart']
MAGIC = b'JLB2\n'
SECONDS, BYTES = 300, 20000000


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode('ascii')


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text(encoding='utf8'))


def checked_path(name):
    assert type(name) is str
    path = (ROOT / name).resolve()
    assert path.is_relative_to(ROOT)
    return path


def save(name, value):
    with (HERE / name).open('xb') as stream:
        stream.write(canonical(value)); stream.flush(); os.fsync(stream.fileno())


def size(path=HERE):
    return sum(p.stat().st_size for p in path.iterdir() if p.is_file())


def signed(value):
    assert type(value) is str
    number = int(value)
    assert str(number) == value
    return number


def check_limit(start):
    assert time.monotonic() - start <= SECONDS, 'audit_time_limit'
    assert size() <= BYTES, 'audit_output_limit'


def append_pin(refs, name, expected, byte_count=None):
    path = checked_path(name)
    assert digest(path) == expected, name
    if byte_count is not None:
        assert path.stat().st_size == byte_count
    if name in refs:
        assert refs[name] == expected
    refs[name] = expected


def identity(args):
    refs = {}
    append_pin(refs, args.gate, args.gate_sha256)
    gate = read(checked_path(args.gate))
    assert type(gate['full_J_classification_audits_authorized']) is int
    assert gate['full_J_classification_audits_authorized'] == 1
    assert gate['expected_H_remaining'] == COUNT
    assert gate['resource_limits'] == {'elapsed_seconds': SECONDS, 'closed_output_bytes': BYTES}
    assert gate['automatic_retry_allowed'] is False
    assert type(gate['new_search_optimizer_points_kernel_or_Lean_authorized']) is int
    assert gate['new_search_optimizer_points_kernel_or_Lean_authorized'] == 0
    prepared = HERE / 'prepared-files.json'
    assert digest(prepared) == gate['prepared_manifest_sha256']
    refs[prepared.relative_to(ROOT).as_posix()] = digest(prepared)
    prep = read(prepared)
    for field in ['files', 'read_only_dependencies']:
        for row in prep[field]:
            append_pin(refs, row['path'], row['sha256'], row['bytes'])
    runtime = prep['runtime']
    assert Path(sys.executable).resolve() == Path(runtime['executable']).resolve()
    assert digest(Path(sys.executable)) == runtime['sha256']
    assert sys.version == runtime['version'] and sys.flags.optimize == 0
    for row in runtime['additional_files']:
        assert digest(Path(row['path'])) == row['sha256']
    manifest_row = gate['producer_manifest']
    assert manifest_row['path'] == 'research-goal-20261018-stageJ-fixed-basis-preparation/files.json'
    append_pin(refs, manifest_row['path'], manifest_row['sha256'])
    manifest = read(checked_path(manifest_row['path']))
    inventory = set()
    for field in ['files', 'package_files', 'read_only_dependencies', 'dependency_files', 'dependencies']:
        for row in manifest.get(field, []):
            append_pin(refs, row['path'], row['sha256'], row.get('bytes'))
            inventory.add(row['path'])
    for name in ['result.json', 'terminal.json', 'basis.json', 'prefix.json', 'classifications.bin',
                 'remaining-indices.u32.bin', 'affine-cache.jsonl', 'cache-index.json']:
        assert 'research-goal-20261018-stageJ-fixed-basis-preparation/' + name in inventory
    for key, name in [('producer_result', 'result.json'), ('producer_terminal', 'terminal.json')]:
        row = gate[key]
        assert row['path'] == 'research-goal-20261018-stageJ-fixed-basis-preparation/' + name
        append_pin(refs, row['path'], row['sha256'])
    assert size(PROD) <= BYTES
    return gate, refs, runtime


def load_original_rows():
    cells = []
    with gzip.open(B / 'exception-cells.jsonl.gz', 'rb') as stream:
        for line in stream:
            row = json.loads(line)
            assert canonical(row) == line
            assert type(row['exception_id']) is int and row['exception_id'] == len(cells)
            assert row['kind'] == 'exception' and row['coordinate_scale'] == Q
            assert row['separation'] == '17/20' and type(row['state']['M']) is int and row['state']['M'] == 0
            lo, hi = row['state']['L'] + row['state']['A'], row['state']['U'] + row['state']['B']
            assert len(lo) == len(hi) == 36 and all(type(v) is int for v in lo + hi)
            assert 0 <= signed(row['original_margin']) < KAPPA * (TAU - CN)
            assert signed(row['tau_margin']) == signed(row['original_margin']) - KAPPA * (TAU - CN)
            cells.append(row)
    assert len(cells) == N
    raw = (H / 'remaining-indices.u32.bin').read_bytes()
    assert len(raw) == 4 * COUNT
    indices = [a[0] for a in struct.iter_unpack('<I', raw)]
    assert all(0 <= q < 4 * N * N for q in indices)
    assert all(a < b for a, b in zip(indices, indices[1:]))
    assert 2417 in indices and 4768 not in indices
    return cells, indices, raw


def chart_flags(chart):
    assert type(chart) is int and chart in range(4)
    return ((chart & 2) != 0, (chart & 1) != 0)


def unit_difference(first, second):
    row = [0] * 10
    row[first] -= 1; row[second] += 1
    return row


def geometry(chart, spans):
    rows = []
    for offset, reverse in enumerate(chart_flags(chart)):
        for left, right in spans:
            a, b = (offset + 8 - right, offset + 8 - left) if reverse else (offset + left, offset + right)
            assert 0 <= a < b <= 9
            upper = unit_difference(a, b)
            rows.append(upper); rows.append([-x for x in upper])
    rows.extend(unit_difference(r + 1, r) for r in range(9))
    for offset, reverse in enumerate(chart_flags(chart)):
        first_gap = offset + (7 if reverse else 0)
        last_gap = offset + (0 if reverse else 7)
        first = unit_difference(first_gap, first_gap + 1)
        last = unit_difference(last_gap, last_gap + 1)
        rows.append([a - b for a, b in zip(first, last)])
    assert len(rows) == 155 and all(sum(a) == 0 for a in rows)
    assert all(type(x) is int for row in rows for x in row)
    return rows


def determinant(matrix):
    """Integer Bareiss elimination, independent of the producer inverse path."""
    work = [list(row) for row in matrix]
    n, previous, parity = len(work), 1, 1
    assert all(len(row) == n for row in work)
    for column in range(n - 1):
        available = [r for r in range(column, n) if work[r][column] != 0]
        if not available:
            return 0
        pivot_row = available[0]
        if pivot_row != column:
            work[column], work[pivot_row] = work[pivot_row], work[column]
            parity = -parity
        pivot = work[column][column]
        for r in range(column + 1, n):
            left = work[r][column]
            for c in range(column + 1, n):
                value = pivot * work[r][c] - left * work[column][c]
                assert value % previous == 0
                work[r][c] = value // previous
            work[r][column] = 0
        previous = pivot
    return parity * work[-1][-1]


def rank_exact(matrix):
    work = [[F(x) for x in row] for row in matrix]
    pivots = 0
    for column in range(len(work[0])):
        candidates = [r for r in range(pivots, len(work)) if work[r][column]]
        if not candidates:
            continue
        selected = candidates[0]
        work[selected], work[pivots] = work[pivots], work[selected]
        value = work[pivots][column]
        for r in range(pivots + 1, len(work)):
            factor = work[r][column] / value
            if factor:
                work[r] = [a - factor * b for a, b in zip(work[r], work[pivots])]
        pivots += 1
    return pivots


def validate_bases(source, producer):
    assert producer['schema'] == 'J-fixed-four-chart-bases-v1'
    assert producer['seed_row_ids'] == SEED and signed(producer['target']) == TARGET
    assert len(producer['charts']) == 4
    all_rows, summaries = [], []
    for chart, saved in enumerate(producer['charts']):
        rows = geometry(chart, source['ALL'])
        selected = [rows[k] for k in SEED]
        transposed = [list(column) for column in zip(*(row[1:] for row in selected))]
        actual_det = determinant(transposed)
        actual_rank = rank_exact(transposed)
        assert (actual_det == 0) == (actual_rank < 9)
        assert saved['chart'] == chart and saved['chart_name'] == CHARTS[chart]
        assert saved['basis_row_ids'] == SEED and saved['selected_full10_normals'] == selected
        assert saved['A_transposed_reduced'] == transposed and saved['rank'] == actual_rank
        assert saved['determinant'] == actual_det and saved['singular'] is (actual_det == 0)
        if actual_det == 0:
            assert saved['denominator'] is None and saved['scaled_inverse'] is None
        else:
            denominator = abs(actual_det)
            assert denominator in [1, 2, 3, 4] and saved['denominator'] == denominator
            scaled = saved['scaled_inverse']
            assert len(scaled) == 9 and all(len(row) == 9 for row in scaled)
            assert all(type(x) is int for row in scaled for x in row)
            for r in range(9):
                for c in range(9):
                    assert sum(transposed[r][k] * scaled[k][c] for k in range(9)) == denominator * int(r == c)
            assert saved['A_times_scaled_inverse_equals_denI'] is True
        all_rows.append(rows)
        summaries.append({'chart': chart, 'rank': actual_rank, 'determinant': actual_det,
                          'scaled_inverse_identity_verified': actual_det != 0})
    return all_rows, summaries


def load_history(roots):
    events = {}
    path = ROOT / 'research-goal-20261018-record-baseline-replay/baseline-events.jsonl.gz'
    with gzip.open(path, 'rb') as stream:
        for line in stream:
            event = json.loads(line)
            if event['root'] in roots:
                assert canonical(event) == line
                key = (event['root'], event['pos'])
                assert key not in events
                events[key] = event
    return events


def locate_original(runner, model, row, history):
    root, position = row['root'], 1
    state = runner.root(model['roots'][root]['indices'])
    assert row['path'].startswith('r') and set(row['path'][1:]) <= {'0', '1'}
    def word_at(at):
        return (model['dispatch_value']('WL' + str(root), at // Q) >> (at % Q)) & ((1 << 480) - 1)
    for direction in row['path'][1:]:
        old = history[(root, position)]
        word = word_at(position)
        assert old['kind'] == 'branch' and old['state_sha256'] == runner.hashstate(state)
        assert word & 1 and old['left'] == position + 8
        axis, mode = (word >> 1) & 63, (word >> 7) & 1
        assert axis == old['axis'] and mode == old['mode'] and axis < 36
        low, high = state[0][axis], state[1][axis]
        cut = (low + high) // 2
        if mode:
            eligible = [(abs(2 * candidate - low - high), order, candidate)
                        for order, candidate in enumerate(model['BND'])
                        if low + 64 <= candidate and candidate + 64 <= high]
            if eligible:
                cut = min(eligible)[2]
        assert cut == old['cut']
        left, right = model['ALL'][axis]
        state = runner.split(state, left, right, cut, direction == '0')
        position = old['left'] if direction == '0' else old['right']
    terminal = history[(root, position)]
    assert terminal['kind'] == 'numeric' and terminal['end'] == row['end']
    assert position == row['position'] and terminal['state_sha256'] == row['state_sha256']
    assert runner.hashstate(state) == row['state_sha256']
    assert state == (row['state']['L'] + row['state']['A'], row['state']['U'] + row['state']['B'])
    raw = word_at(position)
    assert raw & 3 == 0 and state[1][7] >= state[0][0]
    return state, raw >> 2


def original_affine(own, source, row, history):
    runner = own.Replay(source)
    state, word = locate_original(runner, source, row, history)
    consumed, ast_margin = runner.numeric(state, word)
    assert row['position'] + 2 + consumed == row['end']
    assert ast_margin == signed(row['original_margin']) >= 0
    at, FS, components = 0, [], []
    cstar, coefficients = 0, [D * R * x for x in source['BS']]
    weighted_mv = weighted_cp = weighted_cn = 0
    for term_id, (i, j, weight, _slot) in enumerate(source['TS']):
        low, high = runner.bounds(state, i, j)
        lower_gap_sum = sum(state[0][i:j])
        assert lower_gap_sum <= low <= high
        fields, at = runner.decode_term(word, at, low, high)
        kind, mass, first, second = fields
        FS.append(list(fields))
        one, two = runner.weights(kind, mass)
        constant_mass = R - one - two
        assert 0 <= mass <= R and min(one, two, constant_mass) >= 0
        assert one + two + constant_mass == R
        packed = [source['point_value'](a) & ((1 << 96) - 1) for a in [first, second]]
        guards = []
        for amount, anchor in zip([one, two], [first, second]):
            if amount:
                assert anchor in source['pts']
                absolute = source['point_value'](anchor)
                guard_low, guard_high = (absolute >> 96) & ((1 << 24) - 1), absolute >> 120
                assert 1 <= guard_high and guard_low <= low <= anchor <= high <= guard_high
                guards.append({'mass': amount, 'original_anchor': anchor, 'valid_lower': guard_low,
                               'valid_upper': guard_high, 'guard_passed': True})
        upper = max(high, low + 1)
        table = runner.lower_bound(low, upper)
        values = [p & ((1 << 32) - 1) for p in packed]
        slopes = [(p >> 32) & ((1 << 32) - 1) for p in packed]
        derivative_upper = [p >> 64 for p in packed]
        distances = [max(p - lower_gap_sum, 0) for p in [first, second]]
        cp = sum(a * max(u - 2 * D, 0) * z for a, u, z in zip([one, two], derivative_upper, distances))
        cn = sum(a * max(2 * D - u, 0) * z for a, u, z in zip([one, two], derivative_upper, distances))
        mv = constant_mass * table + one * values[0] + two * values[1]
        msl, mw = one * slopes[0] + two * slopes[1], one + two
        delta = msl - 2 * D * mw
        beta = F(mv, V * R) + F(cp - cn, Q * D * R) - F(delta * lower_gap_sum, Q * D * R)
        sigma = F(delta, D * R)
        local_constant = Q * mv + 10 * (cp - cn - delta * lower_gap_sum)
        assert KAPPA * beta == local_constant
        cstar += weight * local_constant
        for gap in range(i, j):
            coefficients[gap] += weight * delta
        weighted_mv += weight * mv; weighted_cp += weight * cp; weighted_cn += weight * cn
        components.append({'term_id': term_id, 'edge': [i, j], 'external_weight_numerator': weight,
            'external_weight_denominator': SA, 'original_term_bounds': [low, high], 'uc_upper': upper,
            'original_L0': lower_gap_sum, 'FS': list(fields), 'mass_constant': constant_mass,
            'mass_first': one, 'mass_second': two, 'original_lb_table_value': table,
            'active_mokI_guards': guards, 'mvT': mv, 'mslT': msl, 'mwT': mw, 'mcpT': cp, 'mcnT': cn,
            'signed_delta': delta, 'beta': str(beta), 'sigma': str(sigma)})
    P, S, Cp, Cm, end = runner.flow(state, word, at)
    assert end == consumed and 0 < consumed <= 478
    semantic = {'FS': FS, 'P': P, 'S': S, 'Cp': Cp, 'Cm': Cm, 'consumed_bits': end}
    payload = {'bits': end, 'value': str(word & ((1 << end) - 1))}
    witness = {'WD': row['root'], 'original_leaf_position': row['position'],
               'payload_bit_position': row['position'] + 2, 'consumed_payload_bits': end,
               'original_rdw_block': row['position'] // Q, 'original_rdw_shift': row['position'] % Q,
               'packed_payload_sha256': sha256(canonical(payload)).hexdigest(),
               'decoded_semantic_sha256': sha256(canonical(semantic)).hexdigest()}
    assert witness == row['witness']
    penalty = sum((state[1][r] - state[0][r]) * max(P[r] - S[r] - coefficients[r], 0) for r in range(8))
    compact = V * R * sum(b * state[0][r] for r, b in enumerate(source['BS']))
    compact += Q * weighted_mv + 10 * (weighted_cp - weighted_cn + Cm - Cp - penalty) - KAPPA * CN
    assert compact == ast_margin
    return {'cell_id': row['exception_id'], 'original_root': row['root'], 'original_path': row['path'],
            'position': row['position'], 'end': row['end'], 'state_sha256': row['state_sha256'],
            'witness': witness, 'canonical_Cstar': str(cstar), 'canonical_J': [str(x) for x in coefficients],
            'original_compact_margin': str(compact), 'original_printed_AST_margin': str(ast_margin),
            'consumed_payload_bits': consumed, 'original_term_components_sha256': sha256(canonical(components)).hexdigest(),
            'guards_and_original_semantics_checked': True}


def audit_cache(own, source, cells, needed, start):
    history = load_history({cells[cid]['root'] for cid in needed})
    expected = {}
    with (PROD / 'affine-cache.jsonl').open('rb') as stream:
        for line in stream:
            saved = json.loads(line)
            assert canonical(saved) == line
            cid = saved['cell_id']
            assert type(cid) is int and cid in needed and cid not in expected
            rebuilt = original_affine(own, source, cells[cid], history)
            assert saved == rebuilt, ('original_affine_cache_mismatch', cid)
            expected[cid] = rebuilt
            if len(expected) % 16 == 0:
                check_limit(start)
    assert set(expected) == needed
    return expected


def objective(index, cache):
    pair, chart = divmod(index, 4)
    left, right = divmod(pair, N)
    constant = 2 * (signed(cache[left]['canonical_Cstar']) + signed(cache[right]['canonical_Cstar']))
    linear = [0] * 10
    for cell_id, offset, reverse in [(left, 0, chart_flags(chart)[0]), (right, 1, chart_flags(chart)[1])]:
        for original_gap, value in enumerate(cache[cell_id]['canonical_J']):
            physical_gap = offset + (7 - original_gap if reverse else original_gap)
            coefficient = signed(value)
            linear[physical_gap] -= coefficient
            linear[physical_gap + 1] += coefficient
    assert sum(linear) == 0
    return constant, linear, left, right, chart


def right_hand_sides(left, right, cells):
    result = []
    for cid in [left, right]:
        state = cells[cid]['state']
        lo, hi = state['L'] + state['A'], state['U'] + state['B']
        for l, u in zip(lo, hi):
            result += [20 * u, -20 * l]
    result += [-17 * Q] * 9 + [0, 0]
    assert len(result) == 155
    return result


def unsigned_leb(value):
    out = bytearray()
    while value >= 128:
        out.append((value & 127) | 128); value >>= 7
    out.append(value)
    return bytes(out)


def decode_signed(data, at):
    begin, value, shift = at, 0, 0
    while True:
        assert at < len(data), 'truncated_signed_N'
        byte = data[at]; at += 1
        value |= (byte & 127) << shift
        if byte < 128:
            break
        shift += 7
    assert unsigned_leb(value) == data[begin:at], 'noncanonical_ULEB'
    return (value // 2 if value % 2 == 0 else -(value // 2) - 1), at


def classify_every_record(data, indices, cells, bases, normals, cache, start):
    assert data.startswith(MAGIC)
    at, counts, remaining, proof_trace = len(MAGIC), Counter({name: 0 for name in NAMES}), [], sha256()
    for ordinal, index in enumerate(indices):
        assert at + 5 <= len(data), 'truncated_record'
        saved_index = struct.unpack_from('<I', data, at)[0]
        tag = data[at + 4]; at += 5
        assert saved_index == index and tag in range(4)
        supplied_N = None
        if tag in [1, 2]:
            supplied_N, at = decode_signed(data, at)
        chart = index % 4
        basis = bases[chart]
        if basis['singular']:
            expected_tag, numerator = 3, None
        else:
            constant, linear, left, right, actual_chart = objective(index, cache)
            assert actual_chart == chart
            scale, inverse = basis['denominator'], basis['scaled_inverse']
            # Each row of the shared inverse labels one selected source normal.
            multipliers = [-sum(row[v] * linear[v + 1] for v in range(9)) for row in inverse]
            for coordinate in range(10):
                assert scale * linear[coordinate] + sum(multipliers[k] * normals[chart][rid][coordinate]
                                                       for k, rid in enumerate(SEED)) == 0
            if min(multipliers) < 0:
                expected_tag, numerator = 0, None
            else:
                rhs = right_hand_sides(left, right, cells)
                numerator = scale * constant - sum(multipliers[k] * rhs[rid] for k, rid in enumerate(SEED))
                expected_tag = 1 if numerator >= scale * TARGET else 2
        assert tag == expected_tag and supplied_N == numerator, ('classification_mismatch', index)
        counts[NAMES[tag]] += 1
        if tag != 1:
            remaining.append(index)
        proof_trace.update(canonical({'index': index, 'tag': tag, 'exact_N': str(numerator) if numerator is not None else None}))
        if ordinal % 256 == 0:
            check_limit(start)
    assert at == len(data), 'classification_trailing_bytes'
    return dict(counts), remaining, proof_trace.hexdigest()


def verify_metadata(result, terminal, prefix, indices_raw, data, remaining_raw, counts, remaining, cache_index):
    assert result['schema'] == 'J-one-fixed-basis-family-result-v1'
    assert result['passed'] is True and result['outcome'] == 'complete_fixed_basis_classification'
    assert result['complete_H_remaining_classified'] is True
    assert result['expected_records'] == result['committed_records'] == COUNT
    assert result['processed_in_memory'] == COUNT and result['uncommitted_records_not_accepted'] == 0
    assert result['counts'] == counts and result['seed_row_ids'] == SEED
    assert result['valid_below_target_exact_bounds_retained'] is True
    assert result['bound_fraction_convention'] == 'N/d, with d from shared chart basis'
    assert result['unresolved_records'] == len(remaining) == COUNT - counts['Lower']
    for key in ['alternate_basis_or_threshold_retries', 'optimizer_calls', 'new_FS_selected', 'kernel_or_point_queries', 'Lean_runs']:
        assert type(result[key]) is int and result[key] == 0
    assert result['new_global_actual_floor_proven'] is False and result['website_submission_ready'] is False
    assert result['inputs_sha256_start'] == result['inputs_sha256_end']
    for name, expected in result['inputs_sha256_start'].items():
        assert digest(checked_path(name)) == expected
    assert type(terminal['exit_code']) is int and terminal['exit_code'] == 0
    assert terminal['schema'] == 'J-one-child-terminal-v1'
    assert terminal['limit_stop'] is None
    assert type(terminal['child_launches']) is int and terminal['child_launches'] == 1
    assert terminal['automatic_retry'] is False
    assert terminal['result_present'] is True
    assert terminal['failure_present'] is False and terminal['inconclusive_present'] is False
    assert 0 <= terminal['seconds'] <= SECONDS
    assert 0 <= terminal['closed_output_bytes'] <= BYTES
    assert terminal['child_pid'] == result['pid']
    assert terminal['inputs_sha256_end_after_child_terminal'] == result['inputs_sha256_end']
    assert prefix['schema'] == 'J-durable-fixed-basis-prefix-v1'
    assert prefix['expected_records'] == prefix['committed_records'] == COUNT
    assert prefix['counts'] == counts and signed(prefix['target']) == TARGET
    assert prefix['committed_bytes'] == len(data) and prefix['certificate_prefix_sha256'] == sha256(data).hexdigest()
    assert prefix['committed_remaining_bytes'] == len(remaining_raw)
    assert prefix['remaining_indices_prefix_sha256'] == sha256(remaining_raw).hexdigest()
    assert prefix['input_index_sequence_sha256'] == prefix['committed_index_sequence_sha256'] == sha256(indices_raw).hexdigest()
    assert prefix['affine_cache_sha256'] == digest(PROD / 'affine-cache.jsonl')
    assert prefix['basis_sha256'] == digest(PROD / 'basis.json')
    assert prefix['unprocessed_suffix_has_no_status'] is True
    assert result['prefix_sha256'] == digest(PROD / 'prefix.json')
    expected_remaining = b''.join(struct.pack('<I', index) for index in remaining)
    assert remaining_raw == expected_remaining, 'second_stream_full_order_or_EOF_mismatch'
    assert cache_index['affine_cache_sha256'] == prefix['affine_cache_sha256']
    assert cache_index['affine_cache_bytes'] == (PROD / 'affine-cache.jsonl').stat().st_size


def run_child(args):
    start, refs, stage = time.monotonic(), {}, 'gate_identity'
    assert not any((HERE / name).exists() for name in ['started.json', 'independent-review.json', 'failure.json'])
    try:
        gate, refs, runtime = identity(args)
        save('started.json', {'pid': os.getpid(), 'time_unix': time.time(), 'attempts': 1, 'input_sha256': refs})
        stage = 'source_model_and_original_H_inputs'
        spec = importlib.util.spec_from_file_location('own_frozen_A_for_J_audit', OWN_A)
        own = importlib.util.module_from_spec(spec); spec.loader.exec_module(own)
        source = own.load_source()
        assert source['CN'] == CN and len(source['TS']) == 34 and len(source['ALL']) == 36
        cells, indices, index_raw = load_original_rows()
        result, terminal, prefix = [read(PROD / name) for name in ['result.json', 'terminal.json', 'prefix.json']]
        data = (PROD / 'classifications.bin').read_bytes()
        remaining_raw = (PROD / 'remaining-indices.u32.bin').read_bytes()
        stage = 'independent_four_chart_geometry_and_exact_basis'
        basis_package = read(PROD / 'basis.json')
        normals, basis_checks = validate_bases(source, basis_package)
        bases = basis_package['charts']
        used_charts = sorted({index % 4 for index in indices})
        singular_only = all(bases[chart]['singular'] for chart in used_charts)
        needed = {cid for index in indices for cid in divmod(index // 4, N)}
        cache_index = read(PROD / 'cache-index.json')
        assert cache_index['cells'] == sorted(needed) and cache_index['cell_count'] == len(needed)
        assert result['cache_cells'] == len(needed)
        cache = {}
        if not singular_only:
            stage = 'pointfree_independent_original_FS_and_cache_comparison'
            cache = audit_cache(own, source, cells, needed, start)
        stage = 'all_JLB2_records_full10_balance_cost_and_two_stream_EOF'
        counts, remaining, trace = classify_every_record(data, indices, cells, bases, normals, cache, start)
        verify_metadata(result, terminal, prefix, index_raw, data, remaining_raw, counts, remaining, cache_index)
        after = {name: digest(checked_path(name)) for name in refs}
        assert after == refs
        check_limit(start)
        review = {'schema': 'independent-full-JLB2-audit-v1', 'passed': True, 'pid': os.getpid(),
            'complete_original_H_input_range_audited': True, 'records': COUNT, 'counts': counts,
            'basis_checks': basis_checks, 'only_singular_charts_used': singular_only,
            'FS_cells_independently_reconstructed': len(cache),
            'original_FS_energy_replay_needed': not singular_only,
            'producer_cache_semantics_verified': not singular_only,
            'singular_only_scope': 'No affine energy conclusion is needed or claimed from the unexamined cache' if singular_only else None,
            'all_effective_N_over_d_checked_including_below_target': True,
            'all_four_chart_original155_rows_checked': True,
            'full10_balance_for_all_nonsingular_records_checked': True,
            'two_streams_complete_order_canonical_ULEB_and_EOF_checked': True,
            'independent_math_trace_sha256': trace, 'remaining_count': len(remaining),
            'input_sha256_start': refs, 'input_sha256_end': after, 'runtime': runtime,
            'seconds': time.monotonic() - start, 'producer_J_I_or_shared_core_imported': False,
            'optimizer_new_geometry_search_point_kernel_or_Lean_runs': 0,
            'new_global_floor_proven': False, 'website_submission_ready': False, 'automatic_retry_allowed': False}
        save('independent-review.json', review)
        print(json.dumps({'passed': True, 'records': COUNT, 'counts': counts,
                          'FS_cells': len(cache), 'singular_only': singular_only, 'seconds': review['seconds']}), flush=True)
    except BaseException as exc:
        save('failure.json', {'passed': False, 'stage': stage, 'error': repr(exc),
                              'traceback': traceback.format_exc(), 'input_sha256': refs,
                              'seconds': time.monotonic() - start, 'automatic_retry_allowed': False})
        raise


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--launch-authorized-once', action='store_true')
    ap.add_argument('--child-authorized-once', action='store_true')
    ap.add_argument('--gate', required=True); ap.add_argument('--gate-sha256', required=True)
    args = ap.parse_args()
    if args.child_authorized_once:
        run_child(args); return
    assert args.launch_authorized_once and not (HERE / 'launch.json').exists()
    identity(args)
    command = [sys.executable, '-B', '-X', 'utf8', str(Path(__file__)), '--child-authorized-once',
               '--gate', args.gate, '--gate-sha256', args.gate_sha256]
    save('launch.json', {'parent_pid': os.getpid(), 'command': command, 'child_launches': 1,
                         'resource_limits': {'elapsed_seconds': SECONDS, 'closed_output_bytes': BYTES}})
    start, stopped = time.monotonic(), None
    with (HERE / 'stdout.log').open('xb') as out, (HERE / 'stderr.log').open('xb') as err:
        process = subprocess.Popen(command, cwd=ROOT, stdout=out, stderr=err)
        save('child.json', {'parent_pid': os.getpid(), 'child_pid': process.pid})
        print(json.dumps({'stage': 'independent_J_audit_live', 'pid': process.pid}), flush=True)
        while process.poll() is None:
            if time.monotonic() - start > SECONDS or size() > BYTES:
                stopped = 'hard_resource_limit_inconclusive'; process.terminate(); break
            time.sleep(.2)
        code = process.wait()
    elapsed = time.monotonic() - start
    if elapsed > SECONDS or size() > BYTES:
        stopped = stopped or 'closed_resource_limit_inconclusive'
    save('terminal.json', {'exit_code': code, 'seconds': elapsed, 'child_pid': process.pid,
                           'limit_stop': stopped, 'child_launches': 1, 'closed_output_bytes': size(),
                           'automatic_retry_allowed': False})
    print(json.dumps({'terminal_exit_code': code, 'limit_stop': stopped}), flush=True)
    if code or stopped:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
