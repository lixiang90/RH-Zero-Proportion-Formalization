"""Predict the unchanged first anchors from a tree plus nine flow orientations.

Only existing exact witnesses are encoded. No anchor, mixture, coefficient,
floor or cell is changed. Predicted potentials need not be feasible: a missed
prediction falls back to the old relative integer, and FS roundtrip is checked.
"""
from pathlib import Path
import argparse
import collections
import hashlib
import json
import time
import relative_codec as codec

HERE = Path(__file__).resolve().parent
OFFSETS = [0, -32, 32, -64, 64, -256, 256]


def orientations(fs, code):
    edges = codec.tree.decode(code)
    div = codec.tree.divergence(fs)
    flags = zero = 0
    for index, (a, b) in enumerate(edges):
        seen = {a}
        for _ in range(9):
            for i, j in edges:
                if (i, j) == (a, b):
                    continue
                if i in seen or j in seen:
                    seen.update((i, j))
        assert b not in seen
        signed = sum(div[v] for v in seen)
        flags |= int(signed > 0) << index
        zero += signed == 0
    return flags, zero


def potentials(code, flags, lo, hi):
    edges = codec.tree.decode(code)
    values = [None] * 10
    values[0] = 0
    for _ in range(9):
        for index, (a, b) in enumerate(edges):
            axis = codec.thin.g.LOOK[a, b]
            length = hi[axis] if flags >> index & 1 else lo[axis]
            if values[a] is not None:
                if values[b] is None:
                    values[b] = values[a] + length
                else:
                    assert values[b] == values[a] + length
            elif values[b] is not None:
                values[a] = values[b] - length
    assert None not in values
    return values


def pack(fs, code, flags, lo, hi, clamped=False, small_raw=False):
    potential = potentials(code, flags, lo, hi)
    mask = sum((k != 0) << t for t, (k, m, p, r) in enumerate(fs))
    word = flags | mask << 9
    offset = 48
    counts = collections.Counter()
    counts['potential_feasible_leaves'] = int(all(
        lo[z] <= potential[j] - potential[i] <= hi[z]
        for z, (i, j) in enumerate(codec.thin.g.ALL)))

    def put(value, bits):
        nonlocal word, offset
        assert 0 <= value < 1 << bits, (value, bits)
        word |= value << offset
        offset += bits

    def geometry(t):
        i, j, _ = codec.thin.g.TERMS[t]
        axis = codec.thin.g.LOOK[i, j]
        base = (lo[axis] + 31) // 32
        count = max(0, hi[axis] // 32 - base)
        pred = ((potential[j] - potential[i] + 16) // 32) * 32
        if clamped:
            pred = min(max(pred, 32 * base), 32 * (base + count))
        return base, count.bit_length(), pred

    for t, (k, m, p, r) in enumerate(fs):
        if k == 0:
            continue
        if k == 1:
            put(0, 1)
        else:
            put(1, 1)
            put(k - 2, 1)
            put(m, 10)
        base, bits, pred = geometry(t)
        delta = p - pred
        counts['active'] += 1
        counts['old_first_anchor_bits'] += bits
        counts['delta_' + str(delta)] += 1
        if small_raw and bits <= 3:
            put(p // 32 - base, bits)
            counts['small_raw'] += 1
            counts['new_first_anchor_bits'] += bits
        elif delta in OFFSETS:
            put(OFFSETS.index(delta), 3)
            counts['hit'] += 1
            counts['new_first_anchor_bits'] += 3
        else:
            put(7, 3)
            put(p // 32 - base, bits)
            counts['fallback'] += 1
            counts['new_first_anchor_bits'] += 3 + bits
        if k == 3:
            delta2 = r - p
            if delta2 in (-32, 32, -256):
                put((-32, 32, -256).index(delta2), 2)
            else:
                put(3, 2)
                put(r // 32 - base, bits)
    return word, offset, counts


def unpack(word, code, lo, hi, clamped=False, small_raw=False):
    flags = word & 511
    word >>= 9
    mask = word & ((1 << 39) - 1)
    word >>= 39
    potential = potentials(code, flags, lo, hi)

    def get(bits):
        nonlocal word
        value = word & ((1 << bits) - 1)
        word >>= bits
        return value

    fs = []
    for t in range(39):
        if not (mask >> t & 1):
            fs.append([0, 0, 0, 0])
            continue
        if get(1) == 0:
            k, m = 1, 0
        else:
            k, m = 2 + get(1), get(10)
        i, j, _ = codec.thin.g.TERMS[t]
        axis = codec.thin.g.LOOK[i, j]
        base = (lo[axis] + 31) // 32
        count = max(0, hi[axis] // 32 - base)
        bits = count.bit_length()
        pred = ((potential[j] - potential[i] + 16) // 32) * 32
        if clamped:
            pred = min(max(pred, 32 * base), 32 * (base + count))
        if small_raw and bits <= 3:
            p = 32 * (base + get(bits))
        else:
            tag = get(3)
            p = pred + OFFSETS[tag] if tag < 7 else 32 * (base + get(bits))
        r = 0
        if k == 3:
            tag = get(2)
            r = p + (-32, 32, -256)[tag] if tag < 3 else 32 * (base + get(bits))
        fs.append([k, m, p, r])
    return fs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--samples', type=int, default=30)
    parser.add_argument('--files', nargs='+', default=['ordered-0.json', 'ordered-2.json', 'native-tailfix-mid-0-0.json'])
    parser.add_argument('--output', type=Path, default=HERE / 'flow-primal-probe.json')
    args = parser.parse_args()
    started = time.monotonic()
    all_rows = []
    for filename in args.files:
        raw = (HERE / filename).read_bytes()
        doc = json.loads(raw)
        leaves = [a for a in doc['accepted'] if 'FS' in a['result']]
        indexes = sorted({min(len(leaves)-1, i*len(leaves)//args.samples) for i in range(args.samples)})
        prepared = []
        for index in indexes:
            rec = leaves[index]
            data = codec.prepare(rec['result'], 4)
            cert = rec['result']['certificate']
            flags, zero = orientations(data['FS'], data['tree_code'])
            prepared.append((rec['path'], data, cert['lower_bounds'], cert['upper_bounds'], flags, zero))
        variants = []
        for clamped in [False, True]:
            for small_raw in [False, True]:
                totals = collections.Counter()
                samples = []
                for path, data, lo, hi, flags, zero in prepared:
                    support, bits, counts = pack(data['FS'], data['tree_code'], flags, lo, hi, clamped, small_raw)
                    assert unpack(support, data['tree_code'], lo, hi, clamped, small_raw) == data['FS']
                    new_word = support * 10**8 + data['tree_code']
                    old_word = int(data['support_hex'], 16) * 10**8 + data['tree_code']
                    mixed_word = 1 + 2 * new_word if bits < data['support_bits'] else 2 * old_word
                    new_bytes = len(codec.text_encode(new_word))
                    mixed_bytes = len(codec.text_encode(mixed_word))
                    totals.update(counts)
                    totals['old_bits'] += data['support_bits']
                    totals['new_bits'] += bits
                    totals['mixed_bits'] += 1 + min(bits, data['support_bits'])
                    totals['old_bytes'] += len(data['text'])
                    totals['new_bytes'] += new_bytes
                    totals['mixed_bytes'] += mixed_bytes
                    totals['zero_edges'] += zero
                    totals['mixed_uses_prediction'] += bits < data['support_bits']
                    samples.append({'path': path, 'orientation': flags, 'old_bits': data['support_bits'],
                                    'new_bits': bits, 'zero_edges': zero})
                variants.append({'clamped': clamped, 'small_raw': small_raw,
                                 'totals': dict(totals), 'samples': samples})
        row = {'input': filename, 'input_sha256': hashlib.sha256(raw).hexdigest(),
               'samples': len(prepared), 'closed': not bool(doc.get('unresolved')), 'variants': variants}
        all_rows.append(row)
        record = {'scope': '90-leaf existing tree/orientation predictor encoding only; anchors and exact witnesses unchanged.',
                  'orientation_bits_per_prediction_leaf': 9, 'offsets': OFFSETS,
                  'rows': all_rows, 'seconds': time.monotonic() - started,
                  'all_FS_roundtrips_passed': True, 'lean_proof_claim': False}
        args.output.write_text(json.dumps(record, indent=2) + '\n', encoding='utf8')
        for variant in variants:
            printable = {key: value for key, value in variant['totals'].items() if not key.startswith('delta_')}
            print(json.dumps({'input': filename, 'clamped': variant['clamped'],
                              'small_raw': variant['small_raw'], 'totals': printable}), flush=True)


if __name__ == '__main__':
    main()
