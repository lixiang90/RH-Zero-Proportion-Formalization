"""Exact shape-dictionary budget using unchanged relative points and mixtures.

This experiment does not alter search data, coefficients, tangent certificates,
or the checker.  Full kind words are dictionaries of 39 base-four digits.
"""
from pathlib import Path
import argparse
import collections
import hashlib
import json
import math
import time
import relative_codec as codec

HERE = Path(__file__).resolve().parent


def pack_data(fs, lo, hi):
    value = offset = 0

    def put(number, bits):
        nonlocal value, offset
        assert 0 <= number < 1 << bits
        value |= number << offset
        offset += bits

    def point(t, p):
        i, j, _ = codec.thin.g.TERMS[t]
        z = codec.thin.g.LOOK[i, j]
        base = (lo[z] + 31) // 32
        count = max(0, hi[z] // 32 - base)
        assert p % 32 == 0
        put(p // 32 - base, count.bit_length())

    for t, (k, m, p, r) in enumerate(fs):
        if not k:
            continue
        if k != 1:
            put(m, 10)
        point(t, p)
        if k == 3:
            delta = r - p
            if delta in (-32, 32, -256):
                put((-32, 32, -256).index(delta), 2)
            else:
                put(3, 2)
                point(t, r)
    return value, offset


def unpack_data(shape, value, lo, hi):
    def get(bits):
        nonlocal value
        number = value % (1 << bits)
        value >>= bits
        return number

    def point(t):
        i, j, _ = codec.thin.g.TERMS[t]
        z = codec.thin.g.LOOK[i, j]
        base = (lo[z] + 31) // 32
        count = max(0, hi[z] // 32 - base)
        return 32 * (base + get(count.bit_length()))

    fs = []
    for t in range(39):
        k = shape >> (2 * t) & 3
        m = p = r = 0
        if k:
            if k != 1:
                m = get(10)
            p = point(t)
            if k == 3:
                tag = get(2)
                r = p + (-32, 32, -256)[tag] if tag < 3 else point(t)
        fs.append([k, m, p, r])
    return fs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--datasets', nargs='+', default=['ordered-0', 'ordered-2'])
    parser.add_argument('--output', type=Path, default=HERE / 'kind-shape-dictionary-budget.json')
    parser.add_argument('--payload-output', type=Path)
    args = parser.parse_args()
    started = time.monotonic()
    leaves = []
    hashes = {}
    for stem in args.datasets:
        original_path = HERE / (stem + '.json')
        compact_path = HERE / (stem + '-compact.json')
        original_raw = original_path.read_bytes()
        original = json.loads(original_raw)
        compact_raw = compact_path.read_bytes()
        packed = json.loads(compact_raw)
        hashes[original_path.name] = hashlib.sha256(original_raw).hexdigest()
        hashes[compact_path.name] = hashlib.sha256(compact_raw).hexdigest()
        assert not original.get('unresolved')
        assert packed['receipt']['input_sha256'] == hashes[original_path.name]
        bounds = {a['path']: a['result']['certificate'] for a in original['accepted']}
        del original, original_raw
        for rec in packed['leaves']:
            if rec['kind'] != 'numeric':
                continue
            cell = bounds[rec['path']]
            lo, hi = cell['lower_bounds'], cell['upper_bounds']
            support = int(rec['support_hex'], 16)
            fs = codec.unpack_relative(support, lo, hi)
            shape = sum(k << (2 * t) for t, (k, _, _, _) in enumerate(fs))
            mask = support & ((1 << 39) - 1)
            data, data_bits = pack_data(fs, lo, hi)
            assert unpack_data(shape, data, lo, hi) == fs
            shape_bits = 39 + sum(1 + (k > 1) for k, _, _, _ in fs if k)
            leaves.append({'path': rec['path'], 'shape': shape, 'mask': mask,
                           'tree_code': rec['tree_code'], 'data': data,
                           'data_bits': data_bits, 'old_shape_bits': shape_bits,
                           'old_text_bytes': len(rec['text'])})
        del bounds, packed, compact_raw
    shape_counts = collections.Counter(a['shape'] for a in leaves)
    mask_counts = collections.Counter(a['mask'] for a in leaves)
    shape_table = [shape for shape, _ in shape_counts.most_common()]
    shape_lookup = {shape: i for i, shape in enumerate(shape_table)}
    index_bits = (len(shape_table) - 1).bit_length()
    old_shape_bits = sum(a['old_shape_bits'] for a in leaves)
    shape_dictionary_bits = len(shape_table) * 78
    new_leaf_bits = index_bits * len(leaves)
    total_payload_bytes = 0
    for a in leaves:
        word = shape_lookup[a['shape']] + (a['tree_code'] << index_bits) + (a['data'] << (index_bits + 27))
        a['word_hex'] = hex(word)
        total_payload_bytes += len(codec.text_encode(word))
    old_bytes = sum(a['old_text_bytes'] for a in leaves)
    record = {'scope': 'Exact kind-shape dictionary encoding and FS roundtrip, no Lean or global-floor claim.',
              'input_sha256': hashes, 'leaves': len(leaves),
              'distinct_full_shapes': len(shape_table), 'distinct_presence_masks': len(mask_counts),
              'shape_index_bits': index_bits,
              'old_shape_bits': old_shape_bits,
              'shape_dictionary_bits': shape_dictionary_bits,
              'new_shape_index_bits': new_leaf_bits,
              'net_shape_saving_bits': old_shape_bits - shape_dictionary_bits - new_leaf_bits,
              'old_payload_text_bytes': old_bytes,
              'new_payload_text_bytes': total_payload_bytes,
              'shape_table_base92_bytes_ceiling': math.ceil(shape_dictionary_bits / math.log2(92)),
              'seconds': time.monotonic() - started,
              'top_shapes': [(hex(s), count) for s, count in shape_counts.most_common(20)]}
    args.output.write_text(json.dumps(record, indent=2) + '\n', encoding='utf8')
    if args.payload_output:
        args.payload_output.write_text(json.dumps({'receipt': record,
            'shapes_hex': [hex(s) for s in shape_table], 'leaves': leaves}, separators=(',', ':')) + '\n', encoding='utf8')
    print(json.dumps({k: v for k, v in record.items() if k not in ('input_sha256', 'top_shapes')}), flush=True)


if __name__ == '__main__':
    main()
