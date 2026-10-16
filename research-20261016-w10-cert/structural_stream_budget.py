"""Measure LZSS on aligned term/field streams instead of mixed base92 leaves.

Research budget only. It emits no claimed proof and changes no live data.
"""
from pathlib import Path
import argparse
import hashlib
import json
import time
import relative_codec as codec
import lzss_source as lzss

HERE = Path(__file__).resolve().parent


def packed_bits(values, bits):
    output = bytearray()
    word = count = 0
    for value in values:
        assert 0 <= value < 1 << bits
        word |= value << count
        count += bits
        while count >= 8:
            output.append(word & 255)
            word >>= 8
            count -= 8
    if count:
        output.append(word)
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--datasets', nargs='+', default=['ordered-0', 'ordered-2'])
    parser.add_argument('--output', type=Path, default=HERE / 'structural-stream-budget.json')
    parser.add_argument('--layouts', nargs='+', default=['leaf40', 'term40', 'term_fields16', 'term_sparse16', 'term_fields_bits'])
    args = parser.parse_args()
    leaves, trees = [], []
    hashes = {}
    for stem in args.datasets:
        raw = (HERE / (stem + '.json')).read_bytes()
        original = json.loads(raw)
        packed_raw = (HERE / (stem + '-compact.json')).read_bytes()
        packed = json.loads(packed_raw)
        hashes[stem] = [hashlib.sha256(raw).hexdigest(), hashlib.sha256(packed_raw).hexdigest()]
        assert packed['receipt']['input_sha256'] == hashes[stem][0]
        bounds = {a['path']: a['result']['certificate'] for a in original['accepted']}
        del raw, original, packed_raw
        for rec in packed['leaves']:
            if rec['kind'] != 'numeric':
                continue
            cell = bounds[rec['path']]
            fs = codec.unpack_relative(int(rec['support_hex'], 16), cell['lower_bounds'], cell['upper_bounds'])
            assert all(p % 32 == 0 and r % 32 == 0 for _, _, p, r in fs)
            leaves.append([(k, m, p//32, r//32) for k, m, p, r in fs])
            trees.append(rec['tree_code'])
        del bounds, packed
    n = len(leaves)
    columns = [[leaf[t] for leaf in leaves] for t in range(39)]
    results = []
    for layout in args.layouts:
        started = time.monotonic()
        raw = bytearray()
        if layout in ('leaf40', 'term40'):
            iterator = (term for leaf in leaves for term in leaf) if layout == 'leaf40' else (term for column in columns for term in column)
            for k, m, p, r in iterator:
                raw.extend((k | m << 2 | p << 12 | r << 26).to_bytes(5, 'little'))
        elif layout == 'term_fields16':
            for column in columns:
                for field in range(4):
                    for values in column:
                        raw.extend(values[field].to_bytes(1 if field == 0 else 2, 'little'))
        elif layout == 'term_sparse16':
            for column in columns:
                raw.extend(packed_bits((k for k, m, p, r in column), 2))
                for k, m, p, r in column:
                    if k >= 2:
                        raw.extend(m.to_bytes(2, 'little'))
                for k, m, p, r in column:
                    if k:
                        raw.extend(p.to_bytes(2, 'little'))
                for k, m, p, r in column:
                    if k == 3:
                        raw.extend(r.to_bytes(2, 'little'))
        elif layout == 'term_fields_bits':
            for column in columns:
                for field, width in enumerate([2, 10, 14, 14]):
                    raw.extend(packed_bits((values[field] for values in column), width))
        else:
            raise ValueError(layout)
        tree_start = len(raw)
        for digit in range(8):
            raw.extend(packed_bits(((code // (10**digit)) % 10 for code in trees), 4))
        raw = bytes(raw)
        compressed = lzss.compress(raw)
        assert lzss.decompress(compressed, len(raw)) == raw
        chunked_text_bytes = sum(len(codec.text_encode(int.from_bytes(compressed[i:i+256], 'little')))
                                 for i in range(0, len(compressed), 256))
        info = {'layout': layout, 'leaves': n, 'raw_bytes': len(raw), 'FS_raw_bytes': tree_start,
                'compressed_bytes': len(compressed), 'base92_bytes': chunked_text_bytes,
                'base92_bytes_per_leaf': chunked_text_bytes / n,
                'roundtrip_passed': True, 'seconds': time.monotonic() - started}
        results.append(info)
        receipt = {'scope': 'Compression budget and byte roundtrip only; no Lean decoder or proof claim.',
                   'input_sha256': hashes, 'results': results}
        args.output.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf8')
        (HERE / ('stream-' + layout + '.bin')).write_bytes(raw)
        (HERE / ('stream-' + layout + '.lzss')).write_bytes(compressed)
        print(json.dumps(info), flush=True)


if __name__ == '__main__':
    main()
