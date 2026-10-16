"""Compress existing relative words as aligned streams and block transposes.

LZSS is the implemented pure Lean format. zlib/bz2 are potential bounds only;
their output is never treated as an accepted submission or a proof.
"""
from pathlib import Path
import argparse
import bz2
import hashlib
import json
import math
import time
import zlib
import lzss_source as lzss

HERE = Path(__file__).resolve().parent


def blocks(values, blocksize, transpose=True, xor=False):
    out = bytearray()
    for start in range(0, len(values), blocksize):
        column = values[start:start + blocksize]
        if xor:
            previous = 0
            transformed = []
            for value in column:
                transformed.append(value ^ previous)
                previous = value
            column = transformed
        width = max(1, max(column).bit_length() + 7 >> 3)
        assert width < 256
        out.append(width)
        encoded = [value.to_bytes(width, 'little') for value in column]
        if transpose:
            out.extend(row[j] for j in range(width) for row in encoded)
        else:
            for row in encoded:
                out.extend(row)
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--datasets', nargs='+', default=['ordered-0', 'ordered-2'])
    parser.add_argument('--output', type=Path, default=HERE / 'relative-stream-budget.json')
    args = parser.parse_args()
    supports, trees, hashes = [], [], {}
    old_text_bytes = 0
    for stem in args.datasets:
        raw = (HERE / (stem + '-compact.json')).read_bytes()
        doc = json.loads(raw)
        hashes[stem] = hashlib.sha256(raw).hexdigest()
        for rec in doc['leaves']:
            if rec['kind'] != 'numeric':
                continue
            supports.append(int(rec['support_hex'], 16))
            trees.append(rec['tree_code'])
            old_text_bytes += len(rec['text'])
    masks = [value & ((1 << 39) - 1) for value in supports]
    params = [value >> 39 for value in supports]
    results = []
    layouts = [
        ('aligned', lambda: blocks(supports, 32, False) + blocks(trees, 32, False)),
        ('split_aligned', lambda: blocks(masks, 32, False) + blocks(params, 32, False) + blocks(trees, 32, False)),
        ('transpose32', lambda: blocks(supports, 32) + blocks(trees, 32)),
        ('transpose128', lambda: blocks(supports, 128) + blocks(trees, 128)),
        ('split_transpose32', lambda: blocks(masks, 32) + blocks(params, 32) + blocks(trees, 32)),
        ('split_transpose128', lambda: blocks(masks, 128) + blocks(params, 128) + blocks(trees, 128)),
        ('xor32', lambda: blocks(supports, 32, False, True) + blocks(trees, 32, False, True)),
        ('split_xor32', lambda: blocks(masks, 32, False, True) + blocks(params, 32, False, True) + blocks(trees, 32, False, True)),
        ('split_xor_transpose32', lambda: blocks(masks, 32, True, True) + blocks(params, 32, True, True) + blocks(trees, 32, True, True)),
    ]
    for layout, make in layouts:
        raw = bytes(make())
        row = {'layout': layout, 'raw_bytes': len(raw), 'compressors': {}}
        for name, compress, decompress in [
                ('lzss', lzss.compress, lambda value: lzss.decompress(value, len(raw))),
                ('zlib9', lambda value: zlib.compress(value, 9), zlib.decompress),
                ('bz2', lambda value: bz2.compress(value, 9), bz2.decompress)]:
            started = time.monotonic()
            packed = compress(raw)
            assert decompress(packed) == raw
            estimate = math.ceil(8 * len(packed) / math.log2(92))
            row['compressors'][name] = {'bytes': len(packed),
                'base92_bytes_estimate': estimate,
                'source_saving_vs_old_estimate': old_text_bytes - estimate,
                'seconds': time.monotonic() - started, 'roundtrip_passed': True}
            (HERE / ('relative-' + layout + '.' + name)).write_bytes(packed)
        (HERE / ('relative-' + layout + '.bin')).write_bytes(raw)
        results.append(row)
        record = {'scope': 'Full low/high existing relative stream budget; zlib/bz2 are bounds without a Lean decoder.',
                  'input_sha256': hashes, 'leaves': len(supports),
                  'old_text_bytes': old_text_bytes, 'results': results}
        args.output.write_text(json.dumps(record, indent=2) + '\n', encoding='utf8')
        print(json.dumps(row), flush=True)


if __name__ == '__main__':
    main()
