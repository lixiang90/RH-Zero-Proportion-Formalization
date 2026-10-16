"""Try each sparse support change with a newly optimized exact dual.

This is a small certificate-search experiment. Frozen mathematical parameters
and the target stay unchanged, and every accepted candidate is replayed by the
existing exact integer formula. No global coverage claim is made.
"""
from pathlib import Path
import argparse
import hashlib
import json
import time
import relative_codec as codec

HERE = Path(__file__).resolve().parent


def probe(rec):
    original = codec.prepare(rec, 4)
    fs = original['FS']
    lo, hi = rec['certificate']['lower_bounds'], rec['certificate']['upper_bounds']
    changes = []
    attempts = 0
    dual = codec.tree.recompute(fs, lo, hi)
    for round in range(2):
        changed = False
        for t in sorted(range(39), key=lambda t: codec.thin.g.TERMS[t][2]):
            k, m, p, r = fs[t]
            if not k:
                continue
            candidates = [[0, 0, 0, 0]]
            if k >= 2:
                candidates.append([1, 0, p, 0])
                if k == 3:
                    candidates.append([1, 0, r, 0])
            for replacement in candidates:
                candidate = [list(term) for term in fs]
                candidate[t] = replacement
                attempts += 1
                try:
                    recomputed = codec.tree.recompute(candidate, lo, hi)
                except AssertionError:
                    continue
                assert int(recomputed['after_numerator']) >= codec.thin.THRESH
                changes.append({'term': t, 'from': fs[t], 'to': replacement, 'round': round})
                fs, dual = candidate, recomputed
                changed = True
                break
        if not changed:
            break
    support, bits = codec.pack_relative(fs, lo, hi)
    assert codec.unpack_relative(support, lo, hi) == fs
    payload = codec.text_encode(support * 10**8 + dual['tree_code'])
    return {'old_bytes': len(original['text']), 'new_bytes': len(payload),
            'old_bits': original['support_bits'], 'new_bits': bits,
            'changes': changes, 'attempts': attempts,
            'after_numerator': dual['after_numerator']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--samples', type=int, default=30)
    parser.add_argument('--files', nargs='+', default=['ordered-0.json', 'ordered-2.json', 'native-tailfix-mid-0-0.json'])
    parser.add_argument('--output', type=Path, default=HERE / 'reflow-thin-probe.json')
    args = parser.parse_args()
    rows = []
    started = time.monotonic()
    for filename in args.files:
        raw = (HERE / filename).read_bytes()
        doc = json.loads(raw)
        leaves = [a for a in doc['accepted'] if 'FS' in a['result']]
        indexes = sorted({min(len(leaves)-1, i*len(leaves)//args.samples) for i in range(args.samples)})
        samples = []
        for index in indexes:
            a = leaves[index]
            samples.append({'path': a['path'], **probe(a['result'])})
        row = {'input': filename, 'input_sha256': hashlib.sha256(raw).hexdigest(),
               'closed': not bool(doc.get('unresolved')), 'samples': samples,
               'old_bytes': sum(a['old_bytes'] for a in samples),
               'new_bytes': sum(a['new_bytes'] for a in samples),
               'accepted_changes': sum(len(a['changes']) for a in samples)}
        rows.append(row)
        record = {'scope': 'Small exact witness thinning experiment; no changed parameters or global floor.',
                  'seconds': time.monotonic() - started, 'rows': rows}
        args.output.write_text(json.dumps(record, indent=2) + '\n', encoding='utf8')
        print(json.dumps({k: v for k, v in row.items() if k != 'samples'}), flush=True)


if __name__ == '__main__':
    main()
