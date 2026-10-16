"""Sample existing relative encoding sizes without changing any codec or search."""
from pathlib import Path
import argparse
import hashlib
import json
import statistics
import relative_codec as codec

HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--samples', type=int, default=30)
    parser.add_argument('--files', nargs='+', default=[
        'native-tailfix-mid-0-0.json',
        'native-tailfix-mid-2-0.json',
        'native-tailfix-mid-2-1.json'])
    parser.add_argument('--output', type=Path, default=HERE / 'mid-payload-budget.json')
    args = parser.parse_args()
    rows = []
    for filename in args.files:
        raw = (HERE / filename).read_bytes()
        doc = json.loads(raw)
        leaves = [rec for rec in doc['accepted'] if 'FS' in rec['result']]
        indexes = sorted({min(len(leaves) - 1, i * len(leaves) // args.samples)
                          for i in range(args.samples)}) if leaves else []
        samples = []
        for index in indexes:
            rec = leaves[index]
            prepared = codec.prepare(rec['result'], 4)
            samples.append({'path': rec['path'], 'bytes': len(prepared['text']),
                            'bits': prepared['support_bits']})
        rows.append({'input': filename, 'input_sha256': hashlib.sha256(raw).hexdigest(),
                     'closed': not bool(doc.get('unresolved')),
                     'accepted_numeric_leaves': len(leaves), 'sample': samples,
                     'mean_payload_bytes': statistics.mean(s['bytes'] for s in samples) if samples else None})
    record = {'scope': 'Uniform-index sample budget only; no new codec and no full certificate claim.',
              'rows': rows,
              'pooled_sample_mean_bytes': statistics.mean(s['bytes'] for row in rows for s in row['sample'])}
    args.output.write_text(json.dumps(record, indent=2) + '\n', encoding='utf8')
    print(json.dumps({k: v for k, v in record.items() if k != 'rows'}), flush=True)
    for row in rows:
        print(json.dumps({k: v for k, v in row.items() if k != 'sample'}), flush=True)


if __name__ == '__main__':
    main()
