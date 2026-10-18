"""Post-terminal byte-only selector export interface; not called by producer.

No FS, curvature, matrix or optimization imports. This is data text only and
requires a separate byte-only authorization; no Lean reconstructor is claimed.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import gzip
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

def canonical(x): return json.dumps(x, sort_keys=True, separators=(',', ':'), allow_nan=False).encode('ascii') + b'\n'
def member(desc):
    with (ROOT / desc['path']).open('rb') as handle: handle.seek(desc['offset']); data = handle.read(desc['bytes'])
    assert len(data) == desc['bytes'] and sha256(data).hexdigest() == desc['compressed_member_sha256']
    raw = gzip.decompress(data); assert sha256(raw).hexdigest() == desc['decoded_sha256']
    value = json.loads(raw); assert canonical(value) == raw; return value
def ns(xs): return '[' + ','.join(str(x) for x in xs) + ']'
def main():
    ap = argparse.ArgumentParser(description=__doc__); ap.add_argument('--export-authorized-terminal-bytes-only', action='store_true')
    args = ap.parse_args(); assert args.export_authorized_terminal_bytes_only
    assert (HERE / 'terminal.json').exists() and not (HERE / 'SelectorData.lean').exists()
    header = ('-- Selector data only. Generic reconstruction and proof consumer not implemented.\nimport Mathlib\n'
        'namespace PSelectorData\ndef cases : List (Nat × Nat × List Nat × List Nat × List Nat × List (Nat × Nat)) := [\n')
    codes = {'Lower': 0, 'deduction_Lower': 1, 'curvature_Lower': 2}
    data = bytearray(header.encode('utf-8')); head = '0' * 64; count = 0; lines = 0
    with (HERE / 'progress-commits.jsonl').open('rb') as handle:
        for line in handle:
            if not line.endswith(b'\n'): break
            envelope = json.loads(line); body = envelope['body']
            assert body['previous_commit_sha256'] == head
            head = sha256(canonical(body)).hexdigest(); assert head == envelope['commit_sha256']
            count += 1; assert body['ordinal'] == count
            if body['outcome'] == 'unresolved': assert body['selector_record'] is None; continue
            value = member(body['selector_record']); assert value['G_index'] == body['G_index']
            fields = [str(value['G_index']), str(codes[body['outcome']]), ns(value.get('group_base_row_IDs', [])),
                ns(value.get('normalized_unknown_row_IDs', [])), ns(value.get('positive_anchor_row_IDs', [])),
                '[' + ','.join('(' + str(a) + ',' + str(b) + ')' for a, b in value.get('original_REG_selectors', [])) + ']']
            data.extend(('  (' + ','.join(fields) + '),\n').encode('utf-8')); lines += 1
    data.extend(b']\nend PSelectorData\n')
    path = HERE / 'SelectorData.lean'
    with path.open('xb') as handle: handle.write(data)
    receipt = {'schema': 'P-terminal-fixed-selector-source-byte-inventory-v1', 'source_bytes': len(data),
        'source_sha256': sha256(data).hexdigest(), 'committed_records': count, 'selector_rows': lines,
        'raw_mu_m_pstar_and_denominators_not_stored': True, 'deterministic_Lean_reconstructor_implemented': False,
        'generic_source_import_baseline_and_runtime_not_counted': True, 'Lean_or_mathematical_runs': 0,
        'merged_submission_budget_or_acceptance_proven': False}
    with (HERE / 'delivery-inventory.json').open('x', encoding='utf-8', newline='\n') as handle:
        json.dump(receipt, handle, indent=2); handle.write('\n')
    print(json.dumps(receipt))

if __name__ == '__main__': main()
