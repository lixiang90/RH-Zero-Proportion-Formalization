"""Read-only proof-strategy diagnostic for the frozen nine-point duals.

No data, weights, multipliers, target or mathematical claim is generated.
The weaker adjacent primitive box is compared with the existing target; failed
cases continue to require the original Floyd box. This is not a kernel proof.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import time
import am_expanded_nine_point_certificate as expanded

ROOT = Path(__file__).resolve().parents[1]

def canonical_sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n").replace(b"\r", b"\n")).hexdigest()

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('tmp/verification/primitive-gap-box-diagnostic.json'))
    args = parser.parse_args()
    output = (ROOT / args.output).resolve()
    if not output.is_relative_to(ROOT):
        parser.error('Output must stay inside this repository')
    data = ROOT / 'output/am-expanded-nine-point-certificate.json'
    report = json.loads(data.read_text(encoding='utf-8'))
    assert report['target_numerator'] == expanded.TARGET == 805260
    assert report['strong_target_numerator'] == expanded.STRONG == 805803
    assert expanded.epi.sha(Path(expanded.__file__).read_bytes()) == report['script_canonical_lf_sha256']
    for name, expected in report['dependency_pins'].items():
        assert canonical_sha(ROOT / name) == expected, name
    files = [data, Path(__file__).resolve(), Path(expanded.__file__), Path(expanded.epi.__file__), Path(expanded.epi.old.__file__)]
    inputs = {path.relative_to(ROOT).as_posix(): canonical_sha(path) for path in files}
    cells = report['captured_cells'] + [expanded.epi.reflected(cell) for cell in report['captured_cells']]
    constraints = [expanded.epi.old.constraints(cell) for cell in cells]
    catalog = {point: (word, list_id) for point, word, list_id in report['point_catalog']}
    target = Q(expanded.TARGET, expanded.SA)
    failures = []
    minimum = None
    maximum_loss = Q(0)
    start = time.monotonic()
    for index, item in enumerate(report['pairs']):
        a, b = item['left'], item['right']
        objective, matrix, rhs, original_box = expanded.problem(cells[a], cells[b], item['extra_points'], catalog, report['region'])
        primitive = []
        for i in range(8):
            bounds = []
            if i < 7:
                bounds.append(constraints[a][i, i + 1])
            if i > 0:
                bounds.append(constraints[b][i - 1, i])
            lo = max(Q(4, 5), *(Q(lo, 5 * expanded.SC) for lo, hi in bounds))
            hi = min(Q(hi, 5 * expanded.SC) for lo, hi in bounds)
            assert lo <= hi
            primitive.append((lo, hi))
        lower = expanded.dual_lower(objective, matrix, rhs, primitive + original_box[8:], item['dual_sparse'])
        assert lower <= Q(item['lower'])
        loss = Q(item['lower']) - lower
        maximum_loss = max(maximum_loss, loss)
        minimum = lower if minimum is None else min(minimum, lower)
        if lower < target:
            failures.append({'pair_index': index, 'left': a, 'right': b})
    unchanged = all(canonical_sha(ROOT / name) == expected for name, expected in inputs.items())
    assert unchanged
    record = {
        'status': 'read_only_diagnostic_complete',
        'input_sha256': inputs,
        'inputs_unchanged': unchanged,
        'pairs_compared': len(report['pairs']),
        'primitive_box_at_target': len(report['pairs']) - len(failures),
        'original_floyd_box_still_needed': len(failures),
        'failed_pairs': failures,
        'primitive_minimum': str(minimum),
        'maximum_loss_against_original_box': str(maximum_loss),
        'target': str(target),
        'elapsed_seconds': round(time.monotonic() - start, 3),
        'scope': 'Exact Python comparison of the same frozen duals with a weaker primitive adjacent-gap box. This only identifies a potential faster proof strategy; it does not modify the original certificate, lower values, theorem or target. Failed cases still need the original full box.',
        'kernel_verified': False,
        'whole_submission_verified': False,
        'submitted': False,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8', newline='\n')
    print(json.dumps({key: value for key, value in record.items() if key not in ('failed_pairs', 'input_sha256')}, indent=2))

if __name__ == '__main__':
    main()
