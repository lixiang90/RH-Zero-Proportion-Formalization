"""Reproduce the independent review of the 15 October finite-margin replay.

Run from the repository root:
  python scripts/review_finite_margin_20261015.py

The shared walker and numerical inequality are imported from
finite_margin_20261015.  This review adds independent reachability checks,
reconstructs the full pwD tangent-validity intervals (the numerical replay
uses only their low 96 bits), and checks every active mokI premise.  It also
checks that the candidate finite certificate differs from the archived
accepted certificate only in the two occurrences of the improved cN.
This is an exact-integer audit, not a Lean kernel-verification receipt.
"""
from __future__ import annotations

import argparse
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import time

import finite_margin_20261015 as replay


ROOT = Path(__file__).resolve().parents[1]
CORE = ROOT / "GramDefect20261015/Core.lean"
EXPECTED_SOURCE_HASH = "153e1ebfa23b5ef307dc39e36ee712d6f14d840b3b1fa5ff70b82e9dbc8dd244"
OLD_CN = 859538456469471854
NEW_CN = 859538525913875481


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def finite_block(text: str) -> str:
    begin, end = "-- SWAP BEGIN certificate", "-- SWAP END certificate"
    assert text.count(begin) == text.count(end) == 1
    return text[text.index(begin):text.index(end)]


def review() -> dict:
    assert __debug__, "Run with Python assertions enabled"
    started = time.monotonic()
    paths = {
        "accepted_source": replay.SRC,
        "candidate_core": CORE,
        "replay_script": Path(replay.__file__),
        "review_script": Path(__file__),
    }
    before = {name: sha256(path) for name, path in paths.items()}
    assert before["accepted_source"] == EXPECTED_SOURCE_HASH
    assert replay.CN == OLD_CN and replay.NEW_CN == NEW_CN

    archived = finite_block(replay.text)
    candidate = finite_block(CORE.read_text(encoding="utf8"))
    assert archived.count(str(OLD_CN)) == 2
    assert candidate.count(str(NEW_CN)) == 2
    assert archived.replace(str(OLD_CN), str(NEW_CN)) == candidate

    # Preserve the complete packed point entries.  pwD adds the point's
    # coordinate to the encoded left/right interval offsets; those high
    # fields are absent from the replay's numerical PT map.
    packed_points: dict[int, int] = {}
    duplicates = 0
    for block, entries in re.findall(r"\.lf (\d+) (\[[^\]]*\])", replay.cert):
        for offset, value in ast.literal_eval(entries):
            point = 1024 * int(block) + offset
            duplicates += point in packed_points
            packed_points[point] = value
    assert duplicates == 0 and len(packed_points) == 2993
    assert set(packed_points) == set(replay.PT)
    assert all((value & ((1 << 96) - 1)) == replay.PT[point]
               for point, value in packed_points.items())

    stats: Counter = Counter()
    old_calc, old_ydec, old_split = replay.calc, replay.ydec, replay.split

    def checked_calc(state, word):
        lower, upper = state
        stats["numeric_leaves"] += 1
        assert all(l <= u for l, u in zip(lower[:8], upper[:8]))
        for index, (i, j) in enumerate(replay.PR, 8):
            assert lower[index] >= sum(lower[i:j])
            assert upper[index] <= sum(upper[i:j])
            stats["pair_bound_invariant_checks"] += 1

        offset = 0
        for i, j, _coefficient, _pair_index in replay.TS:
            index = replay.LOOK[i, j]
            left, right = replay.term_bounds(state, i, j)
            assert (left, right) == (lower[index], upper[index])
            assert left <= right
            (kind, lam, point, other), offset = replay.dec(word, offset, left, right)
            assert 0 <= lam <= 1024
            stats["term_decode_checks"] += 1
            for weight, coordinate in zip(replay.weights(kind, lam), (point, other)):
                if not weight:
                    continue
                assert coordinate in packed_points
                packed = packed_points[coordinate]
                interval_lower = max(0, coordinate - ((packed >> 96) & ((1 << 20) - 1)))
                interval_upper = coordinate + (packed >> 116)
                # Exact original ivIn/mokI conditions after pwD expansion.
                assert 1 <= interval_upper
                assert interval_lower <= left <= coordinate <= right <= interval_upper
                stats["active_tangent_mokI_checks"] += 1
        return old_calc(state, word)

    def checked_ydec(word, offset, state):
        scan = offset
        for _ in range(42):
            if not ((word >> scan) & 1):
                break
            tag = (word >> (scan + 1)) & 31
            # The original Lean decoder terminates when tag >= 28.
            # No such tag occurs on this certificate's reachable leaves.
            assert tag < 28
            scan += 21
            stats["valid_ydec_entry_checks"] += 1
        return old_ydec(word, offset, state)

    def checked_split(state, i, j, cut, upper):
        # These inequalities ensure that the shared signed presentation of
        # the row/column update agrees with nested, saturating Nat.sub.
        assert 0 <= cut < replay.BB
        assert max(state[0]) < replay.BB
        assert max(state[1]) < replay.BB
        stats["split_nat_sub_precondition_checks"] += 1
        return old_split(state, i, j, cut, upper)

    replay.calc, replay.ydec, replay.split = checked_calc, checked_ydec, checked_split
    try:
        records = [replay.Walker(root).run() for root in range(48)]
    finally:
        replay.calc, replay.ydec, replay.split = old_calc, old_ydec, old_split

    totals = {key: sum(record[key] for record in records)
              for key in ("nodes", "leaves", "reverse", "farkas", "tightened")}
    assert totals == {"nodes": 22664, "leaves": 11356,
                      "reverse": 419, "farkas": 0, "tightened": 0}
    assert stats["numeric_leaves"] == 10937
    assert stats["active_tangent_mokI_checks"] == 173527
    minimum = min((record for record in records if record["min_margin"] is not None),
                  key=lambda record: record["min_margin"])
    margin = minimum["min_margin"]
    assert minimum["root"] == 34 and minimum["leaf"]["pos"] == 43828
    assert margin == 23301675193062482720000000000
    increment = margin // replay.SLOPE
    assert increment == NEW_CN - OLD_CN == 69444403627
    residual = margin - replay.SLOPE * increment
    one_more_deficit = replay.SLOPE * (increment + 1) - margin
    assert residual == 235234080000000000
    assert one_more_deficit == 100310240000000000

    after = {name: sha256(path) for name, path in paths.items()}
    assert before == after
    return {
        "scope": "Independent finite replay reachability and all active mokI interval premises",
        "arithmetic": "Exact Python integers; assertions enabled",
        "files": {name: str(path.relative_to(ROOT)).replace("\\", "/")
                  for name, path in paths.items()},
        "source_sha256": before,
        "source_unchanged_during_review": True,
        "candidate_finite_block_only_two_cN_substitutions": True,
        "accepted_finite_block_sha256": hashlib.sha256(archived.encode("utf8")).hexdigest(),
        "candidate_finite_block_sha256": hashlib.sha256(candidate.encode("utf8")).hexdigest(),
        "root_count": len(records),
        "walk_counts": totals,
        "additional_check_counts": dict(sorted(stats.items())),
        "point_keys": len(packed_points),
        "duplicate_point_keys": duplicates,
        "interval_errors": 0,
        "all_original_walk_end_pointers_match": True,
        "minimum_root": minimum["root"],
        "minimum_leaf_position": minimum["leaf"]["pos"],
        "minimum_original_integer_margin": margin,
        "cN_integer_slope": replay.SLOPE,
        "old_cN": OLD_CN,
        "new_cN": NEW_CN,
        "cN_increment": increment,
        "minimum_new_integer_margin": residual,
        "one_further_integer_increment_deficit": one_more_deficit,
        "all_independent_checks_passed": True,
        "lean_kernel_verified": False,
        "official_website_acceptance": False,
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
        default=ROOT / "verification/gram-defect-20261015/independent-finite-review.json")
    args = parser.parse_args()
    receipt = review()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    result = json.dumps(receipt, indent=2) + "\n"
    args.output.write_text(result, encoding="utf8", newline="\n")
    print(result, end="")


if __name__ == "__main__":
    main()
