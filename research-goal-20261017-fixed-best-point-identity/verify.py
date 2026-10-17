"""Read-only identity audit for ONE already selected actual24 sample.

No producer import, pressure/kernel/Phi evaluation, optimizer, enumeration,
or point rounding. --write-receipt creates an absent receipt only.
"""
from pathlib import Path
from fractions import Fraction
from hashlib import sha256
import argparse
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
RECEIPT = HERE / 'identity-replay.json'

CHALLENGE = 'research-20261016-followup/window_reweight_challenge.json'
SUPPORT = 'research-goal-20261017-ternary-coboundary/support-audit.json'
PARAM = 'research-20261016-followup/window_reweight_rational.json'
PROFILE = 'research-20261016-followup/window_profile_24.json'
EXPECTED = {
    CHALLENGE: '4d79a1c05aba683d9971755eb7bad6b109d042abad359c74e43cc1403b3f903b',
    SUPPORT: '3d7fc73a21b5f8e8294be0eeb40881a08072412568dd684f7bed785fe1dc24db',
    PARAM: '61ad18366b0234d75c4204bc661446c94f1705c29c3e6041bed0147dd6476f11',
    PROFILE: 'e15c69876922001f0d79f3e37f5121f2ed271eb6e9f59fbf8e49a2bc26037b93',
}


def raw_input(name):
    raw = (ROOT / name).read_bytes()
    assert sha256(raw).hexdigest() == EXPECTED[name], name
    return json.loads(raw)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write-receipt', action='store_true')
    args = ap.parse_args()
    if args.write_receipt:
        assert not RECEIPT.exists(), 'refuse to overwrite frozen receipt'
    source_start = sha256(Path(__file__).read_bytes()).hexdigest()
    challenge, support, params, profile = [raw_input(p) for p in
                                          [CHALLENGE, SUPPORT, PARAM, PROFILE]]
    assert all(isinstance(d, dict) for d in [challenge, support, params, profile])
    floats = challenge['best_gaps']
    precise = support['zeroV_minimum_sample_exact_binary_float_gaps']
    assert isinstance(floats, list) and len(floats) == 9
    assert isinstance(precise, list) and len(precise) == 9
    assert all(isinstance(v, float) for v in floats)
    assert all(isinstance(v, str) for v in precise)
    assert all(Fraction(q) == Fraction.from_float(x)
               for q, x in zip(precise, floats))
    assert support['zeroV_minimum_sample_float_gaps'] == floats
    assert support['source'] == CHALLENGE + ':best_gaps'
    assert support['zeroV_minimum_sample_row'] == 69
    assert support['actual_scalar_upper_bounds_proven'] is False
    assert challenge['ledger_sha256'] == EXPECTED[PARAM]
    assert challenge['source_sha256'] == EXPECTED[PROFILE]
    nums = challenge['coefficient_numerators_1e9']
    assert isinstance(nums, list) and len(nums) == 24
    assert nums == params['window_coefficient_numerators_1e9']
    assert nums == profile['final_window_coefficient_numerators_1e9']
    for path in EXPECTED:
        raw_input(path)
    source_end = sha256(Path(__file__).read_bytes()).hexdigest()
    assert source_start == source_end
    out = {
        'schema': 'one-fixed-existing-best-point-identity-v1',
        'passed': True,
        'scope': __doc__,
        'script_sha256_start': source_start,
        'script_sha256_end': source_end,
        'input_sha256_start': EXPECTED,
        'input_sha256_end': EXPECTED,
        'all_inputs_unchanged': True,
        'fixed_point': {
            'path': SUPPORT,
            'sha256': EXPECTED[SUPPORT],
            'top_level_type': 'dict',
            'field': 'zeroV_minimum_sample_exact_binary_float_gaps',
            'field_type': 'list[str]',
            'length': 9,
            'element_semantics': 'exact rational numerator/denominator string',
            'values': precise,
            'no_new_rounding': True,
        },
        'discovery_source': {
            'path': CHALLENGE,
            'sha256': EXPECTED[CHALLENGE],
            'field': 'best_gaps',
            'field_type': 'list[float]',
            'values': floats,
            'energy_field': 'best_observed_minimum_upper',
            'saved_F_float_hint': challenge['best_observed_minimum_upper'],
            'this_is_not_an_actual_interval_upper_bound': True,
        },
        'current_ledger_sha256_matches': True,
        'all_24_coefficients_match_current_parameters': True,
        'all_9_existing_rationals_equal_saved_binary_floats': True,
        'saved_pool_row_identity': 69,
        'proof_scope': 'Identity and existing metadata only; no actual scalar upper enclosure or pressure/Phi bound is established.',
        'actions': {'new_pressure_evaluations': 0, 'new_kernel_evaluations': 0,
                    'new_Phi_evaluations': 0, 'new_points': 0,
                    'new_point_roundings': 0, 'solver_calls': 0,
                    'Lean_runs': 0, 'producer_imports': 0},
        'new_global_floor_proven': False,
        'new_unconditional_zero_proportion_proven': False,
    }
    if args.write_receipt:
        RECEIPT.write_text(json.dumps(out, ensure_ascii=False, indent=2,
                                     allow_nan=False) + '\n', encoding='utf-8')
    print(json.dumps({'passed': True, 'fixed_point_path': SUPPORT,
                      'fixed_point_field': out['fixed_point']['field'],
                      'receipt_sha256': sha256(RECEIPT.read_bytes()).hexdigest()
                      if args.write_receipt else None}))


if __name__ == '__main__':
    main()
