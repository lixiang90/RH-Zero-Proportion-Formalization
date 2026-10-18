"""Exact Fraction target update. No kernel/leaf/optimizer/Lean evaluation.

Existing conditional candidates stay conditional. The fixed old linear dual
is reused, without a new optimization or a stronger-family impossibility claim.
"""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
from decimal import Decimal, localcontext
import argparse
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OUT = HERE / 'target-arithmetic.json'
NEW_R = F(3337839448633819172184136761695440236797,
          4955319193847235264050000000000000000000)
DELTA = F(1, 1000000)
NEW_SOURCE = 'research-goal-20261018-record-source-audit/snapshot/Solution.lean'
GLUE = 'research-goal-20261017-ninepoint-decomposition/coefficient-gluing.json'
P24 = 'research-20261016-followup/window_reweight_rational.json'
P10 = 'research-20261016/spectral-w10-refined-rational.json'
OLD_CONDITIONAL = 'StructuralW10Cert20261016/FinalConditional.lean'
CAP = 'research-goal-20261017-pressure-budget/family-cap.json'
INPUTS = {
    NEW_SOURCE: 'f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf',
    GLUE: 'e39f511b50d8e45ecf9f058f3f717d050c2cd1c316e2d7c846031b833bbfc25b',
    P24: '61ad18366b0234d75c4204bc661446c94f1705c29c3e6041bed0147dd6476f11',
    P10: 'ad117819d63588c55d89bd59ae7f0ad11072faaf33ffc53bf08d7eef54010e03',
    OLD_CONDITIONAL: '6712abb9e41eec3beb0b9d1027341356b0b95259e5678a7b9f4d67c193cb2ceb',
    CAP: '68fbb5b1e77744be6d8a10f4bdf66bbf47bbb311e33d3e33839fd9db5e7b5f75',
}


def display(x):
    x = F(x)
    with localcontext() as ctx:
        ctx.prec = 45
        dec = str(Decimal(x.numerator) / Decimal(x.denominator))
    return {'exact': str(x), 'decimal_display_only': dec}


def load_inputs():
    data = {}
    for name, h in INPUTS.items():
        raw = (ROOT / name).read_bytes()
        assert sha256(raw).hexdigest() == h, name
        data[name] = raw
    return data


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write-receipt', action='store_true')
    args = ap.parse_args()
    if args.write_receipt:
        assert not OUT.exists(), 'refuse to overwrite'
    self_start = sha256(Path(__file__).read_bytes()).hexdigest()
    raw = load_inputs()
    glue, p24, p10, cap = [json.loads(raw[n]) for n in [GLUE, P24, P10, CAP]]
    src = raw[NEW_SOURCE].decode('utf-8').splitlines()
    # Line identities, not execution of the downloaded Lean source.
    assert 'cN : ℕ := 893616123055294719' in src[10633]
    assert '893616123055294719 : ℝ' in src[14583]
    assert '6721290091768038344368273523390880473594 / ' in src[16886]
    assert '456111945004000000 : ℝ' in src[16886]
    assert str(NEW_R.numerator) in src[16887]
    assert str(NEW_R.denominator) in src[16887]
    old_src = raw[OLD_CONDITIONAL].decode('utf-8')
    assert '6721684105641188747759983512104999330646 / 10 ^ 40' in old_src

    old_R = F(glue['record'])
    old_K = F(glue['required_strict_target'])
    assert old_K == old_R + F(1, 100000)
    K = NEW_R + DELTA
    assert old_R < NEW_R < K < old_K
    H_old = F(glue['window_floor'])
    assert H_old == F(6721684105641188747759983512104999330646, 10**40)
    H24, B24 = F(p24['window_H_lower']), F(p24['B_exact'])
    B10 = F(p10['B_exact'])
    B9 = F(glue['ordered_deletion_embeddings'][0]['total_pressure'])
    assert B9 == F(glue['ordered_deletion_embeddings'][9]['total_pressure']) == F(54711, 12500000)

    specifications = [
        ('actual24_c880', H24, B24, F(11, 1250), P24,
         'Unproved whole-domain actual24 floor; complete formal/counting/submission gates remain.'),
        ('actual24_c884', H24, B24, F(221, 25000), P24,
         'Unproved whole-domain actual24 floor;69 local basins do not remove global premise.'),
        ('oldW10_c866', H_old, B10, F(433, 50000), P10,
         'OldW10 full numerical cover is not a completed Lean/global submission proof.'),
        ('old9_prefix_suffix_average_c8611', H_old, B9, F(8611, 1000000), GLUE,
         'Unproved joint separated floor; complete arbitrary-sublevel exception/overlap certificate absent.'),
    ]
    candidates = []
    for name, H, B, c, source, scope in specifications:
        assert 0 < c < F(1, 64) and H > B
        ratio = (H-B)/(1-c)
        assert ratio > K
        candidates.append({'name': name, 'H': str(H), 'B': str(B), 'c': str(c),
                           'ratio': display(ratio), 'percent': display(100*ratio),
                           'ratio_minus_new_target': display(ratio-K),
                           'passes_new_amplitude_arithmetic_only': True,
                           'status': 'CONDITIONAL', 'unproved_premise_scope': scope,
                           'source': source})
    assert F(p24['conditional_kappa_exact']) == F(candidates[1]['ratio']['exact'])
    assert F(p10['conditional_kappa_exact']) == F(candidates[2]['ratio']['exact'])

    c9_new = F(893616123055294719, 10**20)
    H_new = F(6721290091768038344368273523390880473594, 10**40)
    B_new = F(456111945004000000, 10**20)
    assert (H_new-B_new)/(1-c9_new) == NEW_R
    dc = (1-c9_new)*DELTA/K
    c_required = c9_new+dc
    assert c_required == 1-(H_new-B_new)/K
    assert (H_new-B_new)/(1-c_required) == K
    tau_required = 2*c_required-c9_new
    assert dc > 0 and c_required < F(1,64)

    # Same exact old dual; no new solver, repair or multipliers.
    y = list(map(F, glue['exact_dual_nonnegative_weights']))
    assert len(y) == 9 and all(t >= 0 for t in y)
    c9_old = F(glue['old_proved_floor'])
    embeddings = glue['ordered_deletion_embeddings']
    assert len(embeddings) == 10
    old_gains = list(map(F, glue['exact_linearized_column_gains']))
    covers = list(map(F, glue['exact_dual_covered_column_gains']))
    new_gains, updated_covers = [], []
    for j, e in enumerate(embeddings):
        a = list(map(F, e['span_masses']))
        b = F(e['total_pressure'])
        assert len(a) == 9 and all(v >= 0 for v in a)
        covered = sum((yi*ai for yi, ai in zip(y,a)), F(0))
        assert covered == covers[j] >= old_gains[j] == old_K*c9_old-b
        gain = K*c9_old-b
        assert covered >= gain and gain < old_gains[j]
        new_gains.append(str(gain)); updated_covers.append(str(covered))
    U = 2*sum(y, F(0))
    assert U == F(glue['exact_dual_upper'])
    strict_gap = K-H_old-U
    assert strict_gap > 0
    total_mass = F(glue['old_exact_total_pair_mass'])
    assert c9_old*F(18)/total_mass < F(1,64)

    M = F(cap['uniform_floor_cap_M'])
    ratio_cap = (H24-B24)/(1-M)
    assert M < 1 and ratio_cap == F(cap['fixed_H_B_ratio_upper']) < NEW_R < K
    assert load_inputs() == raw
    self_end = sha256(Path(__file__).read_bytes()).hexdigest()
    assert self_start == self_end
    out = {
        'schema': 'new-record-target-exact-arithmetic-v1',
        'date': '2026-10-18', 'passed': True, 'scope': __doc__,
        'record_provenance': {'website': 'https://www.riemannzeta.fun/',
                              'R_supplied_by_root_after_website_check': str(NEW_R),
                              'source_snapshot': NEW_SOURCE,
                              'source_lines': {'cN':10634,'cert_AM':14584,'ratio_H_B_identity':[16887,16888]},
                              'this_script_did_not_browse_or_compile': True},
        'source_sha256_start': INPUTS, 'source_sha256_end': INPUTS,
        'script_sha256_start': self_start, 'script_sha256_end': self_end,
        'target': {'new_R':display(NEW_R), 'new_R_percent':display(100*NEW_R),
                   'required_absolute_increment':str(DELTA), 'new_K':display(K),
                   'new_K_percent':display(100*K),
                   'strict_success_requires_ratio_greater_than_K':True,
                   'old_R_from_frozen_site_comparison':display(old_R),
                   'new_R_minus_old_R':display(NEW_R-old_R),
                   'old_K_Rold_plus_1e5_inverse':display(old_K),
                   'new_K_minus_old_K':display(K-old_K)},
        'conditional_candidates': candidates,
        'new_record_fixed_H_B_floor_arithmetic': {
            'H':str(H_new),'B':str(B_new),'current_c9':str(c9_new),
            'source_exact_ratio_identity_recomputed':True,
            'delta_c_formula':'(1-c9)*(1/1000000)/(new_R+1/1000000)',
            'delta_c':display(dc), 'c_required_for_equality_to_K':display(c_required),
            'strict_success_requires_c_greater_than_c_required':True,
            'two_window_exception_tau_at_required_equality':display(tau_required),
            'tau_formula':'2*c_required-c9',
            'thresholds_are_arithmetic_only_not_new_experiment_authorization':True,
            'new_floor_proven':False},
        'old_linear_gluing_fixed_dual_update': {
            'same_old_y_nonnegative':True,'same_y':list(map(str,y)),
            'all10_new_column_gains_covered':True,'new_column_gains':new_gains,
            'unchanged_column_covers':updated_covers,'same_exact_upper_U':str(U),
            'new_K_minus_Hold_minus_U':display(strict_gap),
            'cannot_reach_new_K_with_fixed_H_direct_c9_sum_lambda_rule':True,
            'stronger_actual_joint_floor_for_same_glued_ledger_not_ruled_out':True,
            'new_optimizer_calls':0,
            'old_presolver_failed_execution_and_one_successful_solver_call_not_rewritten':True},
        'old_actual24_uniform_affine_pressure_family_cap_update': {
            'old_floor_cap':display(M),'old_H_B_ratio_cap':display(ratio_cap),
            'strictly_below_new_R':True,'new_R_minus_ratio_cap':display(NEW_R-ratio_cap),
            'scope':'Only frozen old actual24 kernel/current24 ledger and the old whole-domain uniform scalar affine-pressure interface. Does not migrate to new record kernel or refute actual floor.'},
        'new_global_floor_proven':False,'new_unconditional_zero_proportion_proven':False,
        'website_submission_ready':False,
        'actions':{'Fraction_arithmetic_only':True,'new_kernel_evaluations':0,
                   'leaf_scans':0,'solver_calls':0,'Lean_runs':0,'old_packets_modified':False},
    }
    if args.write_receipt:
        OUT.write_text(json.dumps(out,ensure_ascii=False,indent=2,allow_nan=False)+'\n',encoding='utf-8')
    print(json.dumps({'passed':True,'new_R_percent':out['target']['new_R_percent']['decimal_display_only'],
                      'new_K_percent':out['target']['new_K_percent']['decimal_display_only'],
                      'candidate_percent_hints':[{ 'name':c['name'],'percent':c['percent']['decimal_display_only'],
                                                 'margin':c['ratio_minus_new_target']['decimal_display_only']} for c in candidates],
                      'new_c_required':str(c_required),'new_c_required_hint':display(c_required)['decimal_display_only'],
                      'new_tau_hint':display(tau_required)['decimal_display_only'],
                      'old_dual_strict_gap':display(strict_gap)['decimal_display_only'],
                      'receipt_sha256':sha256(OUT.read_bytes()).hexdigest() if args.write_receipt else None}))


if __name__ == '__main__':
    main()
