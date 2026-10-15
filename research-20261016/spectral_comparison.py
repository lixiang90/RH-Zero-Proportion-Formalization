"""Summarize research outcomes; all new numerical floors remain conjectural."""
from pathlib import Path
from fractions import Fraction as Q
import json,math
HERE=Path(__file__).resolve().parent
doc=json.loads((HERE/'spectral-wcert-reopt.json').read_text())
floors={10:Q(433,50000),11:Q(1829,200000),12:Q(6,625)}
D=10**10;rows=[]
for rec in doc['results']:
    n=rec['n'];last=rec['history'][-1];a=[[i,j,math.floor(v*D)] for i,j,v in rec['a']]
    b=[math.ceil(v*D) for v in rec['b']];B=Q(sum(b),D);c=floors[n]
    H=Q(6721684105641188747759983512104999330646,10**40)
    kappa=(H-B)/(1-c)
    assert max(sum(v for i,j,v in a if j-i==d) for d in range(1,n))<=2*D
    row={'n':n,'rounded_B_exact':str(B),'rounded_B_decimal':float(B),
        'sample_LP_c':last['sample_c'],'numerical_worst_c_upper_bound':last['adversarial_c'],
        'sample_LP_optimum_percent_upper_bound':100*last['sample_kappa'],
        'numerical_candidate_percent_upper_bound':100*last['observed_kappa'],
        'proposed_rational_floor_exact':str(c),'proposed_floor_decimal':float(c),
        'margin_observed_before_rounding':last['adversarial_c']-float(c),
        'conditional_proportion_exact':str(kappa),'conditional_percent':100*float(kappa),
        'new_rank_distances':list(range(9,n)),
        'rounded_a_upper_numerators':a,'rounded_b_numerators':b,'denominator':D,
        'status':'Full analytic floor is unproved. Numeric adversaries give upper bounds on minima, not lower bounds.',
        'search_domain_lower':'4/5; covers actual remainder separation17/20',
        'adversaries':'all binary grid; ternary memory9 DP; quaternary memory7 DP; sparse large gaps; continuous polish',
        'remaining_sample_discrepancy':last['violation']}
    if n==10 and (HERE/'spectral-w10-challenge.json').exists():
        challenge=json.loads((HERE/'spectral-w10-challenge.json').read_text())
        row['status']='REFUTED: proposed floor.00866 fails at a continuous central-three-gap example'
        row['numerical_worst_c_upper_bound']=challenge['best_observed_minimum']
        lower=Q(27,3125);row['alternative_unproved_floor_exact']=str(lower)
        row['alternative_unproved_floor_conditional_percent']=100*float((H-B)/(1-lower))
    rows.append(row)
report={'current_proved_percent':100*doc['current_kappa'],'scope':'Research comparison, no new zeta record asserted',
    'rows':rows,
    'uniform_spectral_frames':{'24_point_strong_adversary_percent':67.35398612990656,
        '32_point_strong_adversary_percent':67.35503431838851,
        'interpretation':'The two tested uniform spectral-frame candidates are below the current record and rejected.'},
    'higher_moment_limitation':'For separated normalized Gram spectra in[0,2], Psi is quadratic and trPsi equals the offdiagonal squared energy; no free higher-moment improvement follows.'}
if (HERE/'spectral-w10-refined-rational.json').exists():
    report['revised_W10']=json.loads((HERE/'spectral-w10-refined-rational.json').read_text())
    report['revised_W10']['strong_challenge']=json.loads((HERE/'spectral-w10-refined-challenge.json').read_text())
(HERE/'spectral-comparison.json').write_text(json.dumps(report,indent=2)+'\n')
lines=['Larger-frame research comparison (not a new proved proportion)',
       f'Current proved percentage: {report["current_proved_percent"]:.12f}',
       'All numerical searches use gaps >=4/5, covering the required17/20 separation.',
       'Numerical minima and sampled-LP optima below are upper bounds; proposed analytic floors remain unproved.',
       'WARNING: The ORIGINAL W10 weight set floor.00866 is REFUTED; the REVISED W10 weights below are different.',
       '',
       'n  B exact                    sampled c       observed c      proposed c  conditional %']
for r in rows:
    flag=' REFUTED' if r['n']==10 else ' UNPROVED'
    lines.append(f'{r["n"]:<2} {r["rounded_B_exact"]:<26} {r["sample_LP_c"]:.12f} {r["numerical_worst_c_upper_bound"]:.12f} {r["proposed_floor_decimal"]:.8f}  {r["conditional_percent"]:.10f}{flag}')
if 'revised_W10' in report:
    r=report['revised_W10']
    lines += ['', 'Revised W10 after the counterexample and all19683 ternary starting points:',
        f'B={r["B_exact"]}; proposed c={r["proposed_floor_exact"]}; conditional percentage={r["conditional_percent"]:.10f} UNPROVED.',
        f'Independent strong challenge minimum={r["strong_challenge"]["best_observed_minimum"]:.14f}; no global certificate yet.']
lines += ['', 'All a are rounded down and b up at denominator10^10; exact span capacities are<=2.',
          'The10-point candidate adds rank-distance9 energy with coefficient2.',
          'The11/12-point candidates also add distances10/11; local dimension becomes10/11.',
          'For the ORIGINAL10-point weights, floor433/50000 is REFUTED. The lower candidate27/3125=.00864 would imply67.3587030911%, but remains unproved.',
          '', 'Proof route and size:',
          'The generic WCert(n) counting bridge already covers arbitrary n; positive b reduces the unbounded gap domain to a finite coercive box.',
          'A full Cartesian sinc interval proof in9 dimensions is unattractive: the rank9 pair depends on all9 gaps, so its bound loses all gain until the total span is constrained.',
          'Use polyhedral branches with gap and partial-span constraints, tangent/epigraph lower bounds on each positive a*K^2, and exact rational LP duals; existing9-point scripts provide this style.',
          'Full reoptimization sets some old positive edge weights to0, so the old W9 finite certificate cannot simply be added as a nonnegative subcertificate.',
          'No node-count prediction is certified; the actual adaptive certificate must be generated and replayed before a proportion is claimed.',
          '', 'Uniform24/32-point spectral candidates failed stronger sparse/ternary adversaries.',
          'The Fenchel trace bridge is useful formal infrastructure, but by itself supplies no new numeric proportion.', '']
(HERE/'spectral-comparison.txt').write_text('\n'.join(lines),encoding='utf8')
print('\n'.join(lines[:12]))
