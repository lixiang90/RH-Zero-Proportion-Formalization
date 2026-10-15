"""Freeze a revised W10 candidate after all ternary local basins were sampled."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,math
HERE=Path(__file__).resolve().parent
source=HERE/'spectral-wcert-reopt-full-ternary.json';rec=json.loads(source.read_text())['results'][0]
D=10**10;A=[[i,j,math.floor(v*D)] for i,j,v in rec['a']];b=[math.ceil(v*D) for v in rec['b']]
B=Q(sum(b),D);c=Q(433,50000);H=Q(6721684105641188747759983512104999330646,10**40)
caps=[sum(v for i,j,v in A if j-i==s) for s in range(1,10)];assert max(caps)<=2*D
kappa=(H-B)/(1-c)
record={'scope':'Revised exact admissible W10 parameters; analytic floor remains UNPROVED',
    'revision':'all19683 ternary basins plus per-coordinate forced-three-gap DP',
    'source':source.name,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
    'denominator':D,'a_upper':A,'b_numerators':b,'span_capacity_numerators':caps,
    'B_exact':str(B),'proposed_floor_exact':str(c),'proposed_floor_status':'UNPROVED',
    'conditional_kappa_exact':str(kappa),'conditional_percent':100*float(kappa),
    'observed_continuous_minimum_before_rounding':rec['history'][-1]['adversarial_c'],
    'margin_before_rounding':rec['history'][-1]['adversarial_c']-float(c),
    'gap_lower_exact':'4/5 (covers17/20 required separation)',
    'coercive_upper_exact':[str(c/Q(v,D)) for v in b],
    'supersedes_refuted_parameters':'spectral-w10-rational.json (the old record remains explicitly REFUTED)'}
(HERE/'spectral-w10-refined-rational.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ['B_exact','proposed_floor_status','conditional_percent','margin_before_rounding']},indent=2))
