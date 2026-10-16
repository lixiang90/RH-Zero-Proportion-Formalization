"""Round a new-window ledger in the admissible direction; c remains unproved."""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json,math
HERE=Path(__file__).resolve().parent
source=HERE/'window_reweight_search.json';data=json.loads(source.read_text());r=data['history'][-1]
D=10**10;a=[[i,j,math.floor(v*D)] for i,j,v in r['pair_weights']];b=[math.ceil(v*D) for v in r['pressure']]
caps=[sum(v for i,j,v in a if j-i==s) for s in range(1,10)]
assert min(b)>0 and max(caps)<=2*D
terms={(i,j):v for i,j,v in a};assert all(terms[i,j]==terms[9-j,9-i] for i,j,v in a)
assert b==b[::-1]
rec=json.loads((HERE/'window_exact_parameters.json').read_text())['windows'][1]
h=F(rec['rounded_H_lower']);B=F(sum(b),D);c=F(221,25000)
kap=(h-B)/(1-c)
record={'status':'ADMISSIBLE_RATIONAL_LEDGER_UNPROVED_GLOBAL_FLOOR',
    'source':source.name,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
    'window_coefficient_numerators_1e9':data['window_coefficient_numerators_1e9'],
    'denominator':D,'a_upper':a,'b_numerators':b,'span_capacity_numerators':caps,
    'B_exact':str(B),'window_H_lower':str(h),'proposed_floor_exact':str(c),
    'separation_lower_exact':'123/128','conditional_kappa_exact':str(kap),
    'conditional_percent':100*float(kap),'local_floor_proven':False,
    'all_exact_admissibility_checks_passed':True,'website_upload_ready':False}
(HERE/'window_reweight_rational.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf8')
print(json.dumps({k:record[k] for k in ['B_exact','proposed_floor_exact','conditional_kappa_exact','conditional_percent']},indent=2))
